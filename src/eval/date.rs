// Licensed to Julian Hyde under one or more contributor license
// agreements.  See the NOTICE file distributed with this work
// for additional information regarding copyright ownership.
// Julian Hyde licenses this file to you under the Apache
// License, Version 2.0 (the "License"); you may not use this
// file except in compliance with the License.  You may obtain a
// copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.  See the License for the specific
// language governing permissions and limitations under the
// License.

//! Implementation of the `Date` structure of the SML Basis Library.
//!
//! Date values are stored as `(utc_nanos, offset_secs)` — an instant
//! (nanoseconds since the Unix epoch) plus a local timezone offset in
//! seconds east of UTC. Field accessors like `Date.year` use the
//! local broken-down time (`utc_nanos + offset_secs * 1e9`).

use crate::compile::library::BuiltInExn;
use crate::compile::span::Span;
use crate::eval::order::Order;
use crate::eval::session::Session;
use crate::eval::val::{
    MONTH_APR_ORDINAL, MONTH_AUG_ORDINAL, MONTH_DEC_ORDINAL, MONTH_FEB_ORDINAL,
    MONTH_JAN_ORDINAL, MONTH_JUL_ORDINAL, MONTH_JUN_ORDINAL, MONTH_MAR_ORDINAL,
    MONTH_MAY_ORDINAL, MONTH_NOV_ORDINAL, MONTH_OCT_ORDINAL, MONTH_SEP_ORDINAL,
    Val, WEEKDAY_FRI_ORDINAL, WEEKDAY_MON_ORDINAL, WEEKDAY_SAT_ORDINAL,
    WEEKDAY_SUN_ORDINAL, WEEKDAY_THU_ORDINAL, WEEKDAY_TUE_ORDINAL,
    WEEKDAY_WED_ORDINAL,
};
use crate::shell::main::MorelError;
use crate::shell::prop::{Prop, PropVal};
use chrono::{DateTime, NaiveDate, TimeZone, Utc};
use chrono_tz::Tz;
use std::fmt::Write;
use std::time::{SystemTime, UNIX_EPOCH};

const NS_PER_SEC: i64 = 1_000_000_000;
const SECS_PER_DAY: i64 = 86_400;
const SECS_PER_HOUR: i64 = 3_600;
const SECS_PER_MIN: i64 = 60;

/// Decomposed broken-down date.
#[derive(Copy, Clone)]
struct Broken {
    year: i32,
    month: u32, // 1..12
    day: u32,   // 1..31
    hour: u32,
    minute: u32,
    second: u32,
    weekday: u32, // 0=Mon..6=Sun
    yearday: u32, // 0..365
}

fn weekday_ordinal(w: u32) -> usize {
    match w {
        0 => WEEKDAY_MON_ORDINAL,
        1 => WEEKDAY_TUE_ORDINAL,
        2 => WEEKDAY_WED_ORDINAL,
        3 => WEEKDAY_THU_ORDINAL,
        4 => WEEKDAY_FRI_ORDINAL,
        5 => WEEKDAY_SAT_ORDINAL,
        6 => WEEKDAY_SUN_ORDINAL,
        _ => panic!("invalid weekday: {}", w),
    }
}

fn month_ordinal(m: u32) -> usize {
    match m {
        1 => MONTH_JAN_ORDINAL,
        2 => MONTH_FEB_ORDINAL,
        3 => MONTH_MAR_ORDINAL,
        4 => MONTH_APR_ORDINAL,
        5 => MONTH_MAY_ORDINAL,
        6 => MONTH_JUN_ORDINAL,
        7 => MONTH_JUL_ORDINAL,
        8 => MONTH_AUG_ORDINAL,
        9 => MONTH_SEP_ORDINAL,
        10 => MONTH_OCT_ORDINAL,
        11 => MONTH_NOV_ORDINAL,
        12 => MONTH_DEC_ORDINAL,
        _ => panic!("invalid month: {}", m),
    }
}

/// Returns the 1-based month (1..12) for the given month constructor
/// ordinal.
pub(crate) fn ordinal_to_month(o: usize) -> u32 {
    match o {
        x if x == MONTH_JAN_ORDINAL => 1,
        x if x == MONTH_FEB_ORDINAL => 2,
        x if x == MONTH_MAR_ORDINAL => 3,
        x if x == MONTH_APR_ORDINAL => 4,
        x if x == MONTH_MAY_ORDINAL => 5,
        x if x == MONTH_JUN_ORDINAL => 6,
        x if x == MONTH_JUL_ORDINAL => 7,
        x if x == MONTH_AUG_ORDINAL => 8,
        x if x == MONTH_SEP_ORDINAL => 9,
        x if x == MONTH_OCT_ORDINAL => 10,
        x if x == MONTH_NOV_ORDINAL => 11,
        x if x == MONTH_DEC_ORDINAL => 12,
        _ => panic!("not a month ordinal: {}", o),
    }
}

/// Wraps a date constructor as a `Val::Constructor` with `Val::Unit`
/// payload.
fn ctor(o: usize) -> Val {
    Val::Constructor(o, Box::new(Val::Unit))
}

fn weekday_val(w: u32) -> Val {
    ctor(weekday_ordinal(w))
}

fn month_val(m: u32) -> Val {
    ctor(month_ordinal(m))
}

const MONTH_NAMES_SHORT: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct",
    "Nov", "Dec",
];
const MONTH_NAMES_FULL: [&str; 12] = [
    "January",
    "February",
    "March",
    "April",
    "May",
    "June",
    "July",
    "August",
    "September",
    "October",
    "November",
    "December",
];
const WEEKDAY_NAMES_SHORT: [&str; 7] =
    ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
const WEEKDAY_NAMES_FULL: [&str; 7] = [
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
    "Sunday",
];

/// Howard Hinnant's `civil_from_days`: converts a count of days since
/// 1970-01-01 into a (year, month, day) triple.
fn civil_from_days(days: i64) -> (i32, u32, u32) {
    let z = days + 719468;
    let era = if z >= 0 {
        z / 146097
    } else {
        (z - 146096) / 146097
    };
    let doe = (z - era * 146097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    let y = if m <= 2 { y + 1 } else { y };
    (y as i32, m, d)
}

/// Howard Hinnant's `days_from_civil`: converts a (year, month, day)
/// triple into days since 1970-01-01.
fn days_from_civil(y: i32, m: u32, d: u32) -> i64 {
    let y = if m <= 2 { y as i64 - 1 } else { y as i64 };
    let era = if y >= 0 { y / 400 } else { (y - 399) / 400 };
    let yoe = y - era * 400;
    let m = m as i64;
    let d = d as i64;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

fn is_leap(y: i32) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}

const DAYS_IN_MONTH: [u32; 12] =
    [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

fn days_in_month(y: i32, m: u32) -> u32 {
    if m == 2 && is_leap(y) {
        29
    } else {
        DAYS_IN_MONTH[(m - 1) as usize]
    }
}

/// Day of year (0..365) for the given civil date.
fn day_of_year(y: i32, m: u32, d: u32) -> u32 {
    let mut total: u32 = 0;
    for i in 1..m {
        total += days_in_month(y, i);
    }
    total + d - 1
}

/// Decomposes UTC nanoseconds plus an offset into broken-down local
/// fields.
fn break_down(utc_nanos: i64, offset_secs: i32) -> Broken {
    let local_nanos =
        utc_nanos.wrapping_add((offset_secs as i64).wrapping_mul(NS_PER_SEC));
    let secs = local_nanos.div_euclid(NS_PER_SEC);
    let days = secs.div_euclid(SECS_PER_DAY);
    let day_secs = secs.rem_euclid(SECS_PER_DAY);
    let hour = (day_secs / SECS_PER_HOUR) as u32;
    let minute = ((day_secs % SECS_PER_HOUR) / SECS_PER_MIN) as u32;
    let second = (day_secs % SECS_PER_MIN) as u32;
    // Compute weekday: 1970-01-01 was a Thursday (weekday = 3 with Mon=0).
    let weekday = ((days.rem_euclid(7) + 3).rem_euclid(7)) as u32;
    let (y, m, d) = civil_from_days(days);
    let yearday = day_of_year(y, m, d);
    Broken {
        year: y,
        month: m,
        day: d,
        hour,
        minute,
        second,
        weekday,
        yearday,
    }
}

/// Formats an offset (seconds east of UTC) as an ISO-8601 suffix:
/// `Z` for zero, otherwise `+HH:MM` or `-HH:MM`.
fn format_offset(offset_secs: i32) -> String {
    if offset_secs == 0 {
        "Z".to_string()
    } else {
        let sign = if offset_secs < 0 { '-' } else { '+' };
        let abs = offset_secs.unsigned_abs();
        let h = abs / 3600;
        let m = (abs % 3600) / 60;
        format!("{}{:02}:{:02}", sign, h, m)
    }
}

/// Formats a date value as ISO-8601 (e.g. `1970-01-01T00:00Z` or
/// `1969-12-31T19:00-05:00`).
pub(crate) fn format_iso(utc_nanos: i64, offset_secs: i32) -> String {
    let b = break_down(utc_nanos, offset_secs);
    let suffix = format_offset(offset_secs);
    if b.second == 0 {
        format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}{}",
            b.year, b.month, b.day, b.hour, b.minute, suffix
        )
    } else {
        format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}{}",
            b.year, b.month, b.day, b.hour, b.minute, b.second, suffix
        )
    }
}

/// Reads the `timeZone` property as a `chrono_tz::Tz`. Defaults to UTC
/// when unset or unparseable.
fn session_tz(session: &Session) -> Tz {
    if let Some(PropVal::String(s)) =
        session.config.get_optional(Prop::TimeZone)
        && let Ok(tz) = s.parse::<Tz>()
    {
        return tz;
    }
    Tz::UTC
}

/// Returns the offset (seconds east of UTC) for the given UTC instant
/// in the given timezone.
fn tz_offset_at(tz: Tz, utc_nanos: i64) -> i32 {
    use chrono::offset::Offset;
    let secs = utc_nanos.div_euclid(NS_PER_SEC);
    let nsec = utc_nanos.rem_euclid(NS_PER_SEC) as u32;
    let dt: DateTime<Utc> = Utc
        .timestamp_opt(secs, nsec)
        .single()
        .unwrap_or_else(|| DateTime::<Utc>::from_timestamp(0, 0).unwrap());
    let local = dt.with_timezone(&tz);
    local.offset().fix().local_minus_utc()
}

/// `Date.fromTimeUniv t`: converts a time to a UTC date.
pub(crate) fn from_time_univ(t: i64) -> Val {
    Val::Date(t, 0)
}

/// `Date.fromTimeLocal t`: converts a time to a local date in the
/// timezone given by the `timeZone` property.
pub(crate) fn from_time_local(t: i64, session: &Session) -> Val {
    let tz = session_tz(session);
    Val::Date(t, tz_offset_at(tz, t))
}

/// `Date.toTime d`: converts a date to a time (the underlying UTC
/// instant).
pub(crate) fn to_time(utc_nanos: i64, _offset_secs: i32) -> Val {
    Val::Time(utc_nanos)
}

/// `Date.localOffset ()`: returns the local timezone offset (UTC -
/// local) as a positive duration. Per the SML basis spec, this is the
/// offset to *add* to a UTC time to obtain local time, expressed as a
/// non-negative magnitude. For zones west of UTC it is the absolute
/// value of the offset.
pub(crate) fn local_offset(session: &Session) -> Val {
    let tz = session_tz(session);
    let now_secs = match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(d) => d.as_secs() as i64,
        Err(_) => 0,
    };
    let offset = tz_offset_at(tz, now_secs * NS_PER_SEC);
    // SML: offset is non-negative, meaning "magnitude west of UTC" for
    // western zones and 0 for UTC. We follow morel-java which returns
    // the absolute value.
    Val::Time((offset.unsigned_abs() as i64) * NS_PER_SEC)
}

/// `Date.year d`.
pub(crate) fn year(utc_nanos: i64, offset_secs: i32) -> Val {
    Val::Int(break_down(utc_nanos, offset_secs).year)
}

/// `Date.month d`.
pub(crate) fn month(utc_nanos: i64, offset_secs: i32) -> Val {
    month_val(break_down(utc_nanos, offset_secs).month)
}

/// `Date.day d`.
pub(crate) fn day(utc_nanos: i64, offset_secs: i32) -> Val {
    Val::Int(break_down(utc_nanos, offset_secs).day as i32)
}

/// `Date.hour d`.
pub(crate) fn hour(utc_nanos: i64, offset_secs: i32) -> Val {
    Val::Int(break_down(utc_nanos, offset_secs).hour as i32)
}

/// `Date.minute d`.
pub(crate) fn minute(utc_nanos: i64, offset_secs: i32) -> Val {
    Val::Int(break_down(utc_nanos, offset_secs).minute as i32)
}

/// `Date.second d`.
pub(crate) fn second(utc_nanos: i64, offset_secs: i32) -> Val {
    Val::Int(break_down(utc_nanos, offset_secs).second as i32)
}

/// `Date.weekDay d`.
pub(crate) fn week_day(utc_nanos: i64, offset_secs: i32) -> Val {
    weekday_val(break_down(utc_nanos, offset_secs).weekday)
}

/// `Date.yearDay d`.
pub(crate) fn year_day(utc_nanos: i64, offset_secs: i32) -> Val {
    Val::Int(break_down(utc_nanos, offset_secs).yearday as i32)
}

/// `Date.isDst d`.
pub(crate) fn is_dst(_utc_nanos: i64, _offset_secs: i32) -> Val {
    // NONE — DST information not available.
    Val::Unit
}

/// `Date.compare (d1, d2)`.
pub(crate) fn compare(d1: i64, d2: i64) -> Val {
    Val::Order(Order(d1.cmp(&d2)))
}

/// `Date.date {year, month, day, hour, minute, second, offset}`.
/// Raises `Date` if any field is out of range.
pub(crate) fn make_date(
    args: &[Val],
    span: &Span,
    session: &Session,
) -> Result<Val, MorelError> {
    // Records sort fields alphabetically: day, hour, minute, month, offset,
    // second, year.
    assert_eq!(args.len(), 7);
    let day = args[0].expect_int();
    let hour = args[1].expect_int();
    let minute = args[2].expect_int();
    let month_ord = match &args[3] {
        Val::Constructor(o, _) => *o,
        _ => panic!("expected month constructor"),
    };
    let offset = &args[4]; // time option (Unit = NONE)
    let second = args[5].expect_int();
    let year = args[6].expect_int();

    let m = ordinal_to_month(month_ord);
    if !(1..=days_in_month(year, m) as i32).contains(&day)
        || !(0..24).contains(&hour)
        || !(0..60).contains(&minute)
        || !(0..60).contains(&second)
    {
        return Err(MorelError::Runtime(BuiltInExn::Date, span.clone()));
    }

    let days = days_from_civil(year, m, day as u32);
    let local_secs = days * SECS_PER_DAY
        + hour as i64 * SECS_PER_HOUR
        + minute as i64 * SECS_PER_MIN
        + second as i64;
    let local_nanos = local_secs * NS_PER_SEC;

    // Determine offset. If `offset` field is SOME t, use t directly
    // (interpreted as east-of-UTC magnitude per SML convention).
    // Otherwise use the session's timeZone property.
    let offset_secs: i32 = if let Val::Some(boxed) = offset {
        let off_nanos = boxed.expect_time();
        (off_nanos / NS_PER_SEC) as i32
    } else {
        let tz = session_tz(session);
        // Approximate: get offset at the local-as-utc instant.
        let utc_guess = local_nanos;
        // Use NaiveDate to find offset of the local datetime in tz.
        let naive = NaiveDate::from_ymd_opt(year, m, day as u32)
            .and_then(|d| {
                d.and_hms_opt(hour as u32, minute as u32, second as u32)
            })
            .unwrap_or_default();
        match tz.from_local_datetime(&naive).single() {
            Some(local_dt) => {
                use chrono::offset::Offset;
                local_dt.offset().fix().local_minus_utc()
            }
            None => tz_offset_at(tz, utc_guess),
        }
    };
    let utc_nanos = local_nanos - (offset_secs as i64) * NS_PER_SEC;
    Ok(Val::Date(utc_nanos, offset_secs))
}

/// `Date.toString d`: e.g. `"Wed Dec 31 00:00:00 1969"`.
pub(crate) fn to_string(utc_nanos: i64, offset_secs: i32) -> Val {
    let b = break_down(utc_nanos, offset_secs);
    Val::String(format!(
        "{} {} {:02} {:02}:{:02}:{:02} {:04}",
        WEEKDAY_NAMES_SHORT[b.weekday as usize],
        MONTH_NAMES_SHORT[(b.month - 1) as usize],
        b.day,
        b.hour,
        b.minute,
        b.second,
        b.year
    ))
}

/// `Date.fmt fmt d`: format with strftime-style directives, matching
/// the subset implemented by SML/NJ.
///
/// Supported directives:
/// `%a` `%A` `%b` `%B` `%c` `%d` `%H` `%I` `%j` `%m` `%M` `%p` `%S`
/// `%U` `%w` `%x` `%X` `%y` `%Y` `%%`. An unrecognized `%X` is
/// emitted as the bare letter `X` (the `%` is stripped). A trailing
/// `%` is preserved.
pub(crate) fn fmt(format: &str, utc_nanos: i64, offset_secs: i32) -> Val {
    let b = break_down(utc_nanos, offset_secs);
    Val::String(strftime(format, &b))
}

fn strftime(format: &str, b: &Broken) -> String {
    let mut out = String::new();
    let mut chars = format.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '%' {
            match chars.next() {
                None => out.push('%'),
                Some(d) => emit_directive(&mut out, d, b),
            }
        } else {
            out.push(c);
        }
    }
    out
}

fn emit_directive(out: &mut String, d: char, b: &Broken) {
    // Sunday-based weekday: 0=Sun, 1=Mon, ..., 6=Sat. Internal storage
    // uses Mon=0..Sun=6, so we map.
    let sun_wday = (b.weekday + 1) % 7;
    // 12-hour clock: 0->12, 1..11->1..11, 12->12, 13..23->1..11.
    let hour12 = (b.hour + 11) % 12 + 1;
    let pm = b.hour >= 12;
    match d {
        'a' => out.push_str(WEEKDAY_NAMES_SHORT[b.weekday as usize]),
        'A' => out.push_str(WEEKDAY_NAMES_FULL[b.weekday as usize]),
        'b' | 'h' => {
            // %h is an alias for %b in some locales; SML/NJ does not
            // support %h, but emitting %b here is harmless and slightly
            // more useful.
            out.push_str(MONTH_NAMES_SHORT[(b.month - 1) as usize]);
        }
        'B' => out.push_str(MONTH_NAMES_FULL[(b.month - 1) as usize]),
        'c' => {
            // ctime-style with space-padded day of month.
            let _ = write!(
                out,
                "{} {} {:>2} {:02}:{:02}:{:02} {:04}",
                WEEKDAY_NAMES_SHORT[b.weekday as usize],
                MONTH_NAMES_SHORT[(b.month - 1) as usize],
                b.day,
                b.hour,
                b.minute,
                b.second,
                b.year
            );
        }
        'd' => out.push_str(&format!("{:02}", b.day)),
        'H' => out.push_str(&format!("{:02}", b.hour)),
        'I' => out.push_str(&format!("{:02}", hour12)),
        'j' => out.push_str(&format!("{:03}", b.yearday + 1)),
        'm' => out.push_str(&format!("{:02}", b.month)),
        'M' => out.push_str(&format!("{:02}", b.minute)),
        'p' => out.push_str(if pm { "PM" } else { "AM" }),
        'S' => out.push_str(&format!("{:02}", b.second)),
        'U' => {
            // Week of year, Sunday is first day. Days before the first
            // Sunday are in week 00.
            let week = (b.yearday + 7 - sun_wday) / 7;
            out.push_str(&format!("{:02}", week));
        }
        'w' => out.push_str(&sun_wday.to_string()),
        'x' => {
            let _ = write!(
                out,
                "{:02}/{:02}/{:02}",
                b.month,
                b.day,
                b.year.rem_euclid(100)
            );
        }
        'X' => {
            let _ =
                write!(out, "{:02}:{:02}:{:02}", b.hour, b.minute, b.second);
        }
        'y' => out.push_str(&format!("{:02}", b.year.rem_euclid(100))),
        'Y' => out.push_str(&format!("{:04}", b.year)),
        '%' => out.push('%'),
        // Unrecognized directive: emit the bare letter (% stripped).
        other => out.push(other),
    }
}

/// `Date.fromString s`: parse a date string in `ctime` format
/// (e.g. `"Wed Mar 08 19:06:45 1995"`).
pub(crate) fn from_string(s: &str) -> Val {
    let trimmed = s.trim();
    let parts: Vec<&str> = trimmed.split_ascii_whitespace().collect();
    if parts.len() != 5 {
        return Val::Unit;
    }
    let weekday = parts[0];
    if !WEEKDAY_NAMES_SHORT.contains(&weekday) {
        return Val::Unit;
    }
    let month = match MONTH_NAMES_SHORT.iter().position(|m| *m == parts[1]) {
        Some(i) => (i as u32) + 1,
        None => return Val::Unit,
    };
    let day: u32 = match parts[2].parse() {
        Ok(d) => d,
        _ => return Val::Unit,
    };
    let time_parts: Vec<&str> = parts[3].split(':').collect();
    if time_parts.len() != 3 {
        return Val::Unit;
    }
    let hour: u32 = match time_parts[0].parse() {
        Ok(h) => h,
        _ => return Val::Unit,
    };
    let minute: u32 = match time_parts[1].parse() {
        Ok(m) => m,
        _ => return Val::Unit,
    };
    let second: u32 = match time_parts[2].parse() {
        Ok(s) => s,
        _ => return Val::Unit,
    };
    let year: i32 = match parts[4].parse() {
        Ok(y) => y,
        _ => return Val::Unit,
    };
    if !(1..=days_in_month(year, month)).contains(&day)
        || hour >= 24
        || minute >= 60
        || second >= 60
    {
        return Val::Unit;
    }
    let days = days_from_civil(year, month, day);
    let secs = days * SECS_PER_DAY
        + hour as i64 * SECS_PER_HOUR
        + minute as i64 * SECS_PER_MIN
        + second as i64;
    Val::Some(Box::new(Val::Date(secs * NS_PER_SEC, 0)))
}
