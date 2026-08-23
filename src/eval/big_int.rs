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

//! An integer of arbitrary size.
//!
//! Standard ML's `IntInf.int` is unbounded, and so are the quantities
//! that count a type's values: a nine-character word has 256^9 of them,
//! which no machine integer holds. This is the smallest arithmetic that
//! serves — construction, negation, comparison, addition and
//! multiplication — not a general bignum library.
//!
//! A value is a sign and a magnitude, the magnitude being base-2^32
//! digits with the least significant first. Zero is the empty
//! magnitude, and is not negative, so a value has one representation
//! and `Eq` and `Ord` may be derived from it — after normalizing, which
//! every operation here does.
//!
//! `Display` writes a negative with `-`, as Rust's own integers do,
//! not with Standard ML's `~`. Writing `~` is the value printer's job,
//! as it already is for `int`; this type is not a Morel value. But
//! `parse` reads either, since a numeral typed by a user may be in
//! Morel's notation.

// Nothing uses this type yet; the commit that makes `rangeMaxLength`
// an `IntInf.int` is its first caller, and removes this.
#![allow(dead_code)]

use std::cmp::Ordering;
use std::fmt::{Display, Formatter, Result as FmtResult};

/// An integer of arbitrary size. See the [module docs](self).
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct BigInt {
    /// Whether the value is less than zero. Zero is not negative.
    negative: bool,
    /// Base-2^32 digits, least significant first, with no leading
    /// zeros (so zero is empty).
    mag: Vec<u32>,
}

impl BigInt {
    /// The value zero.
    pub fn zero() -> Self {
        BigInt {
            negative: false,
            mag: Vec::new(),
        }
    }

    /// Whether this is zero.
    pub fn is_zero(&self) -> bool {
        self.mag.is_empty()
    }

    /// Whether this is less than zero.
    // Part of the arithmetic this type offers, though no caller needs
    // it yet.
    #[allow(dead_code)]
    pub fn is_negative(&self) -> bool {
        self.negative
    }

    /// The value of `n`.
    pub fn from_u128(n: u128) -> Self {
        let mut mag = Vec::with_capacity(4);
        let mut n = n;
        while n != 0 {
            mag.push((n & 0xFFFF_FFFF) as u32);
            n >>= 32;
        }
        BigInt {
            negative: false,
            mag,
        }
    }

    /// The value of `n`.
    pub fn from_i64(n: i64) -> Self {
        let b = Self::from_u128(n.unsigned_abs() as u128);
        if n < 0 { b.neg() } else { b }
    }

    /// The value that `s` denotes: decimal digits, optionally preceded
    /// by a sign, which may be Standard ML's `~` or the `-` that other
    /// languages write. Returns `None` if `s` is not such a numeral,
    /// including if it is empty or has no digits.
    pub fn parse(s: &str) -> Option<Self> {
        let (negative, digits) = match s.strip_prefix(['~', '-']) {
            Some(rest) => (true, rest),
            None => (false, s.strip_prefix('+').unwrap_or(s)),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        // Take the digits in chunks of nine, the most that always fit
        // in a u32 factor, so that one multiply-and-add carries nine
        // digits rather than one.
        let mut b = Self::zero();
        let bytes = digits.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            let end = (i + 9).min(bytes.len());
            let chunk = &digits[i..end];
            let scale = 10u32.pow((end - i) as u32);
            b = b.mul_small(scale).add_small(chunk.parse::<u32>().ok()?);
            i = end;
        }
        if negative { Some(b.neg()) } else { Some(b) }
    }

    /// The value of the same magnitude and the opposite sign. Zero
    /// negates to itself.
    #[must_use]
    pub fn neg(&self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        BigInt {
            negative: !self.negative,
            mag: self.mag.clone(),
        }
    }

    /// The sum of this and `other`.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        if self.negative == other.negative {
            let mut r = BigInt {
                negative: self.negative,
                mag: add_mag(&self.mag, &other.mag),
            };
            r.normalize();
            return r;
        }
        // Signs differ, so this is a subtraction: the larger magnitude
        // keeps its sign.
        match cmp_mag(&self.mag, &other.mag) {
            Ordering::Equal => Self::zero(),
            Ordering::Greater => {
                let mut r = BigInt {
                    negative: self.negative,
                    mag: sub_mag(&self.mag, &other.mag),
                };
                r.normalize();
                r
            }
            Ordering::Less => {
                let mut r = BigInt {
                    negative: other.negative,
                    mag: sub_mag(&other.mag, &self.mag),
                };
                r.normalize();
                r
            }
        }
    }

    /// The product of this and `other`.
    // As `is_negative`: offered, but not yet called outside tests.
    #[allow(dead_code)]
    #[must_use]
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut mag = vec![0u32; self.mag.len() + other.mag.len()];
        for (i, &a) in self.mag.iter().enumerate() {
            let mut carry = 0u64;
            for (j, &b) in other.mag.iter().enumerate() {
                let t =
                    u64::from(a) * u64::from(b) + u64::from(mag[i + j]) + carry;
                mag[i + j] = (t & 0xFFFF_FFFF) as u32;
                carry = t >> 32;
            }
            let mut k = i + other.mag.len();
            while carry != 0 {
                let t = u64::from(mag[k]) + carry;
                mag[k] = (t & 0xFFFF_FFFF) as u32;
                carry = t >> 32;
                k += 1;
            }
        }
        let mut r = BigInt {
            negative: self.negative != other.negative,
            mag,
        };
        r.normalize();
        r
    }

    /// This times `n`.
    fn mul_small(&self, n: u32) -> Self {
        if n == 0 || self.is_zero() {
            return Self::zero();
        }
        let mut mag = Vec::with_capacity(self.mag.len() + 1);
        let mut carry = 0u64;
        for &d in &self.mag {
            let t = u64::from(d) * u64::from(n) + carry;
            mag.push((t & 0xFFFF_FFFF) as u32);
            carry = t >> 32;
        }
        while carry != 0 {
            mag.push((carry & 0xFFFF_FFFF) as u32);
            carry >>= 32;
        }
        BigInt {
            negative: self.negative,
            mag,
        }
    }

    /// This plus `n`. Only used where this is not negative.
    fn add_small(&self, n: u32) -> Self {
        self.add(&Self::from_u128(u128::from(n)))
    }

    /// Drops leading zero digits, and unsets the sign of zero, so that
    /// a value has one representation.
    fn normalize(&mut self) {
        while self.mag.last() == Some(&0) {
            self.mag.pop();
        }
        if self.mag.is_empty() {
            self.negative = false;
        }
    }
}

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.negative, other.negative) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            // Among negatives the larger magnitude is the smaller
            // value.
            (true, true) => cmp_mag(&other.mag, &self.mag),
            (false, false) => cmp_mag(&self.mag, &other.mag),
        }
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for BigInt {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        if self.is_zero() {
            return f.write_str("0");
        }
        // Repeatedly divide by 10^9, which yields nine decimal digits
        // at a time; the last chunk out is the most significant, and
        // is the only one not padded.
        let mut mag = self.mag.clone();
        let mut chunks = Vec::new();
        while !mag.is_empty() {
            let mut rem = 0u64;
            for d in mag.iter_mut().rev() {
                let t = (rem << 32) | u64::from(*d);
                *d = (t / 1_000_000_000) as u32;
                rem = t % 1_000_000_000;
            }
            while mag.last() == Some(&0) {
                mag.pop();
            }
            chunks.push(rem as u32);
        }
        if self.negative {
            f.write_str("-")?;
        }
        let mut it = chunks.iter().rev();
        write!(f, "{}", it.next().expect("non-zero has a chunk"))?;
        for c in it {
            write!(f, "{:09}", c)?;
        }
        Ok(())
    }
}

/// The sum of two magnitudes.
fn add_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len().max(b.len()) + 1);
    let mut carry = 0u64;
    for i in 0..a.len().max(b.len()) {
        let t = u64::from(a.get(i).copied().unwrap_or(0))
            + u64::from(b.get(i).copied().unwrap_or(0))
            + carry;
        out.push((t & 0xFFFF_FFFF) as u32);
        carry = t >> 32;
    }
    if carry != 0 {
        out.push(carry as u32);
    }
    out
}

/// `a` minus `b`, which the caller must know is not larger.
fn sub_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0i64;
    for (i, &ai) in a.iter().enumerate() {
        let t =
            i64::from(ai) - i64::from(b.get(i).copied().unwrap_or(0)) - borrow;
        if t < 0 {
            out.push((t + (1i64 << 32)) as u32);
            borrow = 1;
        } else {
            out.push(t as u32);
            borrow = 0;
        }
    }
    out
}

/// Compares two magnitudes.
fn cmp_mag(a: &[u32], b: &[u32]) -> Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    Ordering::Equal
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(s: &str) -> BigInt {
        BigInt::parse(s).expect("valid numeral")
    }

    #[test]
    fn test_parse_and_display_round_trip() {
        // A numeral of any length reads and writes back unchanged.
        for s in [
            "0",
            "1",
            "9",
            "10",
            "999999999",
            "1000000000",
            "4294967295",
            "4294967296",
            "18446744073709551615",
            // 2^72, which counts the values of a nine-character word,
            // and which no machine integer holds.
            "4722366482869645213696",
        ] {
            assert_eq!(b(s).to_string(), s, "round trip of {}", s);
        }
        // A sign is read either way, and written Rust's way.
        assert_eq!(b("~7").to_string(), "-7");
        assert_eq!(b("-7").to_string(), "-7");
        assert_eq!(b("+7").to_string(), "7");
        // Zero has one representation, however it is written.
        assert_eq!(b("~0").to_string(), "0");
        assert!(!b("~0").is_negative());
    }

    #[test]
    fn test_parse_rejects_what_is_not_a_numeral() {
        // Digits are read nine at a time, so a stray character is
        // rejected wherever it falls: in the first chunk, at a chunk
        // boundary, or in a later chunk.
        for s in [
            "",
            "~",
            "-",
            "+",
            "a",
            "1a",
            "123x",
            "12x34",
            " 1",
            "1 ",
            "1.5",
            "~~1",
            "0x1f",
            "~123x",
            "123456789x",
            "1234567890x",
            "123456789012345678x",
            "12345678901234567890x9",
        ] {
            assert!(BigInt::parse(s).is_none(), "should reject {:?}", s);
        }
    }

    #[test]
    fn test_from_u128() {
        assert_eq!(BigInt::from_u128(0).to_string(), "0");
        assert_eq!(
            BigInt::from_u128(u128::MAX).to_string(),
            "340282366920938463463374607431768211455"
        );
        assert_eq!(
            BigInt::from_i64(i64::MIN).to_string(),
            "-9223372036854775808"
        );
    }

    #[test]
    fn test_neg() {
        assert_eq!(b("5").neg().to_string(), "-5");
        assert_eq!(b("~5").neg().to_string(), "5");
        // Zero negates to itself, and stays unsigned.
        assert_eq!(BigInt::zero().neg(), BigInt::zero());
    }

    #[test]
    fn test_cmp() {
        assert!(b("2") < b("10")); // not string order
        assert!(b("~10") < b("~2")); // among negatives, larger is smaller
        assert!(b("~1") < b("0"));
        assert!(b("0") < b("1"));
        assert_eq!(b("7"), b("+7"));
        assert!(b("4722366482869645213696") > b("18446744073709551615"));
    }

    #[test]
    fn test_add() {
        assert_eq!(b("2").add(&b("3")).to_string(), "5");
        // Carrying the whole way up.
        assert_eq!(b("4294967295").add(&b("1")).to_string(), "4294967296");
        assert_eq!(
            b("18446744073709551615").add(&b("1")).to_string(),
            "18446744073709551616"
        );
        // Signs that differ subtract, and the larger magnitude wins.
        assert_eq!(b("5").add(&b("~3")).to_string(), "2");
        assert_eq!(b("3").add(&b("~5")).to_string(), "-2");
        assert_eq!(b("~3").add(&b("~5")).to_string(), "-8");
        // A sum of zero is zero, not negative zero.
        assert_eq!(b("5").add(&b("~5")), BigInt::zero());
    }

    #[test]
    fn test_mul() {
        assert_eq!(b("6").mul(&b("7")).to_string(), "42");
        assert_eq!(b("~6").mul(&b("7")).to_string(), "-42");
        assert_eq!(b("~6").mul(&b("~7")).to_string(), "42");
        assert_eq!(b("5").mul(&BigInt::zero()), BigInt::zero());
        // 2^36 squared is 2^72, the count this exists for.
        assert_eq!(
            b("68719476736").mul(&b("68719476736")).to_string(),
            "4722366482869645213696"
        );
        // A product wider than the operands, carrying through.
        assert_eq!(
            b("4294967295").mul(&b("4294967295")).to_string(),
            "18446744065119617025"
        );
    }

    #[test]
    fn test_against_known_answers() {
        // Sums, products and orderings computed independently.
        for (x, y, sum, prod, ord) in [
            (
                "-59835241579195470773055888625687590849",
                "1858116949505851198455730042046470115364176036626517",
                "1858116949505791363214150846575697059475550349035668",
                "-111180876556080358690173437107118185518405929960637043868114637847309028418878606919942933",
                Ordering::Less,
            ),
            (
                "349485380",
                "-2674946116889110620797816927640970381432883",
                "-2674946116889110620797816927640970031947503",
                "-934854560140515243171560952127037037323816059750540",
                Ordering::Greater,
            ),
            (
                "-922539840931464700676368909311301004295960360",
                "-8994885209409357454891297918949889317149",
                "-922548835816674110033823800609219954185277509",
                "8298139970285293180139010216922010642717487258463519776161347583518018181859572213640",
                Ordering::Less,
            ),
            (
                "36938864480697858808554112351200417588207361576102",
                "-199802137790566730102098686513403021773219893139",
                "36739062342907292078452013664687014566434141682963",
                "-7380464090799464747463249428964106971585984727318724330703892976448283535507960428588723056164178",
                Ordering::Greater,
            ),
            (
                "-94359225976633766497689825841105494271253",
                "-485674050923496030903638379479943910429017",
                "-580033276900129797401328205321049404700270",
                "45827827522077297410248107535115084750541409904934518619797452874788321255000148301",
                Ordering::Greater,
            ),
            (
                "-40421508777446235350600794366742072907633183223266286927",
                "-21935331955212109474070845995359443576575209216998",
                "-40421530712778190562710268437588068267076759798475503925",
                "886659213163803174548418439187946184958806726074403041799642642019631559728755960437540201671330473585146",
                Ordering::Less,
            ),
            (
                "-7022420564388164490600972898760079379000733979865961141",
                "-1301805478982112193589105942384909234224351",
                "-7022420564389466296079955010953668484943118889100185492",
                "9141825566437169117025933647251315942559241635199535880973030324500729055090372016572984241944491",
                Ordering::Less,
            ),
            (
                "315155386598420764932202651033045145539643924208160",
                "2813737928485848331619747757930482481684337964031",
                "317969124526906613263822398790975628021328262172191",
                "886764664638597129972330287915967188546598896668728404232820173150634017351612681134271488236692960",
                Ordering::Greater,
            ),
            (
                "-4040222368702026014091451724769893010696",
                "656422618682554890504033921075834346382956144218815987263569",
                "656422618682554890499993698707132320368864692494046094252873",
                "-2652093347323218714555375563934575374700427578531710539826137772521650891411137242889722727888134024",
                Ordering::Less,
            ),
            (
                "-154343606535999050706",
                "33125738523173651142856878221576540453412150872662",
                "33125738523173651142856878221422196846876151821956",
                "-5112745952835100283930803121584288978172177579651219585484481487199372",
                Ordering::Less,
            ),
            (
                "20257244605842631881968564",
                "1582226873711045898886676600697118598",
                "1582226873731303143492519232579087162",
                "32051556802702335672425881121816726528274037780590426815753272",
                Ordering::Less,
            ),
            (
                "-304318556294351100344970",
                "6383417832575455359191682986312571867610002538814313362",
                "6383417832575455359191682986312267549053708187713968392",
                "-1942592499032978398931963061286931468530044496616612329927553681664171880489140",
                Ordering::Less,
            ),
            (
                "678248141888570852239312655783437004956265418209837301906467",
                "-23720346294259759319",
                "678248141888570852239312655783437004956241697863543042147148",
                "-16088280799035129051321192094180881107591197052800913488437461174727319269615973",
                Ordering::Greater,
            ),
            (
                "-37590754482162853750224965354128661196651546634346463",
                "-174434556743028511417149615329760732576267456496435",
                "-37765189038905882261642114969458421929227814090842898",
                "6557126595732089659542436785392951250157430585211187233336396880871369144193135399090825009029914359405",
                Ordering::Less,
            ),
            (
                "20182551980947355519576298497157210825615917652864591055",
                "96802608133642474695359370950193993414613",
                "20182551980947452322184432139631906184986867846858005668",
                "1953723670548516517399712854546175358180999335113928455755830088592928932288121478669679306086715",
                Ordering::Greater,
            ),
            (
                "-1428822088466257497564923446461151288",
                "-1190304947598457594096023716437411441",
                "-2619127036064715091660947162898562729",
                "1700734001139347371382141251238556880162850222758135024083204743403086008",
                Ordering::Less,
            ),
            (
                "319976808897947584758174173918403960630555",
                "-83652471730530314278649110326648296333562467",
                "-83332494921632366693890936152729892372931912",
                "-26766850960760861059600103270161891834514168594396571984731662203581758094778801379185",
                Ordering::Greater,
            ),
            (
                "1310149710149224385449349056501",
                "-3659711384948428312820611708722770507142896643929",
                "-3659711384948428311510461998573546121693547587428",
                "-4794769810219999901338629041795529922796550684408339828558278896798655499632429",
                Ordering::Greater,
            ),
            (
                "-78072394101362644268361897117920323768391183388352374",
                "-11142708056450956905023355479437127236937232030540855251209",
                "-11142786128845058267667623841334245157261000421724243603583",
                "869937894739667702078252509476212113188603988171983027384927710358409217177219862289225864864627331044381520166",
                Ordering::Greater,
            ),
            (
                "1206279783111041448982936491919727650393906645960",
                "-872173275308038823554570064943416",
                "1206279783111040576809661183880904095823841702544",
                "-1052084989373827714487380283183378229339416620224638067995856319964080373744999360",
                Ordering::Greater,
            ),
            (
                "-107965535574290830151734300517974553852492907802578271",
                "5772128490131782723311581942963077031405541043860706205784",
                "5772020524596208432481430208662559056851688550952903627513",
                "-623190943840700604566350104668635478308239444455834769986764030552552360503160843499193181795003125565092919464",
                Ordering::Less,
            ),
            (
                "-52433011651156733542184639068927",
                "118264442853505504711210151941445112500747127269923",
                "118264442853505504658777140290288378958562488200996",
                "-6200960910055413819758440028540799163196767793903381682771225540028254554130982621",
                Ordering::Less,
            ),
            (
                "516079034845393652721709890541514067223270133871161965",
                "36895093584299682319457654120521087332343125756908764",
                "552974128429693335041167544662035154555613259628070729",
                "19040784287515855550673017793154620844633476678418953759451236443291454370512440295344578895776363171961260",
                Ordering::Greater,
            ),
            (
                "-18357168685029165965350154198842015293220557803128273644",
                "1237296621287010737166515023296",
                "-18357168685029165965350152961545394006209820636613250348",
                "-22713262790382304851956235033502885111965142988635670000685713101556134695506922810624",
                Ordering::Less,
            ),
            (
                "-2041631936599733545633941838063384",
                "-1222695655633874663661",
                "-2041631936600956241289575712727045",
                "2496294499283868437536077083143747109024583660599488824",
                Ordering::Less,
            ),
            (
                "986869274881510482286842",
                "169100247129904865071142341442565590114",
                "169100247129905851940417222953047876956",
                "166879838267373438284132808160328637615565937398074973947479988",
                Ordering::Less,
            ),
            (
                "37284537987188898",
                "-48527605278274168974125364086032425556885577377",
                "-48527605278274168974125364085995141018898388479",
                "-1809329342425121726498489391336755839814573292248028891894360546",
                Ordering::Greater,
            ),
            (
                "8860994956087233532663626880",
                "-2837617346412679234274319504819523398660",
                "-2837617346403818239318232271286859771780",
                "-25144112993868390774825852137960744385834390924688281143259731980800",
                Ordering::Greater,
            ),
            (
                "-2758491737581781727794212959931120932",
                "17152501785327683800781908015194162843",
                "14394010047745902072987695055263041911",
                "-47315034453683175726466909754684927033004073134518295411912741504333929676",
                Ordering::Less,
            ),
            (
                "10515332091995",
                "-223843807100216848438323455193",
                "-223843807100216837922991363198",
                "-2353791968395248467507101626825085336480035",
                Ordering::Greater,
            ),
            (
                "1853062566667995874913618861911262061379207671181592478",
                "35809861808640146482279",
                "1853062566667995874913618861911297871241016311328074757",
                "66357914435144950780466157859641365194304878456791540684331388372209026697362",
                Ordering::Greater,
            ),
            (
                "8553266266516438478467276643",
                "-68278238052369560722710800639353147993068577",
                "-68278238052369552169444534122914669525791934",
                "-584001950270511614466993117282661965236260984915371765141189077929347011",
                Ordering::Greater,
            ),
            (
                "-454575543473722252352015059260438846",
                "14891263911747646142851758229391210697268766611379",
                "14891263911747191567308284507138858682209506172533",
                "-6769204385693313405000066900477758811469182025858074902216014919609341684471877228634",
                Ordering::Less,
            ),
            (
                "-1457668776448173319",
                "224403518974135582526922463532181",
                "224403518974134124858146015358862",
                "-327106002933692660133983873640948162217330022078739",
                Ordering::Less,
            ),
            (
                "-22264824026338971705799899368291376573347",
                "244392807229680543043084436542532836859975251004399913110586",
                "244392807229680543020819612516193865154175351636108536537239",
                "-5441362846271820101802264308277475332871000309243436678456542762786730609578430922211835088551151342",
                Ordering::Less,
            ),
            (
                "-280106824802075731355806116673381168753502683425780902252787",
                "-26366856148492092432928569021930268212362270506",
                "-280106824802102098211954608765814097322524613693993264523293",
                "7385536355767207829357182768539059322382016188091735173924675989618706574956257160150989395411097686400222",
                Ordering::Less,
            ),
            (
                "70296501449488018107658745654343345054328559673",
                "-36554994035749140878557411267395274679638209213116378",
                "-36554923739247691390539303608649620336293154884556705",
                "-2569688191220065338584819223712167401311642997569694545133828443755706740456949062090061516466624394",
                Ordering::Greater,
            ),
            (
                "-155086695044303238091291388016809972718",
                "35164058082869666607412213581062259616577",
                "35008971387825363369320922193045449643859",
                "-5453477552418174347396796940298794040270646268413978698017307804490092510546286",
                Ordering::Less,
            ),
            (
                "156756939991325589833176043398259599959159046",
                "-17177647566655028507789620031421133510155211071139",
                "-17177490809715037182199786855377735250555251912093",
                "-2692715468798282343799555821870375321004813758068829669313452701872644753768282176183321373394",
                Ordering::Greater,
            ),
            (
                "-32084859332406211961908003512468",
                "-10210603473560872180390756776969",
                "-42295462805967084142298760289437",
                "327605776148178834316329397341754170892559009992457526886749492",
                Ordering::Less,
            ),
            (
                "576831845688092291066180396346",
                "96617577549953113983780587949053979498494368069",
                "96617577549953114560612433637146270564674764415",
                "55732095584051844696371051341767583299063739417105681699154371668055226675874",
                Ordering::Less,
            ),
            (
                "-241826148776867065175",
                "1479782413627721435756519492003047320251498666004306811",
                "1479782413627721435756519492003047078425349889137241636",
                "-357850082115328801598574451456618341343231567467390179068487404171833406925",
                Ordering::Less,
            ),
            (
                "-13707712986620265290380979094295659651966711204414317",
                "-79543475562651583292539772162271106413873814232110534",
                "-93251188549271848582920751256566766065840525436524851",
                "1090359132971070821860388470547139218000344492965965397234261040549638415863804584732336500875428276115278",
                Ordering::Greater,
            ),
            (
                "172552201478595183863131127928826016773374152267223941",
                "12075544407529646221155856306847272481425214",
                "172552201490670728270660774149981873080221424748649155",
                "2083661771571778824180831645751264399407227936497828564917216114119680167948018066255822981848374",
                Ordering::Greater,
            ),
            (
                "109749721538484494994043205751",
                "186675683639255811148587231373430139216027646776888",
                "186675683639255811148696981094968623711021689982639",
                "20487604297414551153338577190828307435030143391252269504253609496614430175482888",
                Ordering::Less,
            ),
            (
                "-56037373684689520798575477701152144028767099875",
                "-4605824308582982227593191",
                "-56037373684689520798580083525460727010994693066",
                "258098297906091315266122865340789516523846863459678298918027306366951125",
                Ordering::Less,
            ),
            (
                "14520220401132972511461876892",
                "5674776175750820071522190932632269",
                "5674790695971221204494702394509161",
                "82399000799000408335070407742295228826339300905552232784627948",
                Ordering::Less,
            ),
            (
                "-11365020145244770472",
                "-24266990766230429397000268122752927884902267323562121288301",
                "-24266990766230429397000268122752927884913632343707366058773",
                "275794838922677658592778113649754789282179297586228231247132694972703683848072",
                Ordering::Greater,
            ),
            (
                "31165251315305381259320425156287430436861213534970478466310",
                "-23091601836959468461742",
                "31165251315305381259320425156287430413769611698011010004568",
                "-719655574521809232527702418029082418744531221362177410363583975242612191070912020",
                Ordering::Greater,
            ),
            (
                "-1889610012342980566176764265491887593594",
                "-962599617642",
                "-1889610012342980566176764266454487211236",
                "1818937875373847993564389959747259972646427888585348",
                Ordering::Less,
            ),
            (
                "-283037532894226407078710527873879",
                "415287224791600153104405293844",
                "-282622245669434806925606122580035",
                "-117541871547504524596574418071167892731686515402775689567100876",
                Ordering::Less,
            ),
            (
                "-363166053446752068104714483163328587470083511541",
                "-271377293926865227860",
                "-363166053446752068104714483434705881396948739401",
                "98555020830478882763349850959560616714565666667441733370677904732260",
                Ordering::Less,
            ),
            (
                "-733341661768666550179687349366200008491773528038822216720",
                "-2162344368010520336840489715364",
                "-733341661768666550179687351528544376502293864879311932084",
                "1585737212152952034952007178847211438788373717142082687368186379241058975992792321686080",
                Ordering::Less,
            ),
            (
                "109011262738810922260934779141735474791759965998724764182250",
                "-130436056491913032793986239246306265739",
                "109011262738810922260804343085243561758965979759478457916511",
                "-14218999224854315691989482846051243235756540292661642732732737882173518264010094359543377526932750",
                Ordering::Greater,
            ),
            (
                "104602266179065972285901614737637850885",
                "1900027907317",
                "104602266179065972285901616637665758202",
                "198747224908826524916065563872505211812835846425545",
                Ordering::Greater,
            ),
            (
                "8530532499627533791921016805391010959560260434",
                "22988053410903913924414258416",
                "8530532499627533814909070216294924883974518850",
                "196100336724889419024341858313066284409525224059995560724104956559936312544",
                Ordering::Greater,
            ),
            (
                "-110004432040107391889491651052978205594748804324137272165",
                "-3254759807428305196650124891096459141644415132",
                "-110004432043362151696919956249628330485845263465781687297",
                "358038004043120020982838707253782882033500576155846033563623305553739495202654515099500201293328400780",
                Ordering::Less,
            ),
            (
                "-7543721577647769780708585598053258929285290796507764883",
                "-31933398631093638329859",
                "-7543721577647769780708585598053290862683921890146094742",
                "240896668301008833204934955294861937590511278777508311910382206106369170541497",
                Ordering::Less,
            ),
            (
                "311432448143313236744484292899",
                "-7135650198950362524597580642994447315345973222655431432",
                "-7135650198950362524597580331561999172032736478171138533",
                "-2222273010553431557810884504038552973668457701993624821020659673711651108774299001368",
                Ordering::Greater,
            ),
            (
                "1675543905242255826967247849200270",
                "23090409391369019531980412435271540696027331",
                "23090409393044563437222668262238788545227601",
                "38688994725256906504754140553790884859871944975895237657540636210154412579370",
                Ordering::Less,
            ),
        ] {
            let (x, y) = (b(x), b(y));
            assert_eq!(x.add(&y).to_string(), sum);
            assert_eq!(x.mul(&y).to_string(), prod);
            assert_eq!(x.cmp(&y), ord);
        }
    }
}
