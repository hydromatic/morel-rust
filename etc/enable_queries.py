#!/usr/bin/env python3
"""
enable_queries.py — find and enable passing queries in .smli validate sections.

A "validate section" is a block of .smli code between
  set("mode", "validate");
and
  set("mode", "evaluate");
In validate mode the shell echoes expected output verbatim without evaluating.

This script:
  1. Finds every validate section in a .smli file.
  2. For each query block inside that section, runs it via the Morel binary
     (with the appropriate preamble) and checks whether actual output matches
     the expected output recorded in the file.
  3. Reports PASS / FAIL / PANIC / SKIP for every block.
  4. With --apply, rewrites the file to wrap passing blocks with
       set("mode", "evaluate") ... set("mode", "validate")
     so they are actually evaluated going forward.

Usage:
  python3 scripts/enable_queries.py [OPTIONS]

Options:
  --help, -h          Show this message and exit.
  --file FILE         .smli file to process (default: tests/script/relational.smli)
  --binary BIN        Morel binary path (default: target/debug/main)
  --section N         Only process section N (1-based; default: all sections)
  --apply             Rewrite the file to enable passing queries.
  --verify            Run and report only; never modify the file (default).
  --verbose, -v       Show expected vs actual output for failing blocks.
  --no-skip           Do not skip blocks that use scott.* (will likely error).

Exit codes:
  0   All tested blocks passed (or nothing to test).
  1   One or more blocks failed or panicked.
  2   Argument error.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from typing import List, Optional, Tuple

DEFAULT_FILE = "tests/script/relational.smli"
DEFAULT_BINARY = "target/debug/main"

# Preamble used when testing queries from section 1 (emps/depts queries).
# Has exactly PREAMBLE_STMT_COUNT statements so we can locate the query output.
PREAMBLE_STMT_COUNT = 6
PREAMBLE = """\
Sys.set ("lineWidth", 78);
Sys.set ("printDepth", 6);
Sys.set ("printLength", 64);
Sys.set ("stringDepth", ~1);
val emps =
  let
    val emp0 = {id = 100, name = "Fred", deptno = 10}
    and emp1 = {id = 101, name = "Velma", deptno = 20}
    and emp2 = {id = 102, name = "Shaggy", deptno = 30}
    and emp3 = {id = 103, name = "Scooby", deptno = 30}
  in
    [emp0, emp1, emp2, emp3]
  end;
val depts =
  [{deptno = 10, name = "Sales"},
   {deptno = 20, name = "HR"},
   {deptno = 30, name = "Engineering"},
   {deptno = 40, name = "Support"}];
"""

MODE_SWITCH_EVALUATE = 'set("mode", "evaluate");\n> val it = () : unit\n'
MODE_SWITCH_VALIDATE = 'set("mode", "validate");\n> val it = () : unit\n'

# Blocks whose input_text contains any of these substrings are permanently
# skipped (not tested, not enabled).  Add entries here for queries that pass
# in isolation but produce wrong results when run after earlier blocks (e.g.
# because a prior let-binding leaks a name that shadows a local).
DENY_LIST: List[str] = [
    # Gives wrong answer (2 instead of 13) when 'g' is already bound in the
    # session by the prior 'Multiple functions' block.
    'converted to nested \'let\' expressions',
]


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass
class Block:
    """A single query block: input text + expected output + source location."""
    start_line: int        # 1-indexed, first line of input in the file
    end_line: int          # 1-indexed, last line of expected output
    input_text: str        # the query source (may be multi-line)
    expected_text: str     # expected output (without '> ' prefix)
    raw_lines: List[str]   # original lines from the file (including '>' lines)

    # Filled in after testing
    status: Optional[str] = None   # PASS / FAIL / PANIC / SKIP
    actual_text: Optional[str] = None
    error_msg: Optional[str] = None


@dataclass
class Section:
    """A validate-mode section of the file."""
    number: int            # 1-based index among all validate sections
    start_line: int        # line number of 'set("mode", "validate")'
    end_line: int          # line number of the closing 'set("mode", "evaluate")'
    blocks: List[Block] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def comment_depth(s: str) -> int:
    """Return comment nesting depth at end of string (0 = not in comment)."""
    depth = 0
    i = 0
    while i < len(s):
        if s[i] == '(' and i + 1 < len(s) and s[i + 1] == '*':
            # (*) is a line comment that ends at the next newline.
            if i + 2 < len(s) and s[i + 2] == ')':
                # Consume to end of line.
                while i < len(s) and s[i] != '\n':
                    i += 1
            else:
                depth += 1
                i += 2
        elif s[i] == '*' and i + 1 < len(s) and s[i + 1] == ')':
            depth = max(0, depth - 1)
            i += 2
        else:
            i += 1
    return depth


def parse_smli(lines: List[str]) -> Tuple[List[Section], List[Tuple[int, str]]]:
    """
    Parse an .smli file and return (sections, mode_switches).
    sections: list of Section objects for validate-mode regions.
    mode_switches: list of (line_idx, mode_string) for all set("mode", ...) calls.
    """
    # Find all mode-switch lines.
    mode_switches = []
    for i, line in enumerate(lines):
        s = line.strip()
        if s.startswith('set("mode",') or s.startswith("set('mode',"):
            m = re.search(r'set\s*\(\s*["\']mode["\']\s*,\s*["\'](\w+)["\']\s*\)', s)
            if m:
                mode_switches.append((i, m.group(1)))

    # Find validate sections: regions between 'validate' and 'evaluate'.
    sections = []
    sec_num = 0
    i = 0
    while i < len(mode_switches):
        idx, mode = mode_switches[i]
        if mode == 'validate':
            # Find the matching 'evaluate'
            j = i + 1
            while j < len(mode_switches) and mode_switches[j][1] != 'evaluate':
                j += 1
            end_idx = mode_switches[j][0] if j < len(mode_switches) else len(lines) - 1
            sec_num += 1
            section = Section(
                number=sec_num,
                start_line=idx + 1,  # 1-indexed
                end_line=end_idx + 1,
            )
            section.blocks = parse_blocks(lines, idx + 1, end_idx)
            sections.append(section)
            i = j
        else:
            i += 1

    return sections, mode_switches


def parse_blocks(lines: List[str], start_idx: int, end_idx: int) -> List[Block]:
    """
    Parse lines[start_idx:end_idx] (0-indexed) into Block objects.
    Handles multi-line comments and multi-line statements.
    """
    blocks = []
    i = start_idx
    depth = 0  # comment nesting depth

    while i < end_idx:
        line = lines[i].rstrip('\n')
        stripped = line.strip()

        # Track comment depth entering this line.
        prev_depth = depth
        depth = _update_comment_depth(depth, line)

        # Skip blank lines, and lines inside (or completing) comments.
        if not stripped or prev_depth > 0 or depth > 0:
            i += 1
            continue

        # At this point depth == 0 and prev_depth == 0: we are outside comments.

        # Skip 'set("mode", ...)' directives and their following '>' lines.
        if stripped.startswith('set(') and 'mode' in stripped:
            i += 1
            while i < end_idx and lines[i].lstrip().startswith('>'):
                i += 1
            continue

        # Skip '>' lines (belong to a preceding block).
        if stripped.startswith('>'):
            i += 1
            continue

        # Start of a new query block.
        # NOTE: (*) line comments are NOT skipped here — the shell accumulates
        # them into the statement buffer, so they must be part of the block's
        # input text to get correct line numbers in error messages.
        block_start = i + 1  # 1-indexed
        input_lines = []
        raw_lines = []
        block_depth = 0

        # Collect input lines until we see a '>' line.
        # Skip blank lines between comment lines and query lines (don't include
        # them in the input so that block_start reflects the first real line).
        while i < end_idx:
            l = lines[i].rstrip('\n')
            if l.startswith('>') or l.startswith('> '):
                break
            input_lines.append(l)
            raw_lines.append(lines[i])
            block_depth = _update_comment_depth(block_depth, l)
            i += 1

        # Collect expected output lines (lines starting with '>').
        expected_lines = []
        while i < end_idx:
            l = lines[i].rstrip('\n')
            if l.startswith('> '):
                expected_lines.append(l[2:])
                raw_lines.append(lines[i])
                i += 1
            elif l == '>':
                expected_lines.append('')
                raw_lines.append(lines[i])
                i += 1
            else:
                break

        input_text = '\n'.join(input_lines).strip()
        expected_text = '\n'.join(expected_lines)

        if input_text:
            blocks.append(Block(
                start_line=block_start,
                end_line=i,
                input_text=input_text,
                expected_text=expected_text,
                raw_lines=raw_lines,
            ))

    return blocks


def _update_comment_depth(depth: int, line: str) -> int:
    """Update comment nesting depth after processing `line`."""
    i = 0
    while i < len(line):
        if line[i] == '(' and i + 1 < len(line) and line[i + 1] == '*':
            if i + 2 < len(line) and line[i + 2] == ')':
                # (*) line comment: skip to end
                return depth  # doesn't change depth (inline, self-closing)
            else:
                depth += 1
                i += 2
        elif line[i] == '*' and i + 1 < len(line) and line[i + 1] == ')':
            depth = max(0, depth - 1)
            i += 2
        else:
            i += 1
    return depth


# ---------------------------------------------------------------------------
# Running queries
# ---------------------------------------------------------------------------

def extract_output_blocks(raw_output: str) -> List[List[str]]:
    """
    Split binary output into blocks of output lines.
    Each block corresponds to one statement's '> ...' output.
    Input echo lines (no '>' prefix) separate blocks.
    """
    blocks: List[List[str]] = []
    current_output: List[str] = []
    in_output = False

    for line in raw_output.split('\n'):
        if line.startswith('> '):
            in_output = True
            current_output.append(line[2:])
        elif line == '>':
            in_output = True
            current_output.append('')
        else:
            if in_output and current_output:
                blocks.append(current_output[:])
                current_output = []
                in_output = False
            # non-'>' line: input echo or blank — don't append to output

    if current_output:
        blocks.append(current_output[:])

    return blocks


def run_block(block: Block, binary: str, use_scott: bool = False) -> Block:
    """Run a block and fill in block.status, block.actual_text, block.error_msg."""
    for pattern in DENY_LIST:
        if pattern in block.input_text:
            block.status = 'SKIP'
            block.error_msg = f'deny-list: {pattern!r}'
            return block

    if ('scott.' in block.input_text or 'scott.' in block.expected_text) \
            and not use_scott:
        block.status = 'SKIP'
        block.error_msg = 'uses scott.*'
        return block

    content = PREAMBLE + '\n' + block.input_text + '\n'

    with tempfile.NamedTemporaryFile(
        mode='w', suffix='.smli', delete=False, prefix='/tmp/morel_eq_'
    ) as f:
        f.write(content)
        tmp_path = f.name

    try:
        result = subprocess.run(
            [binary, tmp_path],
            capture_output=True,
            text=True,
            timeout=15,
        )
    except subprocess.TimeoutExpired:
        os.unlink(tmp_path)
        block.status = 'PANIC'
        block.error_msg = 'timeout'
        return block
    finally:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)

    if result.returncode != 0:
        block.status = 'PANIC'
        block.error_msg = (result.stderr or '').strip().splitlines()[-1] \
            if result.stderr else f'exit code {result.returncode}'
        return block

    out_blocks = extract_output_blocks(result.stdout)

    if len(out_blocks) <= PREAMBLE_STMT_COUNT:
        block.status = 'PANIC'
        block.error_msg = (
            f'binary produced {len(out_blocks)} output blocks; '
            f'expected >{PREAMBLE_STMT_COUNT} (preamble + query)'
        )
        return block

    # Collect all output from the query statement(s) after the preamble.
    query_output_lines: List[str] = []
    for ob in out_blocks[PREAMBLE_STMT_COUNT:]:
        query_output_lines.extend(ob)

    block.actual_text = '\n'.join(query_output_lines)
    expected = _normalize(block.expected_text)
    actual = _normalize(block.actual_text)

    block.status = 'PASS' if actual == expected else 'FAIL'
    return block


def _normalize(text: str) -> str:
    return '\n'.join(l.rstrip() for l in text.strip().split('\n'))


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

STATUS_SYMBOL = {
    'PASS': '✓',
    'FAIL': '✗',
    'PANIC': '!',
    'SKIP': '-',
}


def print_block_result(block: Block, verbose: bool = False) -> None:
    sym = STATUS_SYMBOL.get(block.status, '?')
    short = block.input_text[:72].replace('\n', ' ')
    print(f'  [{sym}] lines {block.start_line}-{block.end_line}: {short}')
    if block.status == 'PANIC' and block.error_msg:
        print(f'        error: {block.error_msg}')
    if verbose and block.status == 'FAIL':
        print(f'        expected: {repr(_normalize(block.expected_text)[:120])}')
        print(f'        actual:   {repr(_normalize(block.actual_text or "")[:120])}')


def print_summary(sections: List[Section]) -> None:
    counts = {'PASS': 0, 'FAIL': 0, 'PANIC': 0, 'SKIP': 0}
    for sec in sections:
        for blk in sec.blocks:
            if blk.status:
                counts[blk.status] = counts.get(blk.status, 0) + 1
    total = sum(counts.values())
    print(f'\nSummary: {counts["PASS"]} pass, {counts["FAIL"]} fail, '
          f'{counts["PANIC"]} panic, {counts["SKIP"]} skip  (of {total} blocks)')


# ---------------------------------------------------------------------------
# Applying changes
# ---------------------------------------------------------------------------

def apply_changes(smli_path: str, sections: List[Section], dry_run: bool) -> int:
    """
    Wrap passing blocks with evaluate/validate mode switches.
    Returns number of blocks enabled.
    """
    with open(smli_path) as f:
        original_lines = f.readlines()

    # Collect all edits as (line_idx, 'insert_before' | 'insert_after', text)
    # We'll process them in reverse line order to avoid index shifts.

    # For each section, find runs of consecutive passing blocks and wrap them.
    edits = []  # list of (after_line_idx, insert_text)
    # after_line_idx: insert AFTER this 0-indexed line

    for sec in sections:
        passing_blocks = [b for b in sec.blocks if b.status == 'PASS']
        if not passing_blocks:
            continue

        # Group consecutive passing blocks.
        # A "group" is a maximal sequence of passing blocks with no failing
        # block in between (blanks/comments are fine, but another FAIL/PANIC
        # block interrupts the group).
        # Strategy: process all blocks in order, grouping runs of PASS.
        groups = []
        current_group: List[Block] = []
        for blk in sec.blocks:
            if blk.status == 'PASS':
                current_group.append(blk)
            else:
                if current_group:
                    groups.append(current_group[:])
                    current_group = []
        if current_group:
            groups.append(current_group)

        for group in groups:
            first = group[0]
            last = group[-1]

            # Insert "set evaluate" before first block's first input line.
            # The first input line is at first.start_line (1-indexed) = index
            # first.start_line - 1.
            before_idx = first.start_line - 2  # 0-indexed line BEFORE the block
            edits.append((before_idx, '\n' + MODE_SWITCH_EVALUATE + '\n'))

            # Insert "set validate" after last block's last output line.
            after_idx = last.end_line - 1  # 0-indexed last line of block
            edits.append((after_idx, '\n' + MODE_SWITCH_VALIDATE))

    if not edits:
        print('No passing blocks to enable.')
        return 0

    # Sort in reverse order so we can apply without shifting indices.
    edits.sort(key=lambda e: e[0], reverse=True)

    new_lines = original_lines[:]
    enabled_count = sum(
        1 for sec in sections for b in sec.blocks if b.status == 'PASS'
    )

    if dry_run:
        print(f'\nDRY RUN: would enable {enabled_count} block(s) '
              f'across {len(sections)} section(s).')
        print('  (Use --apply to actually modify the file.)')
        # Show what would be inserted.
        for idx, text in sorted(edits, key=lambda e: e[0]):
            print(f'  insert after line {idx + 1}: '
                  f'{repr(text[:60])}{"..." if len(text) > 60 else ""}')
        return enabled_count

    # Apply edits.
    for after_idx, text in edits:
        insert_at = after_idx + 1  # insert after this index
        new_lines.insert(insert_at, text)

    with open(smli_path, 'w') as f:
        f.writelines(new_lines)

    print(f'\nEnabled {enabled_count} block(s). File updated: {smli_path}')
    return enabled_count


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def parse_args(argv: List[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        prog='enable_queries.py',
        description=__doc__.split('\n')[1].strip(),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='\n'.join(__doc__.split('\n')[2:]),
    )
    p.add_argument('--file', default=DEFAULT_FILE,
                   help=f'smli file to process (default: {DEFAULT_FILE})')
    p.add_argument('--binary', default=DEFAULT_BINARY,
                   help=f'Morel binary (default: {DEFAULT_BINARY})')
    p.add_argument('--section', type=int, default=None, metavar='N',
                   help='Only process section N (1-based)')
    action = p.add_mutually_exclusive_group()
    action.add_argument('--apply', action='store_true',
                        help='Rewrite file to enable passing queries')
    action.add_argument('--verify', action='store_true', default=True,
                        help='Report only; do not modify file (default)')
    p.add_argument('--verbose', '-v', action='store_true',
                   help='Show expected vs actual for failing blocks')
    p.add_argument('--no-skip', action='store_true', dest='no_skip',
                   help='Do not skip blocks that reference scott.*')
    return p.parse_args(argv)


def main(argv: List[str] = None) -> int:
    if argv is None:
        argv = sys.argv[1:]
    args = parse_args(argv)

    if not os.path.exists(args.binary):
        print(f'error: binary not found: {args.binary}', file=sys.stderr)
        print('  Run: cargo build --bin main', file=sys.stderr)
        return 2

    if not os.path.exists(args.file):
        print(f'error: file not found: {args.file}', file=sys.stderr)
        return 2

    with open(args.file) as f:
        all_lines = f.readlines()

    sections, _ = parse_smli(all_lines)

    if args.section is not None:
        sections = [s for s in sections if s.number == args.section]
        if not sections:
            print(f'error: no section {args.section} found', file=sys.stderr)
            return 2

    total_blocks = sum(len(s.blocks) for s in sections)
    print(f'Found {len(sections)} validate section(s), {total_blocks} block(s) total.\n')

    any_fail = False
    for sec in sections:
        print(f'Section {sec.number} '
              f'(lines {sec.start_line}-{sec.end_line}, '
              f'{len(sec.blocks)} blocks):')

        for blk in sec.blocks:
            run_block(blk, args.binary, use_scott=args.no_skip)
            print_block_result(blk, verbose=args.verbose)
            if blk.status in ('FAIL', 'PANIC'):
                any_fail = True
        print()

    print_summary(sections)

    if args.apply:
        apply_changes(args.file, sections, dry_run=False)
    elif not args.verify:
        # --apply was not given; default is verify-only
        pass
    else:
        # Check if there are any passing blocks to report
        passing = sum(
            1 for s in sections for b in s.blocks if b.status == 'PASS'
        )
        if passing:
            print(f'\n{passing} block(s) could be enabled with --apply.')

    return 1 if any_fail else 0


if __name__ == '__main__':
    sys.exit(main())
