#!/usr/bin/env python3
# Licensed to Julian Hyde under one or more contributor license
# agreements.  See the NOTICE file distributed with this work
# for additional information regarding copyright ownership.
# Julian Hyde licenses this file to you under the Apache
# License, Version 2.0 (the "License"); you may not use this
# file except in compliance with the License.  You may obtain a
# copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
# either express or implied.  See the License for the specific
# language governing permissions and limitations under the
# License.
"""Gate that a propagation commit converges morel-rust's `.smli` test files
toward morel-java's, instead of leaving sections behind.

The purpose of a propagation is to move `.smli` changes from morel-java to
morel-rust. This script measures whether that actually happened, by comparing
*deltas*:

    rust commit  vs  rust parent          (what rust changed)
    java commit  vs  java parent          (what java changed)

For every shared `.smli` file it computes the number of differing lines
between rust and java BEFORE the commit (at the parents) and AFTER (at the
commits). The gate fails if any file becomes MORE divergent — that is a
section that java changed but rust did not follow, even if other files
converged enough to hide it in the net.

Usage:
    etc/check-convergence.py [RUST_COMMIT] [--java JAVA_SHA]
                             [--java-repo PATH] [--verbose]

If JAVA_SHA is omitted it is read from RUST_COMMIT's message, from the line
`Propagates hydromatic/morel#NNN commit <sha>`.
"""
import argparse
import difflib
import os
import re
import subprocess
import sys

RUST_PREFIX = "tests/script/"
JAVA_PREFIX = "src/test/resources/script/"
DEFAULT_JAVA_REPO = os.path.expanduser("~/dev/morel.0")


def git(repo, *args):
    """Runs git in `repo`, returning stdout (empty string on failure)."""
    r = subprocess.run(
        ["git", "-C", repo, *args],
        capture_output=True,
        text=True,
    )
    return r.stdout if r.returncode == 0 else None


def smli_files(repo, commit, prefix):
    """Relative `.smli` paths (below `prefix`) present at `commit`."""
    out = git(repo, "ls-tree", "-r", "--name-only", commit)
    if out is None:
        sys.exit(f"error: cannot list files at {commit} in {repo}")
    files = set()
    for line in out.splitlines():
        if line.startswith(prefix) and line.endswith(".smli"):
            files.add(line[len(prefix):])
    return files


def file_at(repo, commit, prefix, rel):
    """Content of `prefix+rel` at `commit`, or empty if absent."""
    out = git(repo, "show", f"{commit}:{prefix}{rel}")
    return out if out is not None else ""


def diff_lines(a, b):
    """Number of differing lines between two file contents (added + removed,
    ignoring the unified-diff header lines)."""
    a_lines = a.splitlines(keepends=True)
    b_lines = b.splitlines(keepends=True)
    n = 0
    for line in difflib.unified_diff(a_lines, b_lines, n=0):
        if line.startswith(("+++", "---", "@@")):
            continue
        if line.startswith(("+", "-")):
            n += 1
    return n


def java_sha_from_message(repo, commit):
    """Extracts the morel-java SHA from `commit`'s 'Propagates ... commit'
    line."""
    msg = git(repo, "log", "-1", "--format=%B", commit) or ""
    m = re.search(r"[Pp]ropagates\s+\S*\s*commit\s+([0-9a-f]{7,40})", msg)
    return m.group(1) if m else None


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("rust_commit", nargs="?", default="HEAD")
    p.add_argument("--java", help="morel-java commit SHA (else from message)")
    p.add_argument("--java-repo", default=DEFAULT_JAVA_REPO)
    p.add_argument("--verbose", action="store_true",
                   help="list every file, not just regressions")
    args = p.parse_args()

    rust_repo = os.getcwd()
    rust = git(rust_repo, "rev-parse", args.rust_commit)
    if rust is None:
        sys.exit(f"error: bad rust commit {args.rust_commit}")
    rust = rust.strip()
    rust_parent = git(rust_repo, "rev-parse", f"{rust}^").strip()

    java = args.java or java_sha_from_message(rust_repo, rust)
    if not java:
        sys.exit("error: no java SHA given and none found in commit message "
                 "(expected a 'Propagates ... commit <sha>' line)")
    java_full = git(args.java_repo, "rev-parse", java)
    if java_full is None:
        sys.exit(f"error: bad java commit {java} in {args.java_repo}")
    java = java_full.strip()
    java_parent = git(args.java_repo, "rev-parse", f"{java}^").strip()

    print(f"rust  {rust[:9]}  (parent {rust_parent[:9]})")
    print(f"java  {java[:9]}  (parent {java_parent[:9]})")
    print()

    # Every relative .smli path seen on either side, at either revision.
    rels = (
        smli_files(rust_repo, rust, RUST_PREFIX)
        | smli_files(rust_repo, rust_parent, RUST_PREFIX)
        | smli_files(args.java_repo, java, JAVA_PREFIX)
        | smli_files(args.java_repo, java_parent, JAVA_PREFIX)
    )

    regressions = []
    improvements = []
    net_before = net_after = 0
    rows = []
    for rel in sorted(rels):
        before = diff_lines(
            file_at(rust_repo, rust_parent, RUST_PREFIX, rel),
            file_at(args.java_repo, java_parent, JAVA_PREFIX, rel),
        )
        after = diff_lines(
            file_at(rust_repo, rust, RUST_PREFIX, rel),
            file_at(args.java_repo, java, JAVA_PREFIX, rel),
        )
        net_before += before
        net_after += after
        if after > before:
            regressions.append((rel, before, after))
        elif after < before:
            improvements.append((rel, before, after))
        rows.append((rel, before, after))

    if args.verbose:
        print(f"{'file':40} {'before':>7} {'after':>7} {'delta':>7}")
        for rel, before, after in rows:
            if before == after:
                continue
            print(f"{rel:40} {before:7} {after:7} {after - before:+7}")
        print()

    if improvements:
        print(f"converged: {len(improvements)} file(s), "
              f"{sum(b - a for _, b, a in improvements)} fewer differing lines")
    print(f"net divergence: {net_before} -> {net_after} "
          f"({net_after - net_before:+d} lines)")
    print()

    if regressions:
        print(f"FAIL: {len(regressions)} file(s) diverged further from "
              f"morel-java:")
        for rel, before, after in regressions:
            print(f"  {rel:40} {before:7} -> {after:7} "
                  f"({after - before:+d})  -- java changed this; rust did not "
                  f"follow")
        return 1

    print("OK: no .smli file diverged further from morel-java.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
