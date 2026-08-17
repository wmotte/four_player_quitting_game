#!/usr/bin/env python3
"""Audit suite for the independent checker.

1. every exported certificate in this repository is accepted;
2. every hand-built good fixture is accepted;
3. every deliberately corrupted fixture is rejected for the stated reason;
4. the period-k case list matches its closed form, partitions the support
   patterns, and every periodic case named by the candidate manifest is on it.

Run from this directory: python3 run_tests.py
"""

import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import enumerate_cases as enum  # noqa: E402
from check_certificates import check_file, collect  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
REAL = os.path.join(HERE, "..", "certificates", "seed202_r78_gen011")
GOOD = os.path.join(HERE, "tests", "good")
BAD = os.path.join(HERE, "tests", "bad_certificates")
BADMAN = os.path.join(HERE, "tests", "bad_manifests")
EXPECTED = os.path.join(HERE, "tests", "expected_rejections.json")


def reject_targets():
    out = [(os.path.basename(f)[:-len(".json")], f) for f in collect([BAD])]
    if os.path.isdir(BADMAN):
        for d in sorted(os.listdir(BADMAN)):
            p = os.path.join(BADMAN, d, "manifest.json")
            if os.path.isfile(p):
                out.append((d, p))
    return out


def expect_accept(label, paths):
    failures = []
    files = collect(paths)
    for f in files:
        ok, msg = check_file(f)
        if not ok:
            failures.append(f"{os.path.basename(f)}: rejected — {msg}")
    print(f"{label}: {len(files) - len(failures)}/{len(files)} accepted")
    return failures


def expect_reject():
    with open(EXPECTED) as fh:
        expected = json.load(fh)
    failures = []
    targets = reject_targets()
    seen = set()
    for name, f in targets:
        seen.add(name)
        ok, msg = check_file(f)
        if ok:
            failures.append(f"{name}: ACCEPTED a corrupted certificate")
        elif name not in expected:
            failures.append(f"{name}: no expected rejection reason recorded")
        elif expected[name] not in msg:
            failures.append(f"{name}: rejected for the wrong reason\n"
                            f"      expected substring: {expected[name]!r}\n"
                            f"      actual message:     {msg!r}")
    for name in expected:
        if name not in seen:
            failures.append(f"{name}: expected fixture is missing")
    print(f"negative suite: {len(targets) - len(failures)}/{len(targets)} "
          f"rejected for the right reason")
    return failures


def _mutated_dump(lines, mutate):
    fd, path = tempfile.mkstemp(suffix=".txt")
    with os.fdopen(fd, "w") as fh:
        fh.write("\n".join(mutate(list(lines))) + "\n")
    return path


def _synthetic_dump():
    """A well-formed dump of the N=4, k=2 list, for the mutation suite."""
    header = ["# game synthetic (N = 4), period k = 2"]
    body = list(enum.all_cases(4, 2))
    return header + body


def check_enumeration():
    failures = []
    for line in enum.self_check():
        print(line.rstrip())

    original = _synthetic_dump()
    header = [l for l in original if l.startswith("#")]
    body = [l for l in original if not l.startswith("#")]
    mutations = [
        ("a dropped case", lambda ls: header + body[1:], "only in the checker"),
        ("a case outside the game", lambda ls: header + body + ["A {5}|{}"],
         "only in the certifier"),
        ("a malformed label", lambda ls: header + body + ["Z {2}|{2,3}"],
         "neither type A nor type B"),
        ("a set out of order", lambda ls: header + body + ["A {3,2}|{}"],
         "not strictly ascending"),
        ("a case visited twice", lambda ls: header + body + [body[0]],
         "which are the same case"),
        ("a missing header", lambda ls: body, "cannot be compared"),
    ]
    for name, mutate, expected in mutations:
        path = _mutated_dump(original, mutate)
        try:
            enum.compare_dump(path)
            failures.append(f"case list with {name}: ACCEPTED")
        except (AssertionError, ValueError) as e:
            if expected not in str(e):
                failures.append(f"case list with {name}: rejected for the "
                                f"wrong reason\n      expected substring: "
                                f"{expected!r}\n      actual: {str(e)!r}")
        finally:
            os.unlink(path)
    print(f"case-list negative suite: "
          f"{len(mutations) - len(failures)}/{len(mutations)} rejected for "
          f"the right reason")

    man = os.path.join(REAL, "manifest.json")
    if os.path.isfile(man):
        try:
            for line in enum.check_manifest(man):
                print(line.rstrip())
        except AssertionError as e:
            failures.append(f"manifest: {e}")
    else:
        failures.append("candidate manifest is missing")
    return failures


def main():
    failures = []
    failures += expect_accept("exported certificates", [REAL])
    failures += expect_accept("good fixtures", [GOOD])
    failures += expect_reject()
    print("case enumeration")
    failures += check_enumeration()
    if failures:
        print("\nFAILURES:")
        for f in failures:
            print("  " + f)
        return 1
    print("\nall checker tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
