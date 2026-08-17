#!/usr/bin/env python3
"""Second, independent enumeration of the periodic support patterns.

Every certificate proves one statement of the form "this system has no
solution in this region". No certificate proves the statement everything rests
on: *these are all the systems*. Miss one case and every certificate is still
valid, the checker still passes, Lean still compiles, and the theorem is still
false. That hinge is what this file addresses.

It re-derives the case list from the mathematical description, in Python,
inside the checker, sharing no code with the Julia pipeline, and then answers
three questions:

1. **Is the list the right size?**  Counted here from scratch, in closed form
   and by enumeration, and the two must agree.
2. **Does the list partition the space?**  Every one of the `3^(N*k)` support
   patterns of a period-k block is mapped to its case, and the images must be
   exactly the enumerated list, each pattern landing on exactly one case. This
   is the check that catches an off-by-one in the truncation or a bug in the
   rotation dedup.
3. **Is it the same list a certifier would walk?**  When a dump of that list
   is present, the two must be equal as sets. This public repository does not
   ship those dumps; the closed-form count and the partition check stand on
   their own.
4. **Does the corpus name cases from that list?**  Every `case` label in a
   manifest must be a member, with no duplicates.

## The description this file implements

A period-k profile plays the block `x^1, ..., x^k` cyclically. Each entry
`x^t_i` is 0 (sure continue), 1 (sure quit), or strictly between (mix), so a
support pattern is a map from the `k*N` entries to `{0, 1, 2}` writing 2 for
"mixes". Patterns fall into two classes.

**Type A** has no entry equal to 1, so every stage recurs with positive
probability. Being an equilibrium is then invariant under rotating the block,
so rotations of one block are one case and the representative is the
lexicographically smallest rotation. The all-continue block (no entry
anything but 0) is not a case here: the pipeline settles it separately by a
one-line check, and this module reports it as such rather than silently
dropping it.

**Type B** has a sure quitter. Let T be the *first* stage that has one. Stages
after T are reached with probability zero, so a Nash equilibrium imposes no
condition on them and they are not enumerated -- they survive as free
variables in the certifier and are handled by branch and bound. So a type-B
case is determined by stages 1..T only: stages before T are 0/2 (a 1 there
would contradict T being first), and stage T is 0/1/2 with at least one 1.

Two things this module does **not** establish, and the paper must not claim it
does. That truncating the tail is sound is a human lemma about reachability,
not a combinatorial fact. That rotation-invariance is legitimate is likewise a
lemma. This module checks that the enumeration implements those two
statements without gaps or overlaps; it does not prove the statements.

Usage:

    python3 enumerate_cases.py                       # self-check for N=4, k=2,3
    python3 enumerate_cases.py ../certificates/seed202_r78_gen011/manifest.json
"""

import itertools
import json
import os
import re
import sys

CONT, QUIT, MIX = 0, 1, 2

# Optional directory of dumped case lists (one file per (game, k)). The labels
# depend on N and k alone. This public repository does not ship those dumps;
# run_tests.py builds a synthetic list from all_cases for the mutation suite.
CASE_LISTS = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "tests", "case_lists")


# --- label format ------------------------------------------------------------
# The labels have to match the certifier's strings exactly, since the whole
# point is to compare two lists. This is the one place where the two
# implementations are coupled, and it is coupled to a rendering convention
# rather than to any mathematics.

def _set(players):
    """`{1,3}` for a sorted collection of 1-based player indices; `{}` if empty."""
    return "{" + ",".join(str(i) for i in sorted(players)) + "}"


def label_a(block):
    """`A {1,3}|{1,2,3,4}` -- one brace group per stage, listing the mixers."""
    return "A " + "|".join(_set(s) for s in block)


def label_b(stages):
    """`B q{}m{2}|q{2}m{1,4}` -- quitters and mixers per stage, up to T."""
    return "B " + "|".join("q" + _set(q) + "m" + _set(m) for q, m in stages)


# --- parsing and rotation-independent normalisation --------------------------
# A type-A case is a rotation CLASS, and which rotation gets printed is a
# convention, not mathematics: the certifier orders stages by the integer value
# of their mixing bitmask, this module orders them by their sorted player list,
# and the two pick different representatives for 44 of the 135 k=2 classes.
# Comparing the raw strings would report that as a difference and it is not
# one. So every label from either side is put through the normaliser below
# before anything is compared. Both sides then use one rule -- this module's --
# and the certifier's convention drops out entirely.

_SET_RE = re.compile(r"^\{([0-9,]*)\}$")
_QM_RE = re.compile(r"^q\{([0-9,]*)\}m\{([0-9,]*)\}$")

# The certifier appends a parenthesised note to the label when it did not
# decide the case on the plain system: `(saturated)` for the Rabinowitsch
# retry, `(aggregated, saturated)` for its type-B counterpart. That names the
# ROUTE, not the case -- `case` is documented (docs/CERTIFICATE_FORMAT.md) as
# the enumeration case the certificate refutes, and the enumeration has no
# such variants. Stripping it here is what lets the coverage check see the
# case at all; nothing is weakened, because the certificate still has to be in
# the enumeration and its equations are still re-derived from the payoff
# matrix (`bind_systems.py` reads saturation off the certificate's own
# variable list, never off this note). Before this, such a label raised and
# the certificate was silently skipped by the equation binding.
_ANNOTATION_RE = re.compile(r" \((?:saturated|aggregated, saturated)\)$")


def _parse_set(s):
    m = _SET_RE.match(s)
    if m is None:
        raise ValueError(f"not a player set: {s!r}")
    body = m.group(1)
    players = tuple(int(x) for x in body.split(",")) if body else ()
    if list(players) != sorted(players) or len(set(players)) != len(players):
        raise ValueError(f"player set not strictly ascending: {s!r}")
    return players


def parse_case(label):
    """('A', block) or ('B', stages) for a case label; ValueError if malformed."""
    label = _ANNOTATION_RE.sub("", label)
    if label.startswith("A "):
        return "A", tuple(_parse_set(s) for s in label[2:].split("|"))
    if label.startswith("B "):
        stages = []
        for part in label[2:].split("|"):
            m = _QM_RE.match(part)
            if m is None:
                raise ValueError(f"not a type-B stage: {part!r}")
            stages.append((_parse_set("{" + m.group(1) + "}"),
                           _parse_set("{" + m.group(2) + "}")))
        return "B", tuple(stages)
    raise ValueError(f"case label is neither type A nor type B: {label!r}")


def normalise(label):
    """The label rewritten with this module's choice of rotation representative."""
    kind, body = parse_case(label)
    if kind == "A":
        return label_a(min(_rotations(body)))
    return label_b(body)


# --- type A ------------------------------------------------------------------

def _rotations(block):
    k = len(block)
    return [tuple(block[(t + r) % k] for t in range(k)) for r in range(k)]


def type_a_cases(N, k):
    """Rotation classes of k-tuples of mixing sets, minus the all-continue one.

    Represented during enumeration as tuples of frozensets ordered by their
    sorted player lists, so "lexicographically minimal rotation" is a total
    and reproducible choice.
    """
    subsets = [tuple(s) for r in range(N + 1)
               for s in itertools.combinations(range(1, N + 1), r)]
    subsets.sort()
    out = []
    for block in itertools.product(subsets, repeat=k):
        if all(len(s) == 0 for s in block):
            continue                       # all-continue: not a case, see below
        if any(rot < block for rot in _rotations(block)[1:]):
            continue                       # not the minimal rotation
        out.append(label_a(block))
    return out


# --- type B ------------------------------------------------------------------

def type_b_cases(N, k):
    """First sure quit at stage T, stages 1..T enumerated and the tail dropped."""
    players = list(range(1, N + 1))
    out = []
    for T in range(1, k + 1):
        # stages before T: every player continues or mixes, never quits
        pre_choices = itertools.product([CONT, MIX], repeat=N * (T - 1))
        for pre in pre_choices:
            for last in itertools.product([CONT, QUIT, MIX], repeat=N):
                if QUIT not in last:
                    continue               # then T is not the first quit stage
                stages = []
                for t in range(T - 1):
                    row = pre[t * N:(t + 1) * N]
                    stages.append((set(), {i for i in players
                                           if row[i - 1] == MIX}))
                stages.append(({i for i in players if last[i - 1] == QUIT},
                               {i for i in players if last[i - 1] == MIX}))
                out.append(label_b(stages))
    return out


def all_cases(N, k):
    return type_a_cases(N, k) + type_b_cases(N, k)


# --- closed forms, derived here and compared against the enumeration ---------

def _rotation_class_count(m, k):
    """Burnside over the cyclic group: classes of k-tuples from an m-set."""
    from math import gcd
    return sum(m ** gcd(r, k) for r in range(k)) // k


def expected_counts(N, k):
    """(type A, type B) counts, from combinatorics rather than from the loops."""
    n_a = _rotation_class_count(2 ** N, k) - 1          # drop the all-continue class
    n_b = sum(2 ** (N * (T - 1)) * (3 ** N - 2 ** N) for T in range(1, k + 1))
    return n_a, n_b


# --- the partition check -----------------------------------------------------

def canonical_case(sigma, N, k):
    """The case a full k-stage support pattern belongs to.

    `sigma[t][i]` is the code for player i+1 at stage t+1. Returns None for the
    all-continue pattern, which is not a case.
    """
    first_quit = None
    for t in range(k):
        if QUIT in sigma[t]:
            first_quit = t
            break
    if first_quit is None:
        block = tuple(tuple(i + 1 for i in range(N) if sigma[t][i] == MIX)
                      for t in range(k))
        if all(len(s) == 0 for s in block):
            return None
        return label_a(min(_rotations(block)))
    stages = []
    for t in range(first_quit + 1):
        stages.append(({i + 1 for i in range(N) if sigma[t][i] == QUIT},
                       {i + 1 for i in range(N) if sigma[t][i] == MIX}))
    return label_b(stages)


def check_partition(N, k):
    """Map every support pattern to its case; the images must be the case list.

    Returns (n_patterns, n_cases, n_all_continue). Raises AssertionError on any
    case that no pattern reaches (an entry the certifier would solve for
    nothing) or any pattern that reaches no case (a genuine gap in coverage).
    """
    cases = all_cases(N, k)
    assert len(cases) == len(set(cases)), "the enumeration produced a duplicate"
    listed = set(cases)
    hit = set()
    n_all_continue = 0
    n_patterns = 0
    for flat in itertools.product([CONT, QUIT, MIX], repeat=N * k):
        sigma = [flat[t * N:(t + 1) * N] for t in range(k)]
        n_patterns += 1
        c = canonical_case(sigma, N, k)
        if c is None:
            n_all_continue += 1
            continue
        assert c in listed, f"pattern {sigma} maps to {c!r}, which is not a case"
        hit.add(c)
    missing = listed - hit
    assert not missing, f"{len(missing)} enumerated cases are unreachable: " \
                        f"{sorted(missing)[:3]}"
    return n_patterns, len(cases), n_all_continue


# --- comparison against the certifier's own enumeration ----------------------

_DUMP_HEADER = re.compile(r"^# game (\S+) \(N = (\d+)\), period k = (\d+)$")


def read_case_dump(path):
    """(game, N, k, [case, ...]) from a dumped case-list file."""
    game = N = k = None
    cases = []
    with open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if line.startswith("#"):
                m = _DUMP_HEADER.match(line)
                if m:
                    game, N, k = m.group(1), int(m.group(2)), int(m.group(3))
                continue
            if line:
                cases.append(line)
    if N is None:
        raise AssertionError(f"{path}: no `# game ... (N = n), period k = k` header, "
                             f"so the dump cannot be compared against anything")
    return game, N, k, cases


def compare_dump(path):
    """The certifier's list and this module's list must agree as sets.

    Compared after normalisation, so a different choice of rotation
    representative is not reported as a difference. Two dumped labels that
    normalise to the same case would be: that is the certifier visiting one
    rotation class twice.
    """
    game, N, k, theirs = read_case_dump(path)
    seen = {}
    for label in theirs:
        key = normalise(label)
        if key in seen:
            raise AssertionError(f"{path}: the certifier enumerates {seen[key]!r} "
                                 f"and {label!r}, which are the same case")
        seen[key] = label
    mine = set(all_cases(N, k))
    only_them = set(seen) - mine
    only_me = mine - set(seen)
    if only_them or only_me:
        raise AssertionError(
            f"{path}: the two enumerations differ. "
            f"{len(only_them)} case(s) only in the certifier "
            f"({sorted(only_them)[:3]}), "
            f"{len(only_me)} only in the checker ({sorted(only_me)[:3]})")
    rotated = sum(1 for key, label in seen.items() if key != label)
    return (f"  {game} N={N} k={k}: {len(theirs)} cases, identical to the "
            f"independent enumeration ({rotated} printed as a different "
            f"rotation of the same class)")


def compare_all_dumps(dirpath=CASE_LISTS):
    if not os.path.isdir(dirpath):
        return [f"  no case-list dumps under {os.path.relpath(dirpath)}"]
    files = sorted(f for f in os.listdir(dirpath) if f.endswith(".txt"))
    if not files:
        return [f"  no case-list dumps under {os.path.relpath(dirpath)}"]
    return [compare_dump(os.path.join(dirpath, f)) for f in files]


# --- manifest binding --------------------------------------------------------

_K_FROM_PATH = re.compile(r"periodic_k(\d+)")


def manifest_cases(path):
    """{k: [case, ...]} for the periodic claim groups of one manifest."""
    with open(path) as fh:
        man = json.load(fh)
    out = {}
    for claim in man.get("claims", []):
        for row in claim.get("case_table", []):
            m = _K_FROM_PATH.search(row.get("certificate", ""))
            if m is None or "pattern" not in row:
                continue
            out.setdefault(int(m.group(1)), []).append(row["pattern"])
    return man["game"]["N"], out


def check_manifest(path):
    """Every periodic case a manifest names must be in the enumeration."""
    N, groups = manifest_cases(path)
    lines = []
    for k in sorted(groups):
        try:
            named = [normalise(c) for c in groups[k]]
        except ValueError as e:
            raise AssertionError(f"{path}: {e}") from None
        listed = set(all_cases(N, k))
        dup = {c for c in named if named.count(c) > 1}
        if dup:
            raise AssertionError(f"{path}: {len(dup)} case(s) claimed by more "
                                 f"than one certificate: {sorted(dup)[:3]}")
        stray = [c for c in named if c not in listed]
        if stray:
            raise AssertionError(f"{path}: {len(stray)} case(s) are not in the "
                                 f"independent enumeration: {sorted(stray)[:3]}")
        lines.append(f"  N={N} k={k}: {len(named)} of {len(listed)} cases "
                     f"carry a certificate, all in the enumeration")
    return lines


# --- entry point -------------------------------------------------------------

def self_check(N=4, ks=(2, 3)):
    lines = []
    for k in ks:
        n_a, n_b = len(type_a_cases(N, k)), len(type_b_cases(N, k))
        e_a, e_b = expected_counts(N, k)
        assert (n_a, n_b) == (e_a, e_b), \
            f"N={N} k={k}: enumerated {n_a}+{n_b}, closed form says {e_a}+{e_b}"
        n_pat, n_case, n_ac = check_partition(N, k)
        lines.append(f"  N={N} k={k}: {n_a} type A + {n_b} type B = {n_case} "
                     f"cases; {n_pat} support patterns all land on exactly one "
                     f"({n_ac} all-continue, handled separately)")
    return lines


def main(argv):
    print("independent case enumeration")
    for line in self_check():
        print(line)
    print("against the certifier's own enumeration")
    for line in compare_all_dumps():
        print(line)
    for path in argv[1:]:
        print(f"manifest {os.path.relpath(path)}")
        for line in check_manifest(path):
            print(line)
    print("enumeration check passed")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
