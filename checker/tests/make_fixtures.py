#!/usr/bin/env python3
"""Regenerate the checker's test fixtures.

Two families:

* `good/` — one hand-built, hand-verified certificate per type. The pipeline
  does not export rur / bnb_trace / aps_trace / witness certificates yet, so
  these double as a worked example of each format and as a check that the
  format is actually satisfiable before the exporters get written.
* `bad_certificates/` — one deliberately corrupted file per failure mode,
  together with `expected.json` recording the substring the rejection message
  must contain. A negative test that only asserts "rejected" would pass for
  the wrong reason.
* `bad_manifests/<name>/` — the failure modes a manifest can only have in
  context, because the check reads the certificates it lists. Each directory
  holds a manifest plus the certificates it points at, and only its
  `manifest.json` is expected to be rejected.

Run: python3 make_fixtures.py
"""

import copy
import json
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
GOOD = os.path.join(HERE, "good")
BAD = os.path.join(HERE, "bad_certificates")
BADMAN = os.path.join(HERE, "bad_manifests")
REAL = os.path.join(HERE, "..", "..", "..", "artifacts", "certificates",
                    "gen025", "periodic_k2", "k2_empty_04.json")
REAL_MANIFEST = os.path.join(HERE, "..", "..", "..", "artifacts",
                             "certificates", "gen025", "manifest.json")


def write(path, obj):
    with open(path, "w") as fh:
        json.dump(obj, fh, indent=2)
        fh.write("\n")


def envelope(cid, ctype, claim, data, game="fixture", case=None):
    c = {"format_version": 1, "id": cid, "game": game, "claim": claim,
         "type": ctype, "domain": {"note": "test fixture"}, "data": data}
    if case is not None:
        c["case"] = case
    return c


# --------------------------------------------------------------------------
# good fixtures
# --------------------------------------------------------------------------

# C2. System x1^2 - 2 = 0, x2 - x1 = 0. Two real solutions, x1 = +-sqrt(2);
# both violate x1 - 3 < 0... no: both satisfy x1 - 3 < 0, which is exactly the
# refutation used here (read as "the domain requires x1 - 3 >= 0").
# Parametrization with T = x1: p = T^2 - 2, w = p' = 2T, x_i = 2T^2 / 2T = T.
RUR = envelope(
    "fixture/rur/sqrt2", "rur",
    "the system has exactly two real solutions and both violate x1 - 3 >= 0",
    {
        "vars": ["x1", "x2"],
        "equations": [
            [["1", [2, 0]], ["-2", [0, 0]]],
            [["1", [0, 1]], ["-1", [1, 0]]],
        ],
        "separating_form": [["1", [1, 0]]],
        "elim_poly": [["1", [2]], ["-2", [0]]],
        "elim_derivative_check": True,
        "param_denominator": [["2", [1]]],
        "param_numerators": [[["2", [2]]], [["2", [2]]]],
        "param_cofactors": [[["4", [2]]], []],
        "membership_cofactors": [[["1", [0, 0]]], []],
        "sturm": {
            "sequence": [[["1", [2]], ["-2", [0]]], [["2", [1]]], [["2", [0]]]],
            "count_interval": ["-2", "2"],
            "count": 2,
        },
        "roots": [
            {"interval": ["-2", "-1"],
             "refutation": {"condition": [["1", [1, 0]], ["-3", [0, 0]]],
                            "sense": "<0", "bound_derivation": "interval"}},
            {"interval": ["1", "2"],
             "refutation": {"condition": [["1", [1, 0]], ["-3", [0, 0]]],
                            "sense": "<0", "bound_derivation": "interval"}},
        ],
    })

# C4, split-tree form: x1 + x2 - 3 never vanishes on the unit square.
BNB_TREE = envelope(
    "fixture/bnb/tree", "bnb_trace",
    "no point of the unit square satisfies x1 + x2 - 3 = 0",
    {
        "vars": ["x1", "x2"],
        "conditions": [[["1", [1, 0]], ["1", [0, 1]], ["-3", [0, 0]]]],
        "root_box": [["0", "1"], ["0", "1"]],
        "splits": {"axis": 0, "cut": "1/2",
                   "lo": {"violated": 0, "sense": "<0"},
                   "hi": {"violated": 0, "sense": "<0"}},
    })

# C4, flat form: the same claim with the four quadrants listed explicitly.
BNB_FLAT = envelope(
    "fixture/bnb/flat", "bnb_trace",
    "no point of the unit square satisfies x1 + x2 - 3 = 0",
    {
        "vars": ["x1", "x2"],
        "conditions": [[["1", [1, 0]], ["1", [0, 1]], ["-3", [0, 0]]]],
        "root_box": [["0", "1"], ["0", "1"]],
        "leaves": [
            {"box": [["0", "1/2"], ["0", "1/2"]], "violated": 0, "sense": "<0"},
            {"box": [["1/2", "1"], ["0", "1/2"]], "violated": 0, "sense": "<0"},
            {"box": [["0", "1/2"], ["1/2", "1"]], "violated": 0, "sense": "<0"},
            {"box": [["1/2", "1"], ["1/2", "1"]], "violated": 0, "sense": "<0"},
        ],
    })

# C4 with inequality conditions: `condition_senses` says the conditions are
# read as "<= 0" rather than "= 0", so a leaf may only be closed by proving one
# strictly positive there. The system is x1 <= 1/4 and x1 >= 1/2, infeasible.
BNB_INEQ = envelope(
    "fixture/bnb/inequalities", "bnb_trace",
    "no point of the unit square satisfies both 4*x1 - 1 <= 0 and 1 - 2*x1 <= 0",
    {
        "vars": ["x1", "x2"],
        "conditions": [[["4", [1, 0]], ["-1", [0, 0]]],
                       [["-2", [1, 0]], ["1", [0, 0]]]],
        "condition_senses": ["<=0", "<=0"],
        "root_box": [["0", "1"], ["0", "1"]],
        "splits": {"axis": 0, "cut": "1/3",
                   "lo": {"violated": 1, "sense": ">0"},
                   "hi": {"violated": 0, "sense": ">0"}},
    })

# C5: [0,1] shrinks to [0,1/2] shrinks to the empty set.
APS = envelope(
    "fixture/aps/shrink", "aps_trace",
    "the iteration contracts to the empty set in two steps",
    {
        "iterations": [
            {"polytope_H": [{"normal": ["1"], "offset": "1"},
                            {"normal": ["-1"], "offset": "0"}]},
            {"polytope_H": [{"normal": ["1"], "offset": "1/2"},
                            {"normal": ["-1"], "offset": "0"}],
             "inclusion_cofactors": {"multipliers": [["1", "0"], ["0", "1"]]}},
            {"polytope_H": [{"normal": ["1"], "offset": "-1"},
                            {"normal": ["-1"], "offset": "0"}],
             "inclusion_cofactors": {"multipliers": [["1", "0"], ["0", "1"]]}},
        ],
        "final": "empty",
        "emptiness_witness": {"farkas": ["1", "1"]},
    })

# C6: a point inside the stratified domain satisfying the listed conditions.
WITNESS = envelope(
    "fixture/witness/point", "witness",
    "at the larger deviation level this point is a near-equilibrium",
    {
        "point": {"x1": "13/1000", "x2": "1/2"},
        "conditions": [
            {"poly": [["1", [1, 0]], ["-1/2", [0, 0]]], "sense": "<=0"},
            {"poly": [["1", [0, 1]], ["-1/2", [0, 0]]], "sense": "==0"},
        ],
    })

# C4 with a genuinely quadratic condition: the positive counterpart of the
# c4_quadratic_leaf_not_positive negative fixture. x1^2 - x1 + 1/2 has its
# minimum at 1/4 > 0, so the Bernstein branch of range_on_box may — and must —
# sign the leaf strictly positive. Not expressible with the multilinear
# vertex rule, which only ever sees the looser interval bound.
QUADRATIC = envelope(
    "fixture/bnb/quadratic_leaf_positive", "bnb_trace",
    "no point of [0,1]^2 has x1^2 - x1 + 1/2 <= 0 (its minimum is 1/4 > 0)",
    {"vars": ["x1", "x2"],
     "conditions": [[["1", [2, 0]], ["-1", [1, 0]], ["1/2", [0, 0]]]],
     "condition_senses": ["<=0"],
     "root_box": [["0", "1"], ["0", "1"]],
     "splits": {"violated": 0, "sense": ">0"}})
QUADRATIC["data"]["condition_names"] = ["quadratic_stays_positive"]

GOOD_FIXTURES = {
    "rur_sqrt2.json": RUR,
    "bnb_tree.json": BNB_TREE,
    "bnb_flat.json": BNB_FLAT,
    "bnb_inequalities.json": BNB_INEQ,
    "aps_shrink.json": APS,
    "witness_point.json": WITNESS,
    "c4_quadratic_bernstein.json": QUADRATIC,
}

# A manifest binds a corpus to one game and one code version. It lives in its
# own subdirectory because the checker verifies that *every* certificate under
# a manifest is listed in some case table -- a completeness check that only
# means anything if the directory holds nothing else.
#
# The game is the real gen025 and the certificate the real k2_empty_04: the
# manifest check does not just compare names, it re-derives the certificate's
# polynomial system from the manifest's payoff matrix (see bind_systems.py),
# so a hand-built fake would need a genuine Nullstellensatz identity AND the
# genuine induced system. Using real exported data gives both for free, and
# the suite itself rejects the fixture if they ever drift apart.
def make_manifest(real_manifest, real_cert):
    """The reduced good fixture: one claim, one case-table entry."""
    return {
        "format_version": 1,
        "game": real_manifest["game"],
        "provenance": {"code_commit": "0" * 40, "code_clean": True,
                       "code_paths": ["src"]},
        "claims": [{"statement": "fixture claim",
                    "case_table": [{"case": "only",
                                    "pattern": real_cert["case"],
                                    "certificate":
                                    "periodic_k2/k2_empty_04.json"}]}],
    }


# --------------------------------------------------------------------------
# bad fixtures: one per failure mode
# --------------------------------------------------------------------------

def mutate(base, fn):
    c = copy.deepcopy(base)
    fn(c)
    return c


def build_bad(real, manifest_ok):
    bad, expected = {}, {}

    def add(name, cert, reason):
        bad[name] = cert
        expected[name] = reason

    # -- envelope
    add("envelope_future_version",
        mutate(real, lambda c: c.__setitem__("format_version", 2)),
        "unsupported format_version")
    add("envelope_unknown_type",
        mutate(real, lambda c: c.__setitem__("type", "handwave")),
        "unknown certificate type")
    add("envelope_missing_claim",
        mutate(real, lambda c: c.pop("claim")),
        "missing field 'claim'")
    # An empty case label is worse than an absent one: it looks like the
    # certificate is bound to an enumeration case when it is bound to nothing.
    add("envelope_empty_case",
        mutate(real, lambda c: c.__setitem__("case", "")),
        "case must be a non-empty string")

    # -- C1, against the real gen025 certificate
    def bump_cofactor(c):
        c["data"]["cofactors"][0][0][0] = "-1/755"
    add("c1_cofactor_perturbed", mutate(real, bump_cofactor),
        "identity sum(g_i * f_i) = 1 does not hold")

    def drop_term(c):
        c["data"]["equations"][0].pop()
    add("c1_equation_term_dropped", mutate(real, drop_term),
        "identity sum(g_i * f_i) = 1 does not hold")

    def float_coeff(c):
        c["data"]["equations"][0][0][0] = -754.0
    add("c1_float_coefficient", mutate(real, float_coeff),
        "rationals must be strings")

    def rounded_coeff(c):
        c["data"]["cofactors"][0][0][0] = "-0.00132625994695"
    add("c1_decimal_coefficient", mutate(real, rounded_coeff),
        "not an exact rational")

    def missing_cofactor(c):
        c["data"]["cofactors"].pop()
    add("c1_cofactor_count_mismatch", mutate(real, missing_cofactor),
        "cofactors for")

    # -- C2
    def sturm_count(c):
        c["data"]["sturm"]["count"] = 1
    add("c2_sturm_count_wrong", mutate(RUR, sturm_count),
        "Sturm count over")

    def sturm_chain(c):
        c["data"]["sturm"]["sequence"][2] = [["3", [0]]]
    add("c2_sturm_chain_broken", mutate(RUR, sturm_chain),
        "not the negated remainder")

    def root_not_isolated(c):
        c["data"]["roots"][0]["interval"] = ["-2", "2"]
    add("c2_root_not_isolated", mutate(RUR, root_not_isolated),
        "does not isolate exactly one root")

    def refutation_flipped(c):
        c["data"]["roots"][1]["refutation"]["sense"] = ">0"
    add("c2_refutation_sense_flipped", mutate(RUR, refutation_flipped),
        "is not >0 on the isolating interval")

    def param_cofactor(c):
        c["data"]["param_cofactors"][0] = [["5", [2]]]
    add("c2_param_cofactor_wrong", mutate(RUR, param_cofactor),
        "does not give the stated multiple of elim_poly")

    def membership(c):
        c["data"]["membership_cofactors"][0] = [["2", [0, 0]]]
    add("c2_membership_cofactor_wrong", mutate(RUR, membership),
        "completeness identity")

    def dropped_root(c):
        c["data"]["roots"].pop()
    add("c2_root_dropped", mutate(RUR, dropped_root),
        "root entries for a Sturm count")

    # -- C4
    def leaf_sign(c):
        c["data"]["splits"]["lo"]["sense"] = ">0"
    add("c4_leaf_sign_wrong", mutate(BNB_TREE, leaf_sign),
        "is not provably >0")

    def cut_outside(c):
        c["data"]["splits"]["cut"] = "3/2"
    add("c4_cut_outside_box", mutate(BNB_TREE, cut_outside),
        "lies outside the box")

    def missing_quadrant(c):
        c["data"]["leaves"].pop()
    add("c4_incomplete_cover", mutate(BNB_FLAT, missing_quadrant),
        "does not cover the box")

    def overlapping(c):
        # Same total volume as the root box, but overlapping and leaving
        # [3/4, 1] x [0, 1] uncovered — the case the volume test alone misses.
        c["data"]["leaves"] = [
            {"box": [["0", "1/2"], ["0", "1"]], "violated": 0, "sense": "<0"},
            {"box": [["1/4", "3/4"], ["0", "1"]], "violated": 0, "sense": "<0"},
        ]
    add("c4_overlapping_leaves", mutate(BNB_FLAT, overlapping),
        "overlap")

    # The failure mode the condition-sense extension exists to catch, and the
    # only one here that the *legacy* reading would have accepted: x1 - 2 is
    # indeed strictly negative on the unit interval, which excludes a zero but
    # leaves the inequality x1 - 2 <= 0 satisfied everywhere. The claim is
    # false, and the arithmetic on the leaf is nonetheless correct.
    add("c4_inequality_refuted_by_wrong_sign",
        envelope("fixture/bnb/inequality_wrong_sign", "bnb_trace",
                 "no point of [0,1] satisfies x1 - 2 <= 0",
                 {"vars": ["x1"],
                  "conditions": [[["1", [1]], ["-2", [0]]]],
                  "condition_senses": ["<=0"],
                  "root_box": [["0", "1"]],
                  "splits": {"violated": 0, "sense": "<0"}}),
        "only violate by being strictly positive")

    def senses_short(c):
        c["data"]["condition_senses"] = ["<=0"]
    add("c4_condition_senses_length", mutate(BNB_INEQ, senses_short),
        "condition_senses: expected 2 entries")

    def senses_unknown(c):
        c["data"]["condition_senses"] = ["<0", "<=0"]
    add("c4_condition_sense_unknown", mutate(BNB_INEQ, senses_unknown),
        "unknown condition sense")

    # The negative test for the Bernstein branch of range_on_box: the
    # enclosure is only ever used to ACCEPT a leaf, so a bug in it buys false
    # certificates, and unlike the multilinear vertex rule it is not exact.
    # x1^2 - x1 + 1/8 dips to -1/8 at x1 = 1/2, so no sound enclosure may
    # sign it strictly positive on the unit box.
    quad = envelope(
        "fixture/bnb/quadratic_leaf_not_positive", "bnb_trace",
        "FALSE ON PURPOSE. Claims no point of [0,1]^2 has x1^2 - x1 + 1/8 "
        "<= 0, on a single leaf. The condition is genuinely negative on part "
        "of that box (its minimum is 1/8 - 1/4 = -1/8 at x1 = 1/2), so no "
        "sound enclosure may sign it positive there. This is the negative "
        "test for the Bernstein branch of range_on_box: the enclosure is "
        "only ever used to ACCEPT a leaf, so a bug in it buys false "
        "certificates, and unlike the multilinear vertex rule it is not "
        "exact.",
        {"vars": ["x1", "x2"],
         "conditions": [[["1", [2, 0]], ["-1", [1, 0]], ["1/8", [0, 0]]]],
         "condition_senses": ["<=0"],
         "root_box": [["0", "1"], ["0", "1"]],
         "splits": {"violated": 0, "sense": ">0"}})
    quad["data"]["condition_names"] = ["quadratic_dips_below_zero"]
    add("c4_quadratic_leaf_not_positive", quad, "is not provably >0")

    # -- C5
    def negative_multiplier(c):
        c["data"]["iterations"][1]["inclusion_cofactors"]["multipliers"][0] = \
            ["2", "-1"]
    add("c5_negative_multiplier", mutate(APS, negative_multiplier),
        "negative Farkas multiplier")

    def trivial_witness(c):
        # Cancels the normals, but proves nothing: 0 <= 0 is not a contradiction.
        c["data"]["emptiness_witness"]["farkas"] = ["0", "0"]
    add("c5_emptiness_not_proved", mutate(APS, trivial_witness),
        "is not negative")

    def offset_too_large(c):
        c["data"]["iterations"][2]["polytope_H"][0]["offset"] = "1"
    add("c5_inclusion_offset_too_large", mutate(APS, offset_too_large),
        "inclusion not proved")

    def broken_inclusion(c):
        c["data"]["iterations"][1]["inclusion_cofactors"]["multipliers"][0] = \
            ["0", "1"]
    add("c5_inclusion_not_proved", mutate(APS, broken_inclusion),
        "do not reproduce the normal")

    # -- C6
    def point_outside(c):
        c["data"]["point"]["x1"] = "3/4"
    add("c6_condition_violated", mutate(WITNESS, point_outside),
        "fails at the point")

    # -- manifest. Each of these must fail *before* the completeness sweep,
    # which would otherwise fire first: bad_certificates/ is full of files a
    # manifest sitting there does not list.
    def bad_shape(c):
        c["game"]["payoffs"] = c["game"]["payoffs"][:-1]
    add("manifest_payoff_shape_wrong", mutate(manifest_ok, bad_shape),
        "payoff matrix must have 2^N-1")

    def float_payoff(c):
        c["game"]["payoffs"][0][0] = 1.0
    add("manifest_float_payoff", mutate(manifest_ok, float_payoff),
        "rationals must be strings")

    def dirty(c):
        c["provenance"]["code_clean"] = False
    add("manifest_dirty_tree", mutate(manifest_ok, dirty),
        "dirty working tree")

    def short_commit(c):
        c["provenance"]["code_commit"] = "1262c36"
    add("manifest_short_commit", mutate(manifest_ok, short_commit),
        "must be a full git hash")

    def missing_cert(c):
        c["claims"][0]["case_table"][0]["certificate"] = "systems/nope.json"
    add("manifest_certificate_missing", mutate(manifest_ok, missing_cert),
        "references a missing certificate")

    return bad, expected


def build_bad_manifests(manifest_ok, manifest_cert):
    """Manifest failures that only exist in context.

    The case-table/certificate binding cannot be corrupted in a standalone
    file: the checker reads the certificates the manifest lists, so the
    fixture has to be a directory holding both. Each entry is
    (manifest, certificate, expected rejection substring).
    """
    dirs = {}

    def wrong_pattern(c):
        c["claims"][0]["case_table"][0]["pattern"] = "B q{2}m{3,4}"
    dirs["manifest_pattern_mismatch"] = (
        mutate(manifest_ok, wrong_pattern), manifest_cert,
        "the certificate says")

    def drop_pattern(c):
        del c["claims"][0]["case_table"][0]["pattern"]
    dirs["manifest_pattern_unlisted"] = (
        mutate(manifest_ok, drop_pattern), manifest_cert,
        "carries no pattern")

    # The failure mode the payoff matrix in the manifest exists for: every
    # string says gen025, the Nullstellensatz identity is valid, and the
    # system is nevertheless about another game. payoffs[0][0] is measured to
    # occur in this certificate's induced system (see bind_systems.py).
    def wrong_game(c):
        c["game"]["payoffs"][0][0] = str(Fraction(c["game"]["payoffs"][0][0])
                                         + 1)
    dirs["manifest_system_wrong_game"] = (
        mutate(manifest_ok, wrong_game), manifest_cert,
        "the equations are not the system the payoff matrix induces")

    return dirs


def main():
    os.makedirs(GOOD, exist_ok=True)
    os.makedirs(BAD, exist_ok=True)
    with open(REAL) as fh:
        real = json.load(fh)
    with open(REAL_MANIFEST) as fh:
        real_manifest = json.load(fh)
    manifest_ok = make_manifest(real_manifest, real)

    for name, cert in GOOD_FIXTURES.items():
        write(os.path.join(GOOD, name), cert)
    mdir = os.path.join(GOOD, "manifest")
    os.makedirs(os.path.join(mdir, "periodic_k2"), exist_ok=True)
    write(os.path.join(mdir, "manifest.json"), manifest_ok)
    write(os.path.join(mdir, "periodic_k2", "k2_empty_04.json"), real)
    bad, expected = build_bad(real, manifest_ok)
    for name, cert in bad.items():
        write(os.path.join(BAD, name + ".json"), cert)
    badman = build_bad_manifests(manifest_ok, real)
    for name, (manifest, cert, reason) in badman.items():
        d = os.path.join(BADMAN, name)
        os.makedirs(os.path.join(d, "periodic_k2"), exist_ok=True)
        write(os.path.join(d, "manifest.json"), manifest)
        write(os.path.join(d, "periodic_k2", "k2_empty_04.json"), cert)
        expected[name] = reason
    # Outside bad_certificates/, so that directory contains only certificates.
    write(os.path.join(HERE, "expected_rejections.json"), expected)
    print(f"wrote {len(GOOD_FIXTURES)} good, {len(bad)} bad and "
          f"{len(badman)} bad-manifest fixtures")


if __name__ == "__main__":
    main()
