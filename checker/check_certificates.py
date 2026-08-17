#!/usr/bin/env python3
"""Independent checker for the certificates described in docs/certificates.md.

Deliberately shares nothing with the Julia pipeline: standard library only,
exact arithmetic only (fractions.Fraction), no solving and no search. Every
check is decision-free arithmetic — evaluate, expand, compare.

    python3 check_certificates.py <file-or-directory> ...
    python3 check_certificates.py --expect-fail <file> ...   # negative tests

Exit status is 0 when every certificate reached the expected verdict.

Scope note, stated up front because a checker that overstates itself is worse
than none: for `aps_trace` this verifies the polyhedral bookkeeping (each
declared inclusion, and final emptiness, by exact Farkas witnesses) but NOT
that the listed polytope really contains the APS image of its predecessor —
the format carries no witness for that step yet. See README.md.
"""

import argparse
import json
import math
import os
import re
import sys
from fractions import Fraction

SUPPORTED_FORMAT_VERSION = 1
KNOWN_TYPES = ("nullstellensatz", "rur", "bnb_trace", "aps_trace", "witness")

# Multilinear polynomials attain their exact range on a box at the vertices;
# below this many variables we use that instead of the looser interval
# extension, matching what the pipeline does when it builds the traces.
MAX_VERTEX_VARS = 12
# Interval evaluation is subdivided this many times before giving up on
# deciding a sign. Sound either way: subdividing only ever sharpens.
MAX_SUBDIVISION_DEPTH = 40
# A Bernstein enclosure costs prod_j (m_j + 1) coefficients. Past this many the
# checker falls back to the interval extension rather than spend unbounded time
# on a condition of high multidegree; skipping it can only cost a rejection,
# never buy an acceptance.
BERNSTEIN_MAX_COEFFS = 20000


class Bad(Exception):
    """A certificate failed to check. The message is the reason."""


# --------------------------------------------------------------------------
# exact scalars
# --------------------------------------------------------------------------

RATIONAL_RE = re.compile(r"^-?\d+(/\d+)?$")


def Q(x, what="value"):
    """Parse an exact rational. Strings only — a float here is a format error."""
    if isinstance(x, bool) or not isinstance(x, str):
        raise Bad(f"{what}: rationals must be strings like \"3/4\", got "
                  f"{type(x).__name__} {x!r}")
    if not RATIONAL_RE.match(x):
        raise Bad(f"{what}: not an exact rational: {x!r}")
    try:
        return Fraction(x)
    except ZeroDivisionError:
        raise Bad(f"{what}: zero denominator in {x!r}")


def sign(x):
    return (x > 0) - (x < 0)


# --------------------------------------------------------------------------
# multivariate polynomials: dict from exponent tuple to Fraction
# --------------------------------------------------------------------------

def parse_poly(terms, nvars, what):
    if not isinstance(terms, list):
        raise Bad(f"{what}: expected a list of terms")
    p = {}
    for t in terms:
        if not (isinstance(t, list) and len(t) == 2):
            raise Bad(f"{what}: a term must be [coefficient, exponents]")
        coeff, exps = t
        c = Q(coeff, f"{what} coefficient")
        if not isinstance(exps, list) or len(exps) != nvars:
            raise Bad(f"{what}: exponent vector must have {nvars} entries, "
                      f"got {exps!r}")
        e = []
        for v in exps:
            if isinstance(v, bool) or not isinstance(v, int) or v < 0:
                raise Bad(f"{what}: exponents must be non-negative integers, "
                          f"got {v!r}")
            e.append(v)
        e = tuple(e)
        p[e] = p.get(e, Fraction(0)) + c
    return {e: c for e, c in p.items() if c != 0}


def padd(a, b):
    r = dict(a)
    for e, c in b.items():
        n = r.get(e, Fraction(0)) + c
        if n == 0:
            r.pop(e, None)
        else:
            r[e] = n
    return r


def psub(a, b):
    return padd(a, {e: -c for e, c in b.items()})


def pmul(a, b):
    r = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            n = r.get(e, Fraction(0)) + ca * cb
            if n == 0:
                r.pop(e, None)
            else:
                r[e] = n
    return r


def pconst(c, nvars):
    return {} if c == 0 else {(0,) * nvars: Fraction(c)}


def peval(p, point):
    total = Fraction(0)
    for e, c in p.items():
        term = c
        for xi, ei in zip(point, e):
            if ei:
                term *= xi ** ei
        total += term
    return total


def total_degree(p):
    return max((sum(e) for e in p), default=0)


# --------------------------------------------------------------------------
# univariate polynomials: list of Fractions, index = degree
# --------------------------------------------------------------------------

def to_univariate(p, nvars, what):
    """Collapse a 1-variable multivariate polynomial to a coefficient list."""
    if nvars != 1:
        raise Bad(f"{what}: expected a univariate polynomial")
    if not p:
        return []
    deg = max(e[0] for e in p)
    coeffs = [Fraction(0)] * (deg + 1)
    for e, c in p.items():
        coeffs[e[0]] = c
    return coeffs


def parse_univariate(terms, what):
    return to_univariate(parse_poly(terms, 1, what), 1, what)


def utrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def uadd(a, b):
    n = max(len(a), len(b))
    r = [Fraction(0)] * n
    for i, c in enumerate(a):
        r[i] += c
    for i, c in enumerate(b):
        r[i] += c
    return utrim(r)


def usub(a, b):
    return uadd(a, [-c for c in b])


def umul(a, b):
    if not a or not b:
        return []
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0:
            continue
        for j, cb in enumerate(b):
            r[i + j] += ca * cb
    return utrim(r)


def uderiv(a):
    return utrim([a[i] * i for i in range(1, len(a))])


def urem(a, b):
    """Remainder of a divided by b, exact over the rationals."""
    b = utrim(b)
    if not b:
        raise Bad("division by the zero polynomial")
    r = utrim(a)
    while r and len(r) >= len(b):
        shift = len(r) - len(b)
        factor = r[-1] / b[-1]
        for i, cb in enumerate(b):
            r[i + shift] -= factor * cb
        r = utrim(r)
    return r


def ugcd(a, b):
    a, b = utrim(a), utrim(b)
    while b:
        a, b = b, urem(a, b)
    return a


def ueval(a, x):
    acc = Fraction(0)
    for c in reversed(a):
        acc = acc * x + c
    return acc


# --------------------------------------------------------------------------
# interval arithmetic (exact rational endpoints, outward by construction)
# --------------------------------------------------------------------------

class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        if lo > hi:
            raise Bad(f"empty interval [{lo}, {hi}]")
        self.lo, self.hi = lo, hi

    def __add__(self, o):
        return Iv(self.lo + o.lo, self.hi + o.hi)

    def __mul__(self, o):
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Iv(min(p), max(p))

    def pow(self, k):
        r = Iv(Fraction(1), Fraction(1))
        for _ in range(k):
            r = r * self
        return r

    def strict_sign(self):
        """+1 if the whole interval is > 0, -1 if < 0, 0 if it may contain 0."""
        if self.lo > 0:
            return 1
        if self.hi < 0:
            return -1
        return 0


def iv_eval_poly(p, box):
    """Natural interval extension of a multivariate polynomial over a box."""
    acc = Iv(Fraction(0), Fraction(0))
    for e, c in p.items():
        term = Iv(c, c)
        for i, ei in enumerate(e):
            if ei:
                term = term * box[i].pow(ei)
        acc = acc + term
    return acc


def is_multilinear(p):
    return all(all(ei <= 1 for ei in e) for e in p)


def bernstein_range(p, box):
    """Bernstein enclosure of p over the box, or None when it does not apply.

    For p of per-variable degree m, writing u_j = x_j - lo_j, v_j = hi_j - x_j
    and w_j = hi_j - lo_j,

        prod_j w_j^m_j * p(x)
            = sum_k b_k * prod_j C(m_j,k_j) * u_j^k_j * v_j^(m_j-k_j)

    identically, so [min b, max b] contains the range of p on the box: every
    coefficient in the sum is nonnegative there and they add up to
    prod_j w_j^m_j. It is the range exactly when m is all ones (the b_k are then
    the corner values), and an enclosure that tightens quadratically under
    subdivision otherwise.

    Why the checker needs it. Interval extension of a genuinely quadratic
    condition carries an error linear in the box width, and the directional
    margin (gap G1) is certified at a delta so close to the true minimum that
    at the minimiser the condition is positive by about 4e-9 -- signing that by
    interval extension needs some 2^48 subdivisions, which is why the depth cap
    below used to reject a true leaf. Bernstein signs it on the leaf as given.
    This is the same rule the exported trace and the Lean replay use, and it is
    implemented here independently, from the identity above.

    Returns None when a coordinate p depends on is degenerate on the box (the
    identity divides by the widths) or when the coefficient array would be
    larger than BERNSTEIN_MAX_COEFFS.
    """
    n = len(box)
    m = [0] * n
    for e in p:
        for i, ei in enumerate(e):
            if ei > m[i]:
                m[i] = ei
    total = 1
    for mi in m:
        total *= mi + 1
    if total > BERNSTEIN_MAX_COEFFS:
        return None
    w = [b.hi - b.lo for b in box]
    for i in range(n):
        if m[i] and w[i] == 0:
            return None

    # coefficients of q(s) = p(lo + w*s) in the power basis, dense over m
    def index(k):
        idx = 0
        for i in range(n):
            idx = idx * (m[i] + 1) + k[i]
        return idx

    c = [Fraction(0)] * total
    for e, coeff in p.items():
        acc = {(0,) * n: Fraction(coeff)}
        for i in range(n):
            if not e[i]:
                continue
            nxt = {}
            for k, v in acc.items():
                for t in range(e[i] + 1):
                    f = (Fraction(math.comb(e[i], t)) * box[i].lo ** (e[i] - t)
                         * w[i] ** t)
                    if f == 0:
                        continue
                    k2 = k[:i] + (t,) + k[i + 1:]
                    nxt[k2] = nxt.get(k2, Fraction(0)) + v * f
            acc = nxt
        for k, v in acc.items():
            c[index(k)] += v

    # power basis -> Bernstein basis, one axis at a time:
    #   b_k = sum_{i<=k} C(k,i)/C(m,i) * c_i   (univariate, degree m)
    stride = [1] * n
    for i in range(n - 2, -1, -1):
        stride[i] = stride[i + 1] * (m[i + 1] + 1)
    for i in range(n):
        mi = m[i]
        if mi == 0:
            continue
        st = stride[i]
        for base in range(total):
            if (base // st) % (mi + 1):
                continue                      # only the k_i = 0 slot starts a run
            col = [c[base + t * st] for t in range(mi + 1)]
            for k in range(mi + 1):
                acc = Fraction(0)
                for j in range(k + 1):
                    acc += (Fraction(math.comb(k, j), math.comb(mi, j))
                            * col[j])
                c[base + k * st] = acc
    return Iv(min(c), max(c))


def range_on_box(p, box):
    """Range enclosure of p over the box. Exact for multilinear p in few
    variables (vertices attain the range); otherwise the natural interval
    extension intersected with the Bernstein enclosure, both of which are
    supersets of the range, so their intersection is one too."""
    nvars = len(box)
    if is_multilinear(p) and nvars <= MAX_VERTEX_VARS:
        active = sorted({i for e in p for i, ei in enumerate(e) if ei})
        lo = hi = None
        for mask in range(1 << len(active)):
            point = [b.lo for b in box]
            for bit, i in enumerate(active):
                if mask >> bit & 1:
                    point[i] = box[i].hi
            v = peval(p, point)
            lo = v if lo is None else min(lo, v)
            hi = v if hi is None else max(hi, v)
        if lo is None:
            return Iv(Fraction(0), Fraction(0))
        return Iv(lo, hi)
    iv = iv_eval_poly(p, box)
    bz = bernstein_range(p, box)
    if bz is None:
        return iv
    return Iv(max(iv.lo, bz.lo), min(iv.hi, bz.hi))


def prove_sign_on_box(p, box, want, depth=0):
    """Prove p has strictly the sign `want` (+1/-1) everywhere on the box,
    subdividing when the enclosure is inconclusive."""
    s = range_on_box(p, box).strict_sign()
    if s == want:
        return True
    if s != 0:
        return False                       # provably the opposite sign
    if depth >= MAX_SUBDIVISION_DEPTH:
        return False
    widest = max(range(len(box)), key=lambda i: box[i].hi - box[i].lo)
    if box[widest].hi == box[widest].lo:
        return False                       # degenerate: nothing left to split
    mid = (box[widest].lo + box[widest].hi) / 2
    for lo, hi in ((box[widest].lo, mid), (mid, box[widest].hi)):
        half = list(box)
        half[widest] = Iv(lo, hi)
        if not prove_sign_on_box(p, half, want, depth + 1):
            return False
    return True


def parse_sense(s, what):
    if s not in ("<0", ">0", "<=0", ">=0", "==0"):
        raise Bad(f"{what}: unknown sense {s!r}")
    return s


def sense_holds(value, s):
    return {"<0": value < 0, ">0": value > 0, "<=0": value <= 0,
            ">=0": value >= 0, "==0": value == 0}[s]


# --------------------------------------------------------------------------
# type checkers
# --------------------------------------------------------------------------

def need(d, key, what):
    if key not in d:
        raise Bad(f"{what}: missing field {key!r}")
    return d[key]


def get_vars(data):
    vs = need(data, "vars", "data")
    if not isinstance(vs, list) or not all(isinstance(v, str) for v in vs):
        raise Bad("data.vars: expected a list of variable names")
    if len(set(vs)) != len(vs):
        raise Bad("data.vars: duplicate variable name")
    return vs


def check_nullstellensatz(cert):
    """1 = sum(g_i f_i) proves the system has no solution over any extension."""
    data = need(cert, "data", "certificate")
    vs = get_vars(data)
    n = len(vs)
    eqs = [parse_poly(t, n, f"equation {i}")
           for i, t in enumerate(need(data, "equations", "data"))]
    cof = [parse_poly(t, n, f"cofactor {i}")
           for i, t in enumerate(need(data, "cofactors", "data"))]
    if len(cof) != len(eqs):
        raise Bad(f"{len(cof)} cofactors for {len(eqs)} equations")
    if not eqs:
        raise Bad("no equations: nothing is being refuted")
    acc = {}
    for g, f in zip(cof, eqs):
        acc = padd(acc, pmul(g, f))
    if acc != pconst(1, n):
        raise Bad("the identity sum(g_i * f_i) = 1 does not hold")
    return f"Nullstellensatz identity verified ({len(eqs)} equations, {n} variables)"


def check_witness(cert):
    """A point that satisfies the listed near-equilibrium conditions."""
    data = need(cert, "data", "certificate")
    point = need(data, "point", "data")
    if not isinstance(point, dict) or not point:
        raise Bad("data.point: expected a non-empty object")
    names = sorted(point)
    values = [Q(point[k], f"point[{k}]") for k in names]
    idx = {v: i for i, v in enumerate(names)}
    conds = need(data, "conditions", "data")
    if not conds:
        raise Bad("no conditions: the witness claims nothing")
    for i, c in enumerate(conds):
        vs = c.get("vars", names)
        if list(vs) != names:
            missing = [v for v in vs if v not in idx]
            if missing:
                raise Bad(f"condition {i}: variables {missing} absent from the point")
        poly = parse_poly(need(c, "poly", f"condition {i}"), len(vs),
                          f"condition {i} poly")
        s = parse_sense(need(c, "sense", f"condition {i}"), f"condition {i}")
        value = peval(poly, [values[idx[v]] for v in vs])
        if not sense_holds(value, s):
            raise Bad(f"condition {i} fails at the point: value {value} is not {s}")
    return f"witness point satisfies all {len(conds)} conditions"


def bnb_condition_senses(data, ncond):
    """How each condition of a bnb_trace is to be read.

    Legacy and default is "=0": the certificate refutes a system of equations,
    and a leaf is excluded by pinning the condition to either strict sign.
    "<=0" says the condition is an inequality the refuted point would have to
    satisfy, and then only strict POSITIVITY excludes a leaf — a condition
    proved strictly negative there is satisfied, not violated. Getting that
    backwards would accept a trace that proves the opposite of its claim, so
    the two are kept apart here rather than in the leaf.
    """
    raw = data.get("condition_senses")
    if raw is None:
        return ["=0"] * ncond
    if not isinstance(raw, list) or len(raw) != ncond:
        got = len(raw) if isinstance(raw, list) else type(raw).__name__
        raise Bad(f"data.condition_senses: expected {ncond} entries, got {got}")
    for s in raw:
        if s not in ("=0", "<=0"):
            raise Bad(f"data.condition_senses: unknown condition sense {s!r} "
                      f"(expected \"=0\" or \"<=0\")")
    return list(raw)


def check_bnb_trace(cert):
    """A box subdivision in which every leaf kills one of the conditions."""
    data = need(cert, "data", "certificate")
    vs = get_vars(data)
    n = len(vs)
    conds = [parse_poly(t, n, f"condition {i}")
             for i, t in enumerate(need(data, "conditions", "data"))]
    if not conds:
        raise Bad("no conditions: nothing to violate")
    senses = bnb_condition_senses(data, len(conds))
    root_spec = need(data, "root_box", "data")
    if len(root_spec) != n:
        raise Bad(f"root_box has {len(root_spec)} intervals for {n} variables")
    root = [Iv(Q(lo, "root_box lower"), Q(hi, "root_box upper"))
            for lo, hi in root_spec]

    leaves = []

    def check_leaf(leaf, box, path):
        k = need(leaf, "violated", f"leaf {path}")
        if not isinstance(k, int) or isinstance(k, bool) or not 0 <= k < len(conds):
            raise Bad(f"leaf {path}: violated index {k!r} out of range")
        s = parse_sense(need(leaf, "sense", f"leaf {path}"), f"leaf {path}")
        if s not in ("<0", ">0"):
            raise Bad(f"leaf {path}: sense must be strict (<0 or >0) to exclude "
                      f"a zero, got {s}")
        if senses[k] == "<=0" and s != ">0":
            raise Bad(f"leaf {path}: condition {k} is declared \"<=0\", which a "
                      f"leaf can only violate by being strictly positive there; "
                      f"sense {s} would leave the condition satisfied")
        want = 1 if s == ">0" else -1
        if not prove_sign_on_box(conds[k], box, want):
            raise Bad(f"leaf {path}: condition {k} is not provably {s} on "
                      f"[{', '.join(f'{b.lo}..{b.hi}' for b in box)}]")
        leaves.append(box)

    def walk(node, box, path):
        if "violated" in node:
            check_leaf(node, box, path)
            return
        axis = need(node, "axis", f"node {path}")
        if not isinstance(axis, int) or isinstance(axis, bool) or not 0 <= axis < n:
            raise Bad(f"node {path}: axis {axis!r} out of range")
        cut = Q(need(node, "cut", f"node {path}"), f"node {path} cut")
        if not box[axis].lo <= cut <= box[axis].hi:
            raise Bad(f"node {path}: cut {cut} lies outside the box on axis {axis}")
        for side, (lo, hi) in (("lo", (box[axis].lo, cut)), ("hi", (cut, box[axis].hi))):
            child = need(node, side, f"node {path}")
            half = list(box)
            half[axis] = Iv(lo, hi)
            walk(child, half, path + "/" + side)

    if "splits" in data:
        # Coverage is automatic: bisections of a closed box into two closed
        # halves cover it, so walking the tree is a complete argument.
        sys.setrecursionlimit(10000)
        walk(data["splits"], root, "")
        how = "split tree"
    elif "leaves" in data:
        # Flat form: verify coverage explicitly. Closed leaves inside the root
        # with pairwise disjoint interiors and volumes summing to the root's
        # volume must cover it (the uncovered part would be relatively open
        # and of measure zero, hence empty).
        flat = need(data, "leaves", "data")
        for i, leaf in enumerate(flat):
            spec = need(leaf, "box", f"leaf {i}")
            if len(spec) != n:
                raise Bad(f"leaf {i}: box has {len(spec)} intervals for {n} variables")
            box = [Iv(Q(lo, "leaf lower"), Q(hi, "leaf upper")) for lo, hi in spec]
            for j, (b, r) in enumerate(zip(box, root)):
                if b.lo < r.lo or b.hi > r.hi:
                    raise Bad(f"leaf {i}: box escapes the root box on axis {j}")
            check_leaf(leaf, box, str(i))
        root_volume = Fraction(1)
        for b in root:
            root_volume *= b.hi - b.lo
        if root_volume == 0:
            raise Bad("root box is degenerate; the flat form cannot be verified "
                      "by volume — use the split-tree form")
        if len(leaves) > 2000:
            raise Bad(f"{len(leaves)} leaves in flat form: pairwise disjointness "
                      f"is quadratic — export a split tree instead")
        total = Fraction(0)
        for b in leaves:
            v = Fraction(1)
            for iv in b:
                v *= iv.hi - iv.lo
            total += v
        for i in range(len(leaves)):
            for j in range(i + 1, len(leaves)):
                if all(min(a.hi, b.hi) > max(a.lo, b.lo)
                       for a, b in zip(leaves[i], leaves[j])):
                    raise Bad(f"leaves {i} and {j} overlap; the volume argument "
                              f"for coverage does not apply")
        if total != root_volume:
            raise Bad(f"leaf volumes sum to {total}, root box volume is "
                      f"{root_volume}: the subdivision does not cover the box")
        how = "flat leaves + volume coverage"
    else:
        raise Bad("data must contain either 'splits' (tree) or 'leaves' (flat)")
    kinds = "".join(sorted(set(senses)))
    return (f"{len(leaves)} leaves, each excluding a condition ({how}; "
            f"conditions read as {kinds})")


def check_aps_trace(cert):
    """Polyhedral bookkeeping: declared inclusions and final emptiness."""
    data = need(cert, "data", "certificate")
    iters = need(data, "iterations", "data")
    if not iters:
        raise Bad("no iterations")

    def rows_of(it, what):
        H = need(it, "polytope_H", what)
        rows = []
        for i, r in enumerate(H):
            normal = [Q(x, f"{what} row {i} normal") for x in need(r, "normal", what)]
            offset = Q(need(r, "offset", what), f"{what} row {i} offset")
            rows.append((normal, offset))
        if not rows:
            raise Bad(f"{what}: empty H-representation")
        widths = {len(nrm) for nrm, _ in rows}
        if len(widths) != 1:
            raise Bad(f"{what}: rows have differing dimensions {sorted(widths)}")
        return rows

    polys = [rows_of(it, f"iteration {k}") for k, it in enumerate(iters)]
    dim = len(polys[0][0][0])
    for k, rows in enumerate(polys):
        if len(rows[0][0]) != dim:
            raise Bad(f"iteration {k}: dimension {len(rows[0][0])} != {dim}")

    # Each step must certify that it is contained in its predecessor: for every
    # row (c, d) of the outer polytope, nonnegative multipliers over the inner
    # polytope's rows with sum(lam_i * n_i) = c and sum(lam_i * b_i) <= d.
    for k in range(1, len(polys)):
        inner, outer = polys[k], polys[k - 1]
        lams = need(iters[k], "inclusion_cofactors", f"iteration {k}")
        mult = need(lams, "multipliers", f"iteration {k} inclusion_cofactors")
        if len(mult) != len(outer):
            raise Bad(f"iteration {k}: {len(mult)} multiplier rows for "
                      f"{len(outer)} rows of the previous polytope")
        for r, (c, d) in enumerate(outer):
            lam = [Q(x, f"iteration {k} multiplier {r}") for x in mult[r]]
            if len(lam) != len(inner):
                raise Bad(f"iteration {k}, row {r}: {len(lam)} multipliers for "
                          f"{len(inner)} rows")
            if any(l < 0 for l in lam):
                raise Bad(f"iteration {k}, row {r}: negative Farkas multiplier")
            combo = [sum((l * nrm[j] for l, (nrm, _) in zip(lam, inner)),
                         Fraction(0)) for j in range(dim)]
            if combo != c:
                raise Bad(f"iteration {k}, row {r}: multipliers do not reproduce "
                          f"the normal (got {combo}, want {c})")
            rhs = sum((l * b for l, (_, b) in zip(lam, inner)), Fraction(0))
            if rhs > d:
                raise Bad(f"iteration {k}, row {r}: offset {rhs} exceeds {d}, "
                          f"inclusion not proved")

    if need(data, "final", "data") != "empty":
        raise Bad("data.final: this checker only certifies traces ending empty")
    fw = need(data, "emptiness_witness", "data")
    lam = [Q(x, "emptiness multiplier") for x in need(fw, "farkas", "emptiness_witness")]
    last = polys[-1]
    if len(lam) != len(last):
        raise Bad(f"emptiness witness has {len(lam)} multipliers for "
                  f"{len(last)} rows")
    if any(l < 0 for l in lam):
        raise Bad("emptiness witness: negative Farkas multiplier")
    combo = [sum((l * nrm[j] for l, (nrm, _) in zip(lam, last)), Fraction(0))
             for j in range(dim)]
    if any(x != 0 for x in combo):
        raise Bad(f"emptiness witness: multipliers must cancel the normals, "
                  f"got {combo}")
    rhs = sum((l * b for l, (_, b) in zip(lam, last)), Fraction(0))
    if rhs >= 0:
        raise Bad(f"emptiness witness: combined offset {rhs} is not negative, "
                  f"so infeasibility is not proved")
    return (f"{len(polys)} polytopes, inclusions and final emptiness certified "
            f"(operator step not covered by the format)")


def check_rur(cert):
    """All real solutions are enumerated by a rational univariate
    representation, and every one of them violates a stated condition."""
    data = need(cert, "data", "certificate")
    vs = get_vars(data)
    n = len(vs)
    eqs = [parse_poly(t, n, f"equation {i}")
           for i, t in enumerate(need(data, "equations", "data"))]
    if not eqs:
        raise Bad("no equations")
    p = parse_univariate(need(data, "elim_poly", "data"), "elim_poly")
    p = utrim(p)
    if len(p) < 2:
        raise Bad("elim_poly must be non-constant")
    w = parse_univariate(need(data, "param_denominator", "data"), "param_denominator")
    nums = [parse_univariate(t, f"param_numerator {i}")
            for i, t in enumerate(need(data, "param_numerators", "data"))]
    if len(nums) != n:
        raise Bad(f"{len(nums)} parametrization numerators for {n} variables")
    if data.get("elim_derivative_check"):
        if utrim(w) != uderiv(p):
            raise Bad("elim_derivative_check is set but param_denominator is not "
                      "the derivative of elim_poly")

    # (1) parametrization soundness: each equation vanishes on the
    #     parametrization modulo p, with the given quotient as witness.
    quots = [parse_univariate(t, f"param_cofactor {i}")
             for i, t in enumerate(need(data, "param_cofactors", "data"))]
    if len(quots) != len(eqs):
        raise Bad(f"{len(quots)} param_cofactors for {len(eqs)} equations")
    for j, f in enumerate(eqs):
        d = total_degree(f)
        acc = []
        for e, c in f.items():
            term = [c]
            for i, ei in enumerate(e):
                for _ in range(ei):
                    term = umul(term, nums[i])
            for _ in range(d - sum(e)):
                term = umul(term, w)
            acc = uadd(acc, term)
        if utrim(acc) != utrim(umul(quots[j], p)):
            raise Bad(f"equation {j}: substituting the parametrization does not "
                      f"give the stated multiple of elim_poly")

    # (2) completeness: p(l(x)) lies in the ideal, so every solution of the
    #     system maps to a root of p; and w does not vanish at those roots.
    ell = parse_poly(need(data, "separating_form", "data"), n, "separating_form")
    if total_degree(ell) > 1:
        raise Bad("separating_form must be linear")
    hs = [parse_poly(t, n, f"membership_cofactor {i}")
          for i, t in enumerate(need(data, "membership_cofactors", "data"))]
    if len(hs) != len(eqs):
        raise Bad(f"{len(hs)} membership_cofactors for {len(eqs)} equations")
    composed = {}
    power = pconst(1, n)
    for c in p:
        composed = padd(composed, pmul(pconst(c, n), power) if c else {})
        power = pmul(power, ell)
    acc = {}
    for h, f in zip(hs, eqs):
        acc = padd(acc, pmul(h, f))
    if composed != acc:
        raise Bad("completeness identity p(l(x)) = sum(h_j * f_j) does not hold")
    g = ugcd(p, w)
    if len(utrim(g)) != 1:
        raise Bad("param_denominator shares a root with elim_poly: the "
                  "parametrization is undefined at some solution")

    # (3) real-root count via a Sturm chain over the counting interval.
    seq = [utrim(parse_univariate(t, f"sturm[{i}]"))
           for i, t in enumerate(need(need(data, "sturm", "data"), "sequence",
                                      "sturm"))]
    if len(seq) < 2 or seq[0] != p or seq[1] != uderiv(p):
        raise Bad("sturm.sequence must start with elim_poly and its derivative")
    for i in range(2, len(seq)):
        if seq[i] != [-c for c in urem(seq[i - 2], seq[i - 1])]:
            raise Bad(f"sturm.sequence[{i}] is not the negated remainder of the "
                      f"two preceding entries")
    if len(seq[-1]) != 1:
        raise Bad("sturm.sequence must end in a non-zero constant (elim_poly "
                  "must be squarefree for the count to be valid)")

    def variations(x):
        signs = [sign(ueval(s, x)) for s in seq]
        signs = [s for s in signs if s != 0]
        return sum(1 for a, b in zip(signs, signs[1:]) if a != b)

    sturm = data["sturm"]
    a, b = (Q(x, "sturm.count_interval") for x in need(sturm, "count_interval",
                                                       "sturm"))
    if a >= b:
        raise Bad("sturm.count_interval is empty")
    if ueval(p, a) == 0:
        raise Bad("sturm.count_interval: elim_poly vanishes at the left endpoint, "
                  "which the half-open count would miss")
    count = need(sturm, "count", "sturm")
    actual = variations(a) - variations(b)
    if actual != count:
        raise Bad(f"Sturm count over ({a}, {b}] is {actual}, certificate says "
                  f"{count}")

    # (4) every counted root is isolated and refuted.
    roots = need(data, "roots", "data")
    if len(roots) != count:
        raise Bad(f"{len(roots)} root entries for a Sturm count of {count}")
    spans = []
    for i, r in enumerate(roots):
        lo, hi = (Q(x, f"root {i} interval") for x in need(r, "interval", f"root {i}"))
        if lo >= hi:
            raise Bad(f"root {i}: empty isolating interval")
        if lo < a or hi > b:
            raise Bad(f"root {i}: isolating interval escapes the counting interval")
        if variations(lo) - variations(hi) != 1:
            raise Bad(f"root {i}: interval ({lo}, {hi}] does not isolate exactly "
                      f"one root")
        spans.append((lo, hi, i))
    spans.sort()
    for (lo1, hi1, i1), (lo2, _, i2) in zip(spans, spans[1:]):
        if hi1 > lo2:
            raise Bad(f"roots {i1} and {i2} have overlapping isolating intervals, "
                      f"so the count does not cover all roots")

    for i, r in enumerate(roots):
        lo, hi = (Q(x, f"root {i} interval") for x in r["interval"])
        ref = need(r, "refutation", f"root {i}")
        cond = parse_poly(need(ref, "condition", f"root {i}"), n,
                          f"root {i} condition")
        s = parse_sense(need(ref, "sense", f"root {i}"), f"root {i} refutation")
        if s not in ("<0", ">0"):
            raise Bad(f"root {i}: refutation must be strict")
        # Substitute x_i = v_i(T)/w(T) and clear denominators: the sign of the
        # condition is the sign of the cleared numerator divided by w^d.
        d = total_degree(cond)
        num = []
        for e, c in cond.items():
            term = [c]
            for k, ek in enumerate(e):
                for _ in range(ek):
                    term = umul(term, nums[k])
            for _ in range(d - sum(e)):
                term = umul(term, w)
            num = uadd(num, term)
        span = [Iv(lo, hi)]
        num_poly = {(k,): c for k, c in enumerate(num) if c != 0}
        w_poly = {(k,): c for k, c in enumerate(w) if c != 0}
        num_sign = (1 if prove_sign_on_box(num_poly, span, 1) else
                    -1 if prove_sign_on_box(num_poly, span, -1) else 0)
        if num_sign == 0:
            raise Bad(f"root {i}: the condition's numerator has no provable sign "
                      f"on the isolating interval")
        w_sign = (1 if prove_sign_on_box(w_poly, span, 1) else
                  -1 if prove_sign_on_box(w_poly, span, -1) else 0)
        if w_sign == 0:
            raise Bad(f"root {i}: the parametrization denominator has no provable "
                      f"sign on the isolating interval")
        # condition = numerator / w^d, so its sign is sign(num) * sign(w)^d
        got = num_sign * (w_sign if d % 2 else 1)
        want = 1 if s == ">0" else -1
        if got != want:
            raise Bad(f"root {i}: the condition is not {s} on the isolating "
                      f"interval")
    return (f"{count} real solutions enumerated and refuted "
            f"({len(eqs)} equations, {n} variables)")


CHECKERS = {
    "nullstellensatz": check_nullstellensatz,
    "rur": check_rur,
    "bnb_trace": check_bnb_trace,
    "aps_trace": check_aps_trace,
    "witness": check_witness,
}


def _bind_equations(payoff_rows, n, rel, cert):
    """Re-derive the certificate's polynomial system from the payoff matrix.

    Returns the number of equations bound, or None when the certificate's
    case is not a periodic one (stationary systems etc. — for those the
    name layer is all there is; see bind_systems.py's module docstring).
    """
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import bind_systems
    try:
        return bind_systems.check_binding(payoff_rows, n, rel, cert)
    except bind_systems.Mismatch as e:
        raise Bad(f"certificate {rel}: {e}")
    except bind_systems.NoSystem as e:
        raise Bad(f"certificate {rel}: {e}")


# --------------------------------------------------------------------------
# envelope + driver
# --------------------------------------------------------------------------

def check_manifest(man, path=None):
    """A manifest binds a set of certificates to one game and one code version.

    Without it a certificate that is internally valid but about a *different*
    game would be accepted, and a corpus recorded from a modified working tree
    could not be reconstructed later. Neither is checkable from a certificate
    alone, so both live here.

    The game half has two layers. The name layer compares strings: every
    listed certificate must declare the manifest's game. That alone would
    still accept a valid certificate that had simply been relabelled, so for
    periodic nullstellensatz certificates there is a second layer: the
    certificate's equations must BE the system the manifest's payoff matrix
    induces for the case the case table names, re-derived from scratch in
    `bind_systems.py`. (The derivation shares no code with the pipeline; it is
    validated against the pipeline's own systems on both the type-A and the
    type-B construction, plain and saturated.)
    """
    game = need(man, "game", "manifest")
    if not isinstance(game, dict):
        raise Bad("manifest 'game' must be an object with name / N / payoffs")
    name = need(game, "name", "manifest game")
    n = need(game, "N", "manifest game")
    if not isinstance(n, int) or n < 1:
        raise Bad(f"manifest game N must be a positive integer, got {n!r}")
    rows = need(game, "payoffs", "manifest game")
    want = 2 ** n - 1
    if not isinstance(rows, list) or len(rows) != want:
        got = len(rows) if isinstance(rows, list) else type(rows).__name__
        raise Bad(f"payoff matrix must have 2^N-1 = {want} rows, got {got}")
    for i, row in enumerate(rows):
        if not isinstance(row, list) or len(row) != n:
            raise Bad(f"payoff row {i + 1} must have N = {n} entries")
        for x in row:
            Q(x, f"payoff row {i + 1}")

    prov = man.get("provenance")
    if prov is not None:
        commit = need(prov, "code_commit", "provenance")
        if not re.fullmatch(r"[0-9a-f]{40}", str(commit)):
            raise Bad(f"provenance code_commit must be a full git hash, "
                      f"got {commit!r}")
        if prov.get("code_clean") is not True:
            raise Bad("provenance records a dirty working tree: the corpus "
                      "cannot be tied to a code version")

    listed = []
    patterns = {}
    for c in need(man, "claims", "manifest"):
        need(c, "statement", "claim")
        for e in need(c, "case_table", "claim"):
            need(e, "case", "case table entry")
            rel = need(e, "certificate", "case table entry")
            if rel in listed:
                raise Bad(f"certificate {rel} listed twice in the case table")
            listed.append(rel)
            if "pattern" in e:
                if not isinstance(e["pattern"], str) or not e["pattern"].strip():
                    raise Bad(f"case table entry for {rel}: pattern must be a "
                              f"non-empty string")
                patterns[rel] = e["pattern"]

    nbound = 0
    if path is not None:
        base = os.path.dirname(os.path.abspath(path))
        for rel in listed:
            p = os.path.join(base, rel)
            if not os.path.isfile(p):
                raise Bad(f"case table references a missing certificate: {rel}")
            with open(p) as fh:
                other = json.load(fh)
            if other.get("game") != name:
                raise Bad(f"certificate {rel} is about game "
                          f"{other.get('game')!r}, not {name!r}")
            # The case table's `pattern` and the certificate's `case` are two
            # independently written copies of the same fact. Requiring them to
            # agree is what turns the case table from a file inventory into a
            # statement about which enumeration cases are covered.
            if patterns.get(rel, other.get("case")) != other.get("case"):
                raise Bad(f"case table says {rel} refutes pattern "
                          f"{patterns[rel]!r}, the certificate says "
                          f"{other.get('case')!r}")
            if "case" in other and rel not in patterns:
                raise Bad(f"certificate {rel} names case {other['case']!r} but "
                          f"the case table entry carries no pattern")
            # The equations themselves must be the system this payoff matrix
            # induces for the named case — the half of the binding a string
            # comparison cannot give.
            if other.get("type") == "nullstellensatz" and \
                    isinstance(other.get("case"), str):
                bound = _bind_equations(rows, n, rel, other)
                if bound is not None:
                    nbound += 1
        on_disk = set()
        for root, _, names in os.walk(base):
            for f in names:
                p = os.path.join(root, f)
                if f.endswith(".json") and \
                        os.path.abspath(p) != os.path.abspath(path):
                    on_disk.add(os.path.relpath(p, base))
        extra = sorted(on_disk - set(listed))
        if extra:
            raise Bad(f"{len(extra)} certificate(s) under the manifest are not "
                      f"listed in any case table: {extra[:3]}")
    return (f"manifest for {name}: {len(listed)} certificates "
            f"({len(patterns)} bound to a named case, {nbound} with equations "
            f"re-derived from the payoff matrix), "
            f"{want}x{n} exact payoff matrix")


def check_certificate(cert, path=None):
    if not isinstance(cert, dict):
        raise Bad("certificate must be a JSON object")
    v = need(cert, "format_version", "certificate")
    if v != SUPPORTED_FORMAT_VERSION:
        raise Bad(f"unsupported format_version {v!r} (this checker knows "
                  f"{SUPPORTED_FORMAT_VERSION})")
    if isinstance(cert.get("game"), dict) or "claims" in cert:
        return check_manifest(cert, path)
    for field in ("id", "game", "claim", "type"):
        if not isinstance(need(cert, field, "certificate"), str):
            raise Bad(f"certificate.{field} must be a string")
    # `case` names the enumeration case this certificate refutes. It is
    # optional so that older corpora still check, but when present it is the
    # only key that joins a certificate to a case list -- the file name is a
    # bare ordinal and `data.vars` is not unique across a corpus -- so an
    # empty or non-string value is worse than none and is rejected here.
    if "case" in cert:
        if not isinstance(cert["case"], str) or not cert["case"].strip():
            raise Bad("certificate.case must be a non-empty string")
    t = cert["type"]
    if t not in KNOWN_TYPES:
        raise Bad(f"unknown certificate type {t!r}")
    return CHECKERS[t](cert)


def check_file(path):
    try:
        with open(path) as fh:
            cert = json.load(fh)
    except json.JSONDecodeError as e:
        return False, f"not valid JSON: {e}"
    try:
        return True, check_certificate(cert, path)
    except Bad as e:
        return False, str(e)
    except RecursionError:
        return False, "split tree too deep for this checker"


def collect(paths):
    files = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, names in os.walk(p):
                files.extend(os.path.join(root, f) for f in sorted(names)
                             if f.endswith(".json"))
        else:
            files.append(p)
    return sorted(files)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("paths", nargs="+", help="certificate files or directories")
    ap.add_argument("--expect-fail", action="store_true",
                    help="negative testing: every certificate must be rejected")
    ap.add_argument("-q", "--quiet", action="store_true")
    args = ap.parse_args(argv)

    files = collect(args.paths)
    if not files:
        print("no certificates found", file=sys.stderr)
        return 2
    bad = 0
    for f in files:
        ok, msg = check_file(f)
        good = (not ok) if args.expect_fail else ok
        if not good:
            bad += 1
        if not args.quiet or not good:
            label = "PASS" if good else "FAIL"
            detail = f"rejected: {msg}" if args.expect_fail and not ok else msg
            print(f"{label}  {f}\n      {detail}")
    verb = "rejected" if args.expect_fail else "accepted"
    print(f"\n{len(files) - bad}/{len(files)} {verb} as expected")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
