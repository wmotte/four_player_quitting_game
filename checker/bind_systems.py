#!/usr/bin/env python3
"""Bind periodic nullstellensatz certificates to the manifest's payoff matrix.

The manifest binds a certificate to a game by *name*: `certificate.game` must
equal `manifest.game.name`. That is a string comparison, and it is all that
stands between the corpus and a certificate that is internally valid — its
Nullstellensatz identity checks out — but talks about a *different* game.
This module closes that gap for the periodic certificates: it recomputes, in
Python and sharing no code with the Julia pipeline, the exact polynomial
system the certifier must have handed to msolve for (payoff matrix, case
label), and requires the certificate's equations to equal it.

What is re-derived here is the construction documented at the top of
`code/julia/src/periodic_cert.jl`. Per stage t the stage-game polynomials in
the block variables x^t_i (quit probabilities) are, with P_m the probability
that exactly coalition m quits at t:

    q^t    = P_0                                   (nobody quits)
    A^t_i  = sum_{m != 0} P_m * r[m, i]            (absorption payoff)
    qv^t_i = sum over m not containing i of qq_i(m) * r[m + {i}, i]
    sb^t_i = sum over m not containing i, m != 0, of qq_i(m) * r[m, i]
    sv^t_i = qq_i(0) = prod_{j != i} (1 - x^t_j)   (opponents all continue)

where qq_i(m) is the probability that exactly coalition m of i's *opponents*
quits, and r[mask, i] is the exact rational payoff from the manifest (row
mask - 1 of `game.payoffs`). A support pattern pins every non-mixing entry to
0 (sure continue) or 1 (sure quit); substituting those pins gives:

* **Type A** (no sure quitter, k recurring stages): one equation per mixing
  entry (t, i), in the mixing entries only —

      qv^t_i = sb^t_i + sv^t_i * Y^{t+1}_i,
      Y^s_i  = qv^s_i                    if i mixes at s,
             = A^s_i + q^s * Y^{s+1}_i   otherwise,

  the recursion ending at the first stage cyclically after t where i mixes.
  The saturated variant adds the Rabinowitsch variable t0 and the equation
  t0 * D * prod_v (1 - x_v) = 1 with D = 1 - prod_t q^t.

* **Type B** (first sure quitter at stage T): absorption is sure at T, so
  y^T = A^T and y^t = A^t + q^t * y^{t+1} for t < T; a mixer at t < T gets
  qv^t_i = sb^t_i + sv^t_i * y^{t+1}_i, a mixer at T gets qv^T_i = sb^T_i
  (its survival polynomial is identically zero — a sure quitter is among the
  opponents). Constant equations are dropped; a *nonzero* constant equation
  means the pattern is refuted without msolve and cannot carry a certificate
  at all. The saturated variant adds t0 * prod_v x_v (1 - x_v) = 1.

As in the pipeline, every polynomial is printed to msolve with its
coefficient denominators cleared (multiplied by their lcm, NOT made
primitive), and the certificate's JSON equations are exactly that printed
system, parsed. So the comparison here is exact equality of the cleared
polynomials, as an unordered system.
"""

import os
import re
import sys
from fractions import Fraction
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import enumerate_cases as enum  # noqa: E402

_K_FROM_PATH = re.compile(r"periodic_k(\d+)")


class Mismatch(Exception):
    """The certificate's equations are not the system the matrix induces."""


class NotPeriodic(Exception):
    """The case label is not a periodic one; this module binds nothing."""


class NoSystem(Exception):
    """The case can carry no certificate at all (refuted before msolve)."""


# --------------------------------------------------------------------------
# sparse polynomials over the k*N block slots: {exponent tuple: Fraction}
# Slots are 1-based, slot(t, i) = (t-1)*N + i, matching the pipeline's
# variable names x1 .. x{kN}; exponent vectors are 0-based lists of length nv.
# --------------------------------------------------------------------------

def pconst(nv, c):
    return {(0,) * nv: c} if c else {}


def pvar(nv, slot):
    e = [0] * nv
    e[slot - 1] = 1
    return {tuple(e): Fraction(1)}


def padd(a, b):
    r = dict(a)
    for e, c in b.items():
        n = r.get(e, Fraction(0)) + c
        if n:
            r[e] = n
        else:
            r.pop(e, None)
    return r


def pscale(a, c):
    return {e: v * c for e, v in a.items()} if c else {}


def psub(a, b):
    return padd(a, pscale(b, Fraction(-1)))


def pmul(a, b):
    r = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            n = r.get(e, Fraction(0)) + ca * cb
            if n:
                r[e] = n
            else:
                r.pop(e, None)
    return r


def psubst(a, fixed):
    """x_j = c for every pinned slot j; result keeps full-length exponents."""
    r = {}
    for e, c in a.items():
        e2 = list(e)
        for j, v in fixed.items():
            k = e2[j - 1]
            if k:
                c *= v ** k
                e2[j - 1] = 0
        if c:
            e2 = tuple(e2)
            n = r.get(e2, Fraction(0)) + c
            if n:
                r[e2] = n
            else:
                r.pop(e2, None)
    return r


def isconst(a):
    return all(not any(e) for e in a)


def constval(a, nv):
    return a.get((0,) * nv, Fraction(0))


# --------------------------------------------------------------------------
# the stage-game polynomials, one set per stage
# --------------------------------------------------------------------------

def periodic_polys(payoffs, N, k):
    """payoffs: rows of exact rationals, row m-1 the coalition mask m."""
    nv = k * N

    def slot(t, i):
        return (t - 1) * N + i

    r = [[Q(x) for x in row] for row in payoffs]
    if len(r) != 2 ** N - 1:
        raise Mismatch(f"payoff matrix must have 2^N-1 = {2 ** N - 1} rows")

    q, A, qval, sabs, surv = {}, {}, {}, {}, {}
    for t in range(1, k + 1):
        # P[m] = P(exactly coalition m quits at t), built player by player
        P = [None] * (2 ** N)
        P[0] = pconst(nv, Fraction(1))
        for j in range(1, N + 1):
            bit = 1 << (j - 1)
            xj = pvar(nv, slot(t, j))
            cj = psub(pconst(nv, Fraction(1)), xj)
            for m in range(2 ** j - 1, -1, -1):
                if not (m & bit):
                    base = P[m]
                    P[m + bit] = pmul(base, xj)
                    P[m] = pmul(base, cj)
        q[t] = P[0]
        for i in range(1, N + 1):
            a = {}
            for m in range(1, 2 ** N):
                a = padd(a, pscale(P[m], r[m - 1][i - 1]))
            A[t, i] = a
        for i in range(1, N + 1):
            ibit = 1 << (i - 1)
            qv, sb, sv = {}, {}, {}
            for m in range(2 ** N):
                if m & ibit:
                    continue
                qq = pconst(nv, Fraction(1))
                for j in range(1, N + 1):
                    if j == i:
                        continue
                    xj = pvar(nv, slot(t, j))
                    qq = pmul(qq, xj if (m >> (j - 1)) & 1
                              else psub(pconst(nv, Fraction(1)), xj))
                qv = padd(qv, pscale(qq, r[m + ibit - 1][i - 1]))
                if m == 0:
                    sv = qq
                else:
                    sb = padd(sb, pscale(qq, r[m - 1][i - 1]))
            qval[t, i], sabs[t, i], surv[t, i] = qv, sb, sv
    return {"nv": nv, "slot": slot, "q": q, "A": A,
            "qval": qval, "sabs": sabs, "surv": surv}


def Q(x):
    if not isinstance(x, str):
        raise Mismatch(f"payoff entries must be strings, got {type(x).__name__}")
    try:
        return Fraction(x)
    except (ValueError, ZeroDivisionError):
        raise Mismatch(f"payoff entry is not an exact rational: {x!r}")


# --------------------------------------------------------------------------
# per-case system assembly
# --------------------------------------------------------------------------

def _substituted(pp, N, k, fixed):
    return (
        {t: psubst(pp["q"][t], fixed) for t in range(1, k + 1)},
        {(t, i): psubst(pp["A"][t, i], fixed)
         for t in range(1, k + 1) for i in range(1, N + 1)},
        {(t, i): psubst(pp["qval"][t, i], fixed)
         for t in range(1, k + 1) for i in range(1, N + 1)},
        {(t, i): psubst(pp["sabs"][t, i], fixed)
         for t in range(1, k + 1) for i in range(1, N + 1)},
        {(t, i): psubst(pp["surv"][t, i], fixed)
         for t in range(1, k + 1) for i in range(1, N + 1)},
    )


def _lift(p):
    return {e + (0,): c for e, c in p.items()}


def _type_a(pp, N, k, block, saturated):
    nv = pp["nv"]
    slot = pp["slot"]
    mixslots = sorted(slot(t, i) for t in range(1, k + 1) for i in range(1, N + 1)
                      if i in block[t - 1])
    fixed = {slot(t, i): Fraction(0)
             for t in range(1, k + 1) for i in range(1, N + 1)
             if i not in block[t - 1]}
    qs, As, qv, sb, sv = _substituted(pp, N, k, fixed)

    def yexp(s, i):
        if i in block[s - 1]:
            return qv[s, i]
        return padd(As[s, i], pmul(qs[s], yexp(s % k + 1, i)))

    xeqs = []
    for t in range(1, k + 1):
        for i in range(1, N + 1):
            if i in block[t - 1]:
                xeqs.append(psub(qv[t, i],
                                 padd(sb[t, i],
                                      pmul(sv[t, i], yexp(t % k + 1, i)))))
    if not saturated:
        # No constant filtering, mirroring the pipeline's aux tuple: a zero
        # polynomial would be printed as "0" and parsed back as no terms.
        return mixslots, xeqs
    prod = pconst(nv + 1, Fraction(1))
    for t in range(1, k + 1):
        prod = pmul(prod, qs[t])
    D = psub(pconst(nv, Fraction(1)), prod)
    sat = pmul(_lift(D), pvar(nv + 1, nv + 1))
    for v in mixslots:
        sat = pmul(sat, psub(pconst(nv + 1, Fraction(1)), pvar(nv + 1, v)))
    return mixslots + ["t0"], [_lift(p) for p in xeqs] + \
        [psub(sat, pconst(nv + 1, Fraction(1)))]


def _type_b(pp, N, k, stages, saturated):
    nv = pp["nv"]
    slot = pp["slot"]
    T = len(stages)
    sigma = {}
    for t, (quitters, mixers) in enumerate(stages, start=1):
        for i in range(1, N + 1):
            sigma[t, i] = 1 if i in quitters else 2 if i in mixers else 0
    mixslots = sorted(slot(t, i) for (t, i), v in sigma.items() if v == 2)
    fixed = {slot(t, i): Fraction(v)
             for (t, i), v in sigma.items() if v != 2}
    qs, As, qv, sb, sv = _substituted(pp, N, k, fixed)
    y = {T: {i: As[T, i] for i in range(1, N + 1)}}
    for t in range(T - 1, 0, -1):
        y[t] = {i: padd(As[t, i], pmul(qs[t], y[t + 1][i]))
                for i in range(1, N + 1)}
    eqs = []
    for t in range(1, T + 1):
        for i in range(1, N + 1):
            if sigma[t, i] != 2:
                continue
            if t == T:
                eqs.append(psub(qv[T, i], sb[T, i]))
            else:
                eqs.append(psub(qv[t, i],
                                padd(sb[t, i], pmul(sv[t, i], y[t + 1][i]))))
    for e in eqs:
        if isconst(e) and constval(e, nv) != 0:
            raise NoSystem("the case is refuted by a constant equation "
                           "before msolve ever runs")
    eqs = [e for e in eqs if not isconst(e)]
    if not saturated:
        return mixslots, eqs
    sat = pvar(nv + 1, nv + 1)
    for v in mixslots:
        sat = pmul(sat, pmul(pvar(nv + 1, v),
                             psub(pconst(nv + 1, Fraction(1)),
                                  pvar(nv + 1, v))))
    return mixslots + ["t0"], [_lift(p) for p in eqs] + \
        [psub(sat, pconst(nv + 1, Fraction(1)))]


# --------------------------------------------------------------------------
# comparison against the certificate
# --------------------------------------------------------------------------

def _clear_denominators(p):
    """Multiply through by the lcm of the coefficient denominators — exactly
    what the pipeline's msolve printing does (no primitivization)."""
    den = 1
    for c in p.values():
        den = den * c.denominator // gcd(den, c.denominator)
    return {e: c * den for e, c in p.items()}


def _project(p, idx):
    """Drop exponent positions outside idx; they must all be zero."""
    out = {}
    for e, c in p.items():
        if any(e[j] for j in range(len(e)) if j not in idx):
            raise Mismatch("an equation uses a variable outside the "
                           "certificate's variable list")
        ne = tuple(e[j] for j in idx)
        n = out.get(ne, Fraction(0)) + c
        if n:
            out[ne] = n
        else:
            out.pop(ne, None)
    return out


def _parse_cert_poly(terms, nvars):
    p = {}
    for t in terms:
        coeff, exps = t
        c = Q(coeff) if isinstance(coeff, str) else Fraction(coeff)
        if len(exps) != nvars:
            raise Mismatch(f"exponent vector must have {nvars} entries")
        e = tuple(int(v) for v in exps)
        n = p.get(e, Fraction(0)) + c
        if n:
            p[e] = n
        else:
            p.pop(e, None)
    return p


def expected_system(payoffs, N, case_label, cert_path, cert_vars):
    """(variable names, [polynomial over those variables]) that the payoff
    matrix induces for this case, in the certificate's own representation.

    cert_path is only consulted for the period length of type-B cases: their
    label names the stages up to the first sure quitter, not k. Type-A
    labels name all k stages, so a path marker there is only cross-checked.
    """
    try:
        kind, body = enum.parse_case(case_label)
    except ValueError:
        raise NotPeriodic(case_label)
    saturated = "t0" in cert_vars
    m = _K_FROM_PATH.search(cert_path or "")
    if kind == "A":
        k = len(body)
        if m and int(m.group(1)) != k:
            raise Mismatch(f"case label has {k} stages but the path says "
                           f"periodic_k{m.group(1)}")
    else:
        if m is None:
            raise Mismatch("a type-B case does not record the period length; "
                           "the certificate must live under a periodic_k<N>/ "
                           "directory for the binding to be checkable")
        k = int(m.group(1))
        if len(body) > k:
            raise Mismatch(f"case label has {len(body)} stages, more than "
                           f"k = {k}")
    pp = periodic_polys(payoffs, N, k)
    if kind == "A":
        slots, eqs = _type_a(pp, N, k, body, saturated)
    else:
        slots, eqs = _type_b(pp, N, k, body, saturated)
    names = ["x%d" % s if isinstance(s, int) else s for s in slots]
    if set(names) != set(cert_vars):
        raise Mismatch(f"the induced system is over {names}, but the "
                       f"certificate declares {sorted(cert_vars)}")
    idx = [s - 1 if isinstance(s, int) else pp["nv"] for s in slots]
    order = [names.index(v) for v in cert_vars]  # cert-var order
    out = []
    for p in eqs:
        proj = _project(_clear_denominators(p), idx)
        out.append({tuple(e[j] for j in order): c for e, c in proj.items()})
    return names, out


def check_binding(payoffs, N, rel, cert):
    """Raise Mismatch/NoSystem if cert's equations are not the system the
    payoff matrix induces for cert's case; return None if there is nothing
    to bind (not a periodic case)."""
    case = cert.get("case")
    try:
        names, eqs = expected_system(payoffs, N, case, rel,
                                     cert["data"]["vars"])
    except NotPeriodic:
        return None
    try:
        got = [_parse_cert_poly(t, len(cert["data"]["vars"]))
               for t in cert["data"]["equations"]]
    except (KeyError, TypeError, IndexError):
        raise Mismatch("certificate data has no vars/equations to bind")
    want = sorted(sorted(p.items()) for p in eqs)
    have = sorted(sorted(p.items()) for p in got)
    if want != have:
        only_want = [dict(p) for p in want if p not in have]
        only_have = [dict(p) for p in have if p not in want]
        raise Mismatch(
            f"the equations are not the system the payoff matrix induces "
            f"for case {case!r}: {len(only_want)} induced polynomial(s) "
            f"missing, {len(only_have)} unexpected (first unexpected: "
            f"{only_have[:1]})")
    return len(eqs)
