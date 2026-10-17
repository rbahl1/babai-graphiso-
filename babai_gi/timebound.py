"""Verification of the numerical inequalities of the time bound (``PROOF.md``, Part II).

Every inequality that the proof reduces to is checked here with exact interval
arithmetic (``interval.py``): on a bounded range by bisection, and beyond it by the
dominance lemma ``tail_dominated`` (Lemma 11.2 of ``PROOF.md``).  Each check is a
statement "f(x) >= 0 for all x in D" where the proof writes f as P - N with P and N
nondecreasing on D, so that on a sub-interval [a, b] the value P(a) - N(b) is a lower
bound of f; the functions ``*_PN`` below return the enclosures of P and N at a point.

``python -m babai_gi.timebound`` runs every check and prints the constants and the
table of a(b).
"""

from __future__ import annotations

from bisect import bisect_right
from fractions import Fraction
from math import factorial, floor
from typing import Callable, Iterable, List, Optional, Sequence, Tuple

from .interval import LN2, LOG2_3_2, PI2, Interval, log2, sqrt

Num = Fraction


# ------------------------------------------------------------ rounding

_BITS = 48


def _dn(q: Fraction, bits: int = _BITS) -> Fraction:
    s = 1 << bits
    return Fraction((q.numerator * s) // q.denominator, s)


def _up(q: Fraction, bits: int = _BITS) -> Fraction:
    s = 1 << bits
    return Fraction(-((-q.numerator * s) // q.denominator), s)


def rnd(x: Interval, bits: int = _BITS) -> Interval:
    """Outward rounding to dyadic endpoints (keeps the fractions small)."""
    x = Interval.of(x)
    return Interval(_dn(x.lo, bits), _up(x.hi, bits))


def _L_point(q: Fraction) -> Interval:
    """log2 q = e + log2(q / 2^e) with q / 2^e in [1/2, 2], the quotient rounded outward to
    dyadic rationals first (log2 is increasing), so that the series runs on small numbers."""
    if q <= 0:
        raise ValueError("log2 of a non-positive number")
    e = q.numerator.bit_length() - q.denominator.bit_length()
    r = q / (Fraction(2) ** e)
    lo = log2(Interval(_dn(r, 60))).lo if _dn(r, 60) > 0 else log2(Interval(r)).lo
    hi = log2(Interval(_up(r, 60))).hi
    return Interval(_dn(lo + e), _up(hi + e))


def L(x) -> Interval:
    """log2 of a positive point or interval, rounded outward."""
    x = Interval.of(x)
    if x.lo == x.hi:
        return _L_point(x.lo)
    return Interval(_L_point(x.lo).lo, _L_point(x.hi).hi)


# ------------------------------------------------------------ constants

DELTA = rnd(LOG2_3_2, 60)                     # delta = log2(3/2)
S2 = rnd(Fraction(1, 2) + PI2 / 6, 60)        # 1/2 + pi^2/6
BETA = rnd(S2 / DELTA, 60)                    # S2 / delta: choice count 2^(beta y^2 + R(y))
B = rnd(1 / (2 * DELTA), 60)                  # 1 / (2 delta)
A = rnd((BETA - Fraction(1, 2)) / (3 * DELTA), 60)
BSTAR = rnd(A + B, 60)                        # = (S2 + delta) / (3 delta^2)
BGI = rnd(2 * A + 3 * B, 60)                  # leading constant for graphs, in log^3 v
C = Fraction(2)
INV_LN2 = rnd(1 / LN2, 60)

# rho(w) = RA w log^2 w + RB w log w + RC w   (w >= 1)
RA, RB, RC = Fraction(5), Fraction(3), Fraction(12)
# e(u) = E3 u^2 / log^2(u + 4) + 2 E2 u + E1,  E(X) = integral_0^X e(u) du
E3, E2, E1 = Fraction(3), Fraction(11, 2), Fraction(60)

# C-kind: y-coefficient left after the cancellation, and the constant
C1 = rnd(1 + DELTA * (BETA + Fraction(1, 2)) - 2 * C * DELTA, 60)
CC0 = rnd(4 + C * DELTA * DELTA - BSTAR * DELTA ** 3, 60)
Q1_MARGIN = Fraction(21, 10)                  # the share of CC0 checked in (Q1)
Q2_MARGIN = Fraction(21, 10)                  # ... and in (Q2); Q1 + Q2 >= CC0

Y0 = Fraction(6491853096329, 10 ** 12)        # <= log2(90) (checked below)


# ------------------------------------------------------------ the functions

def R_fun(Y) -> Interval:
    """The remainder of the Split-or-Johnson choice count (soj.md, Theorem B):
    5.8 Y L^2 + 6.1 Y L + 10.3 Y + 3.5 L^2 + 6 L + 9 with L = log2 Y."""
    Y = Interval.of(Y)
    l = L(Y)
    return rnd(Fraction(58, 10) * Y * l * l + Fraction(61, 10) * Y * l + Fraction(103, 10) * Y
               + Fraction(35, 10) * l * l + 6 * l + 9)


def rho(w) -> Interval:
    w = Interval.of(w)
    l = L(w)
    return rnd(RA * w * l * l + RB * w * l + RC * w)


def phi(w) -> Interval:
    """phi(w) = w rho(w)."""
    w = Interval.of(w)
    return rnd(w * rho(w))


def phi_prime(w) -> Interval:
    """phi'(w) = 2 RA w L^2 + (2 RA / ln 2 + 2 RB) w L + (RB / ln 2 + 2 RC) w; nondecreasing on [1, oo)."""
    w = Interval.of(w)
    l = L(w)
    return rnd(2 * RA * w * l * l + (2 * RA * INV_LN2 + 2 * RB) * w * l + (RB * INV_LN2 + 2 * RC) * w)


def e_fun(u) -> Interval:
    """e(u) = E3 u^2 / log2(u + 4)^2 + 2 E2 u + E1: nondecreasing on [0, oo) (PROOF.md, Lemma 4.1)
    and convex (Lemma 13.2)."""
    u = Interval.of(u)
    l = L(u + 4)
    return rnd(E3 * u * u / (l * l) + 2 * E2 * u + E1)


def E_upper(X: Fraction, steps: int = 64) -> Interval:
    """An interval containing E(X) = int_0^X e: lower and upper Riemann sums (e nondecreasing)."""
    X = Fraction(X)
    if X <= 0:
        return Interval(0)
    h = X / steps
    lo = Fraction(0)
    hi = Fraction(0)
    prev = e_fun(Fraction(0))
    for j in range(1, steps + 1):
        cur = e_fun(h * j)
        lo += h * prev.lo
        hi += h * cur.hi
        prev = cur
    return Interval(lo, hi)


def F(z, w, Y) -> Interval:
    z, w, Y = Interval.of(z), Interval.of(w), Interval.of(Y)
    return rnd(z * (A * w * w + B * w * (Y - (z - w) / 2)))


def T_level(z, w, Y) -> Interval:
    """The term of one level: F(z, w, Y) + z rho(w) + C z^2."""
    z = Interval.of(z)
    return rnd(F(z, w, Y) + z * rho(w) + C * z * z)


def k_of(X: Fraction) -> int:
    """k = k_paper(n) = max(9, floor(log2 n) + 3) as a function of X = log2 n."""
    return max(9, floor(X) + 3)


_FACT_CACHE = {}


def log2_factorial(m: int) -> Interval:
    v = _FACT_CACHE.get(m)
    if v is None:
        v = L(Fraction(factorial(m)))
        _FACT_CACHE[m] = v
    return v


# ------------------------------------------------------------ bisection

class CheckFailed(AssertionError):
    pass


def verify_PN(name: str, PN: Callable[[Fraction], Tuple[Interval, Interval]], a: Fraction, b: Fraction,
              breaks: Sequence[Fraction] = (), min_width: Fraction = Fraction(1, 1 << 20),
              rel: bool = True) -> int:
    """Check f = P - N >= 0 on [a, b] for P, N nondecreasing on [a, b] (on each piece between
    consecutive ``breaks``, which is where the proof's formula for P and N may change, e.g. at
    integers for floor(X)).  On [u, v]: f >= P(u).lo - N(v).hi.  Returns the number of pieces."""
    pts = sorted(set([Fraction(a), Fraction(b)] + [Fraction(t) for t in breaks if a < t < b]))
    count = 0
    stack: List[Tuple[Fraction, Fraction]] = [(pts[i], pts[i + 1]) for i in range(len(pts) - 1)][::-1]
    while stack:
        u, v = stack.pop()
        Pu, _ = PN(u)
        _, Nv = PN(v)
        if Pu.lo - Nv.hi >= 0:
            count += 1
            continue
        if v - u < min_width:
            raise CheckFailed(f"{name}: fails near [{float(u)}, {float(v)}]: P={Pu!r} N={Nv!r}")
        mid = _dn((u + v) / 2, 40)
        if not (u < mid < v):
            mid = (u + v) / 2
        stack.append((mid, v))
        stack.append((u, mid))
    return count


def integer_breaks(a: Fraction, b: Fraction) -> List[Fraction]:
    return [Fraction(j) for j in range(floor(a) + 1, floor(b) + 1)]


# ------------------------------------------------------------ dominance lemma for the tails

Term = Tuple[Interval, Fraction, Fraction]      # c * x^p * (log2 x)^q


def tail_dominated(name: str, terms: Sequence[Term], x1: Fraction) -> None:
    """Lemma 11.2: if f(x) >= sum_i c_i x^{p_i} L^{q_i} (L = log2 x) for x >= x1 >= 4, the term d with
    the lexicographically largest (p, q) has c_d > 0, every other (p_i, q_i) is smaller, and for
    p_i < p_d: (q_i - q_d) <= (p_d - p_i) ln x1, then the ratios x^{p_i} L^{q_i} / (x^{p_d} L^{q_d}) are
    nonincreasing on [x1, oo), so f(x) >= x^{p_d} L^{q_d} (c_d + sum_{c_i < 0} c_i r_i(x1)) >= 0 when the
    bracket is >= 0 at x1."""
    x1 = Fraction(x1)
    if x1 < 4:
        raise ValueError("x1 >= 4")
    d = max(range(len(terms)), key=lambda i: (terms[i][1], terms[i][2]))
    cd, pd, qd = terms[d]
    if not cd.lo > 0:
        raise CheckFailed(f"{name}: leading coefficient not positive")
    lnx1 = rnd(Interval.of(L(x1)) * LN2)
    lx1 = L(x1)
    bracket = Interval(cd.lo)
    for i, (c, p, q) in enumerate(terms):
        if i == d:
            continue
        if (p, q) >= (pd, qd):
            raise CheckFailed(f"{name}: two leading terms")
        if p < pd and not (q - qd) <= ((pd - p) * lnx1).lo:
            raise CheckFailed(f"{name}: ratio of term {i} not monotone from x1")
        if c.lo < 0:
            # r_i(x1) = x1^(p - pd) * L(x1)^(q - qd); p - pd and q - qd may be fractional:
            # only integer exponents are used in this module
            if (p - pd).denominator != 1 or (q - qd).denominator != 1:
                raise ValueError("integer exponents only")
            r = Interval(Fraction(x1)) ** 0
            pe, qe = int(p - pd), int(q - qd)
            r = r * (Interval(x1) ** pe if pe >= 0 else 1 / Interval(x1) ** (-pe))
            r = r * (lx1 ** qe if qe >= 0 else 1 / lx1 ** (-qe))
            bracket = bracket + Interval(c.lo) * Interval(r.hi)
    if not bracket.lo >= 0:
        raise CheckFailed(f"{name}: tail bracket {bracket!r} at x1 = {float(x1)}")


# ============================================================ the reduced inequalities
#
# Each function returns (P(x), N(x)) as enclosures; the proof shows f = P - N with P, N
# nondecreasing on the stated domain, and f >= 0 is the inequality of PROOF.md named in
# the docstring.

def q1_PN(y: Fraction) -> Tuple[Interval, Interval]:
    """(Q1), y >= Y0: phi(y) - phi(y - delta) >= R(y) + C1 y + Q1_MARGIN (Lemma 11.4);
    phi(y) - phi(y - delta) = int_{y-delta}^y phi' is nondecreasing because phi' is."""
    y = Fraction(y)
    P = rnd(phi(y) - phi(y - DELTA))
    N = rnd(R_fun(y) + C1 * y + Q1_MARGIN)
    return P, N


def q1_tail(y1: Fraction) -> None:
    """(Q1) for y >= y1: with l = log2 y and eps = delta / ((y1 - delta) ln 2) >= log2 y - log2(y - delta),
    (y - d) L(y-d)^2 >= y l^2 - d l^2 - 2 eps y l and (y - d) L(y-d) >= y l - d l - eps y."""
    eps = rnd(DELTA * INV_LN2 / (Fraction(y1) - DELTA))
    a2 = 2 * RA
    a1 = 2 * RA * INV_LN2 + 2 * RB
    a0 = RB * INV_LN2 + 2 * RC
    terms = [
        (rnd(DELTA * a2 - Fraction(58, 10)), Fraction(1), Fraction(2)),
        (rnd(-DELTA * a2 * 2 * eps + DELTA * a1 - Fraction(61, 10)), Fraction(1), Fraction(1)),
        (rnd(-DELTA * a1 * eps + DELTA * a0 - Fraction(103, 10) - C1), Fraction(1), Fraction(0)),
        (rnd(-DELTA * DELTA * a2 - Fraction(35, 10)), Fraction(0), Fraction(2)),
        (rnd(-DELTA * DELTA * a1 - 6), Fraction(0), Fraction(1)),
        (rnd(-DELTA * DELTA * a0 - 9 - Q1_MARGIN), Fraction(0), Fraction(0)),
    ]
    tail_dominated("Q1", terms, y1)


def q2_PN(X: Fraction) -> Tuple[Interval, Interval]:
    """(Q2), X >= Y0 + 1: delta e(X - delta) >= delta + delta X / 2 + Q2_MARGIN
    (lower bound of E(X) - E(X - delta) - delta - delta X / 2)."""
    P = rnd(DELTA * e_fun(X - DELTA))
    N = rnd(DELTA + DELTA * X / 2 + Q2_MARGIN)
    return P, N


def q2_tail(x1: Fraction) -> None:
    """e(u) >= 2 E2 u + E1, so delta e(X - delta) >= 2 E2 delta X + delta (E1 - 2 E2 delta)."""
    terms = [
        (rnd(2 * E2 * DELTA - DELTA / 2), Fraction(1), Fraction(0)),
        (rnd(DELTA * (E1 - 2 * E2 * DELTA) - DELTA - Q2_MARGIN), Fraction(0), Fraction(0)),
    ]
    tail_dominated("Q2", terms, x1)


CE2 = rnd(3 * A + 2 * B - 1 - BETA, 60)
CE1 = rnd(-3 * A + B + 2 * C - 2, 60)
CE0 = rnd(-3 * B - 2 * C, 60)


def q3_PN(y: Fraction) -> Tuple[Interval, Interval]:
    """(Q3), y >= Y0: E-kind, t = 1, at X = y + 1 (Lemma 11.5):
    CE2 y^2 + CE1 y + CE0 + phi'(y - 1) - rho(1) - R(y) - 4 >= 0."""
    assert CE2.lo > 0 and CE1.hi < 0 and CE0.hi < 0
    P = rnd(CE2 * y * y + phi_prime(Fraction(y) - 1))
    N = rnd(-CE1 * y - CE0 + rho(Fraction(1)) + R_fun(y) + 4)
    return P, N


def q3_tail(y1: Fraction) -> None:
    """phi' >= 0 is dropped; -R(y) is expanded into its monomials."""
    terms = [
        (rnd(Interval.of(CE2)), Fraction(2), Fraction(0)),
        (Interval(Fraction(-58, 10)), Fraction(1), Fraction(2)),
        (Interval(Fraction(-61, 10)), Fraction(1), Fraction(1)),
        (rnd(Fraction(-103, 10) + CE1), Fraction(1), Fraction(0)),
        (Interval(Fraction(-35, 10)), Fraction(0), Fraction(2)),
        (Interval(Fraction(-6)), Fraction(0), Fraction(1)),
        (rnd(CE0 - rho(Fraction(1)) - 9 - 4), Fraction(0), Fraction(0)),
    ]
    tail_dominated("Q3", terms, y1)


ZDEF = Fraction(1017, 1000)     # 2y - z_min(y) <= 1 - log2(1 - 1/90) < 1.017


def q4_PN(y: Fraction) -> Tuple[Interval, Interval]:
    """(Q4), y >= Y0: E-kind (and J-kind) with t >= 2, at X = z = z_min (Lemma 11.6):
    z[(A + B/2)(2y - 1) + (B/2) z] + z (rho(y) - rho(y - 1)) - (z + 1) y - beta y^2 - R(y) - 4 >= 0
    for z in [2y - ZDEF, 2y - 1]."""
    y = Fraction(y)
    zl = 2 * y - ZDEF
    zh = 2 * y - 1
    dr = rho(y) - rho(y - 1)
    P = rnd(zl * ((A + B / 2) * (2 * y - 1) + (B / 2) * zl) + zl * dr)
    N = rnd((zh + 1) * y + BETA * y * y + R_fun(y) + 4)
    return P, N


def q4_tail(y1: Fraction) -> None:
    """rho(y) - rho(y - 1) >= 0 dropped; zl = 2y - ZDEF."""
    a = A + B / 2
    # zl a (2y - 1) = a (4y^2 - (2 + 2 ZDEF) y + ZDEF); (B/2) zl^2 = (B/2)(4y^2 - 4 ZDEF y + ZDEF^2)
    terms = [
        (rnd(4 * a + 2 * B - 2 - BETA), Fraction(2), Fraction(0)),
        (Interval(Fraction(-58, 10)), Fraction(1), Fraction(2)),
        (Interval(Fraction(-61, 10)), Fraction(1), Fraction(1)),
        (rnd(-a * (2 + 2 * ZDEF) - 2 * B * ZDEF - Fraction(103, 10)), Fraction(1), Fraction(0)),
        (Interval(Fraction(-35, 10)), Fraction(0), Fraction(2)),
        (Interval(Fraction(-6)), Fraction(0), Fraction(1)),
        (rnd(a * ZDEF + (B / 2) * ZDEF * ZDEF - 9 - 4), Fraction(0), Fraction(0)),
    ]
    tail_dominated("Q4", terms, y1)


OMEGA_J = Fraction(61, 100)     # w_J <= log2(1 + 2^((y+1)/2)) <= y/2 + 1/2 + 0.11 for y >= Y0


def q5_PN(y: Fraction) -> Tuple[Interval, Interval]:
    """(Q5), y >= Y0: J-kind, t = 1, at X = y + 1 (Lemma 11.7), with om = y/2 + OMEGA_J:
    y[A(y^2 - om^2) + B X (y - om) + (B/2) om (y - om)] + y(rho(y) - rho(om)) - (X+1) y - beta y^2 - R(y) - 4."""
    y = Fraction(y)
    om = y / 2 + OMEGA_J
    X = y + 1
    P = rnd(y * (A * (y * y - om * om) + B * X * (y - om) + (B / 2) * om * (y - om)) + y * (rho(y) - rho(om)))
    N = rnd((X + 1) * y + BETA * y * y + R_fun(y) + 4)
    return P, N


def q5_tail(y1: Fraction) -> None:
    """Drop y(rho(y) - rho(om)) >= 0; om = y/2 + c: y A (y^2 - om^2) = A(3/4 y^3 - c y^2 - c^2 y);
    y B (y+1)(y - om) = B (y^3/2 + (1/2 - c) y^2 - c y); y (B/2) om (y - om) = (B/2)(y^3/4 - c^2 y)."""
    c = OMEGA_J
    terms = [
        (rnd(A * Fraction(3, 4) + B / 2 + B / 8), Fraction(3), Fraction(0)),
        (rnd(-A * c + B * (Fraction(1, 2) - c) - 1 - BETA), Fraction(2), Fraction(0)),
        (Interval(Fraction(-58, 10)), Fraction(1), Fraction(2)),
        (Interval(Fraction(-61, 10)), Fraction(1), Fraction(1)),
        (rnd(-A * c * c - B * c - (B / 2) * c * c - 2 - Fraction(103, 10)), Fraction(1), Fraction(0)),
        (Interval(Fraction(-35, 10)), Fraction(0), Fraction(2)),
        (Interval(Fraction(-6)), Fraction(0), Fraction(1)),
        (Interval(Fraction(-13)), Fraction(0), Fraction(0)),
    ]
    tail_dominated("Q5", terms, y1)


LOG2_3 = L(Fraction(3))
LOG2_9 = L(Fraction(9))     # letter factor of the comparison calls: (lam + 2)^2 <= 9 lam^2


def _cert_N(X: Fraction, compare: bool) -> Interval:
    k = k_of(X)
    lk = L(Fraction(k))
    if compare:
        return rnd(2 * k * k / (B * lk) - log2_factorial(k) + X + lk + 7 + LOG2_9)
    return rnd(Fraction(k * k) / (2 * B * lk) + X + lk + 6)


def q6_PN(X: Fraction) -> Tuple[Interval, Interval]:
    """(Q6), X >= Y0 + 1 (Lemma 11.8, local certificates): log2(k) e(X - log2 k) >=
    k^2 / (2 B log2 k) + X + log2 k + 6, k = k_of(X); P, N nondecreasing between integers."""
    X = Fraction(X)
    lk = L(Fraction(k_of(X)))
    return rnd(lk * e_fun(X - lk)), _cert_N(X, False)


def q7_PN(X: Fraction) -> Tuple[Interval, Interval]:
    """(Q7), X >= Y0 + 1 (Lemma 11.7, comparisons): log2(k) e(X - log2 k) >=
    2 k^2 / (B log2 k) - log2(k!) + X + log2 k + 7 + log2 9."""
    X = Fraction(X)
    lk = L(Fraction(k_of(X)))
    return rnd(lk * e_fun(X - lk)), _cert_N(X, True)


def _PN_piecewise(PN, X: Fraction, side: str):
    return PN(X)


def q67_tail(x1: Fraction, compare: bool) -> None:
    """For X >= x1 >= 16: k in [X + 2, X + 3], l = log2 X, eps = 4 / (x1 ln 2):
    l <= log2 k <= l + eps and log2(X - log2 k + 4) <= l + eps, so (with X - l - eps >= 0)
      log2(k) e(X - log2 k) >= l [E3 (X - l - eps)^2 / (l + eps)^2 + 2 E2 (X - l - eps) + E1]
    and 1/(l + eps)^2 >= 1/l^2 - 2 eps / l^3;  2k^2/(B log2 k) <= 2 (X + 3)^2 / (B l);
    log2(k!) >= k log2 k - k / ln 2 >= (X + 2) l - (X + 3) / ln 2."""
    x1 = Fraction(x1)
    eps = rnd(4 * INV_LN2 / x1)
    # l E3 (X^2 - 2 X (l + eps)) (1/l^2 - 2 eps/l^3)  (dropping the positive (l+eps)^2 term)
    #   = E3 [X^2/l - 2 eps X^2/l^2 - 2 X (l + eps)/l + 4 eps X (l + eps)/l^2]
    #  >= E3 [X^2/l - 2 eps X^2/l^2 - 2 X - 2 eps X / l]
    terms = [
        (Interval(E3), Fraction(2), Fraction(-1)),
        (rnd(-2 * E3 * eps), Fraction(2), Fraction(-2)),
        (Interval(-2 * E3), Fraction(1), Fraction(0)),
        (rnd(-2 * E3 * eps), Fraction(1), Fraction(-1)),
        (Interval(2 * E2), Fraction(1), Fraction(1)),          # l * 2 E2 X
        (rnd(-2 * E2 * (1 + eps)), Fraction(0), Fraction(2)),   # - l * 2 E2 (l + eps) >= -2E2(1+eps) l^2 (l >= 1)
        (Interval(E1), Fraction(0), Fraction(1)),
    ]
    if compare:
        c = rnd(2 / B)
        terms += [
            (rnd(-c), Fraction(2), Fraction(-1)), (rnd(-6 * c), Fraction(1), Fraction(-1)),
            (rnd(-9 * c), Fraction(0), Fraction(-1)),
            (Interval(Fraction(1)), Fraction(1), Fraction(1)), (Interval(Fraction(2)), Fraction(0), Fraction(1)),
            (rnd(-INV_LN2 - 1), Fraction(1), Fraction(0)),
            (rnd(-3 * INV_LN2 - 7 - LOG2_9 - eps), Fraction(0), Fraction(0)), (Interval(Fraction(-1)), Fraction(0), Fraction(1)),
        ]
    else:
        c = rnd(1 / (2 * B))
        terms += [
            (rnd(-c), Fraction(2), Fraction(-1)), (rnd(-6 * c), Fraction(1), Fraction(-1)),
            (rnd(-9 * c), Fraction(0), Fraction(-1)), (Interval(Fraction(-1)), Fraction(1), Fraction(0)),
            (Interval(Fraction(-1)), Fraction(0), Fraction(1)), (rnd(-6 - eps), Fraction(0), Fraction(0)),
        ]
    # merge equal monomials
    merged = {}
    for cf, p, q in terms:
        merged[(p, q)] = merged.get((p, q), Interval(0)) + cf
    tail_dominated("Q7" if compare else "Q6", [(rnd(v), p, q) for (p, q), v in merged.items()], x1)


# ------------------------------------------------------------ (Q8) small Gamma

def x_min_small_gamma(mg: int) -> Fraction:
    """The smallest X = log2 n at which a Johnson quotient on mg < ell(n) = 10 k(X) points can
    occur with z = log2 mg <= X: k(X) >= (mg + 1)/10."""
    need = -(-(mg + 1) // 10)            # ceil((mg + 1) / 10)
    g = L(Fraction(mg))
    xk = Fraction(max(0, need - 3)) if need > 9 else Fraction(0)
    return max(g.hi, xk)


def log2_factorial_upper(m: int) -> Interval:
    """Robbins: m! <= sqrt(2 pi m) (m/e)^m e^(1/(12 m)), so
    log2 m! <= (m + 1/2) log2 m - m log2 e + log2 sqrt(2 pi) + 1/(12 m ln 2) (upper end only)."""
    if m <= 4096:
        return log2_factorial(m)
    lm = L(Fraction(m))
    pi_hi = Interval(sqrt(PI2).hi)
    v = (m + Fraction(1, 2)) * lm - m * INV_LN2 + L(2 * pi_hi) / 2 + INV_LN2 / (12 * m)
    return Interval(v.hi)


def q8_value(ma: int, mb: int) -> Interval:
    """Lower bound of T(g,g,X) + g e(X - g) - g - log2(m!) - 4 for all m in [ma, mb] at
    X >= x_min(m) (Lemma 11.9)."""
    ga = L(Fraction(ma)).lo
    gb = L(Fraction(mb)).hi
    Xa = x_min_small_gamma(ma)
    if Xa - gb < 0:
        u = Fraction(0)
    else:
        u = Xa - gb
    v = T_level(ga, ga, Xa) + ga * e_fun(u).lo - gb - log2_factorial_upper(mb).hi - 4
    return rnd(v)


def check_q8(m_exact: int = 4096, m_top: int = 1 << 17) -> int:
    count = 0
    for mg in range(6, m_exact + 1):
        if not q8_value(mg, mg).lo >= 0:
            raise CheckFailed(f"Q8 fails at mg = {mg}: {q8_value(mg, mg)!r}")
        count += 1
    ma = m_exact + 1
    while ma <= m_top:
        mb = min(m_top, ma + max(1, ma // 256))
        if not q8_value(ma, mb).lo >= 0:
            raise CheckFailed(f"Q8 fails on [{ma}, {mb}]")
        count += 1
        ma = mb + 1
    # mg > m_top: T >= B g^2 X >= B g^2 (mg/10 - 3) and log2 mg! <= mg g (Lemma 11.9, tail)
    g = Fraction(17)
    if not (B * g / 10 - 1).lo > Fraction(45, 100):
        raise CheckFailed("Q8 tail")
    return count


# ------------------------------------------------------------ (Q9) unrecognised quotients of degree < 25

def check_q9() -> None:
    """Lemma 11.10: for 2 <= m <= 24, z = log2 m: 2 z^2 + (A + B/2 + rho(1)) z >= log2(m!) + 4."""
    for m in range(2, 25):
        z = L(Fraction(m))
        lhs = 2 * z * z + (A + B / 2 + rho(Fraction(1))) * z
        if not (lhs - log2_factorial(m) - 4).lo >= 0:
            raise CheckFailed(f"Q9 fails at m = {m}")


# ------------------------------------------------------------ (W) the own work (PROOF.md §12)
#
# docs/bounds/ownwork.md bounds the own work of every node type by lam^e 2^omega (e <= 2) with
# omega a log-sum of terms.  Here every term is bounded by a combination, with nonnegative
# coefficients, of the basis functions below (all >= 0 for y >= Y0, X >= 1), using
#   log2 M <= k y <= X y + 3 y,  log2 k! <= k log2 k <= (X + 3) log2(X + 3),
#   log2 s <= sigma <= X y + y + beta y^2 + R(y),  t <= X,
# and a log-sum of r terms by the coefficientwise maximum plus log2 r.

BASIS = ("Xy", "y2", "R", "yly", "y", "ly2", "X", "XlX", "1")


def _vec(**kw) -> dict:
    v = {b: Fraction(0) for b in BASIS}
    for kk, c in kw.items():
        v[kk] = v[kk] + Fraction(c)
    return v


def _add(*vs) -> dict:
    out = _vec()
    for v in vs:
        for b in BASIS:
            out[b] += v[b]
    return out


def _scale(c, v) -> dict:
    return {b: Fraction(c) * v[b] for b in BASIS}


def _maxlse(*vs) -> dict:
    """Upper bound of log2(sum 2^{term_i}) by the coefficientwise maximum plus log2(r)."""
    out = {b: max(v[b] for v in vs) for b in BASIS}
    out["1"] += L(Fraction(len(vs))).hi
    return out


def _c(c) -> dict:
    """The constant log2 c, rounded up."""
    return _vec(**{"1": L(Fraction(c)).hi})


BETA_UP = BETA.hi
LM = _vec(Xy=1, y=3)                                  # log2 M
LKF = _vec(XlX=1)                                     # log2 k!
LS = _vec(Xy=1, y=1, y2=BETA_UP, R=1)                 # log2 s <= sigma
UE = _vec(y=7, yly=2, ly2=4)                          # U(y) = (7 + 2 log2 y) y + 4 log2(y + 2)
RT = _vec(ly2=1, X=2, Xy=2, y=1, **{"1": Fraction(844, 100)})   # log2(y+1) + log2(4t^2+55t+287) + (2t+1) y
RK = _vec(ly2=1, X=2, Xy=2, y=7, **{"1": Fraction(917, 100)})   # the same with k <= X + 3
PISO = _vec(X=7, **{"1": Fraction(2374, 100)})        # log2 P_iso(n) <= 7X + 23.74


def own_work_johnson_imprimitive() -> dict:
    """Upper bound (in the basis) of log2(W_tot / lam^2) + 1 for an imprimitive Johnson node:
    ownwork.md §8.14 (J0, aggregate, Q_A wrappers, every case) plus P_iso for every call."""
    X = lambda c: _vec(X=c)
    terms = [
        _add(_c(29070), X(5)), _add(_c(672), X(1)),
        _add(_c(1508700), LM, X(6)), _add(_c(3514), LM, LKF, X(4)), _add(_c("44.8"), _scale(3, LM), X(2)),
        _add(_c(131), _scale(2, LM)),
        _add(_c(41421), LM, LKF, X(6)),
        _add(_c(5989168), X(5)), _add(_c(20604), LM, X(3)),
        _add(_c(18105170), X(5)), _add(_c(33218), LM, X(3)),
        _add(_c("3.75"), LS, UE), _add(_c(6808321), _scale(4, LS), X(5)), _add(_c(816017), _scale(4, LS), LM, X(5)),
        _add(_c(16569), _scale(2, LM), X(6)), _add(_c(7025), _scale(2, LM), LKF, X(4)),
        _add(_c("0.32"), LM, _scale(2, LKF), X(2)),
        _add(_c(82839 * 3), _scale(2, LM), LKF, X(6)),
        _add(_c(34), LS, RK), _add(_c("3.74"), LS, UE), _add(_c(8670), LS, X(5)),
        _add(_c(6808160), _scale(4, LS), X(5)), _add(_c(816017), _scale(4, LS), LM, X(5)),
        # P_iso for the Q_A <= 2M(n+1)k!, Q_cmp <= 4M^2(n+1)k! and <= 5s calls
        _add(_maxlse(_add(_c(4), LM, LKF, X(1)), _add(_c(8), _scale(2, LM), LKF, X(1)), _add(_c(5), LS)), PISO),
    ]
    out = _maxlse(*terms)
    out["1"] += 1
    return out


def own_work_johnson_primitive() -> dict:
    """The same for a primitive Johnson node (pullback or EDL branch; ownwork.md §8.6, §8.7)."""
    X = lambda c: _vec(X=c)
    terms = [
        _add(_c(29070), X(5)), _add(_c(5948600), X(5)),
        _add(_c(34), LS, RT), _add(_c("3.74"), LS, UE),
        _add(_c(34 * 322), X(1), LS, _vec(Xy=1, y=1)),          # 34(280 + 42t) m^{t+1} <= 34*322 X m^{X+1}
        _add(_c(34), LS, X(1), _vec(**{"1": Fraction(513, 100)}), _vec(Xy=1)),
        _add(_c(6738528), _scale(4, LS), X(5)), _add(_c(8602), LS, X(5)), _add(_c(29071), X(5)),
        _add(LS, PISO),
    ]
    out = _maxlse(*terms)
    out["1"] += 1
    return out


def _basis_value(v: dict, X: Fraction, y: Fraction) -> Interval:
    """Upper end of the combination at (X, y)."""
    X, y = Fraction(X), Fraction(y)
    vals = {"Xy": Interval(X * y), "y2": Interval(y * y), "R": R_fun(y), "yly": rnd(y * L(y)),
            "y": Interval(y), "ly2": L(y + 2), "X": Interval(X), "XlX": rnd((X + 3) * L(X + 3)),
            "1": Interval(1)}
    tot = Interval(0)
    for b in BASIS:
        if v[b]:
            tot = tot + v[b] * vals[b]
    return rnd(tot)


def check_own_work() -> dict:
    """(W1)-(W5) of PROOF.md §12."""
    out = {}
    # (W1) brute force, giant, strong Luks, Cameron: E(X) >= 5.5 X^2 + 60 X >= 23.79 + 7X + 1 for X >= 1
    if not (Fraction(11, 2) + 60 - Fraction(2479, 100) - 7) > 0:
        raise CheckFailed("W1")
    # (W2) imprimitive Johnson node: Phi >= A y^3 + B y^2 X + y rho(y) + 2 y^2 + E(X), X >= y + 1
    v = own_work_johnson_imprimitive()
    out["W2_coeffs"] = {b: float(c) for b, c in v.items() if c}
    if not (B * Y0 - v["Xy"]).lo > 0:
        raise CheckFailed(f"W2: Xy coefficient {float(v['Xy'])} > B Y0")
    qy = Fraction(0)

    def w2y(y):
        P = rnd(A * y ** 3 + 2 * y * y + y * rho(y))
        N = rnd(v["y2"] * y * y + v["R"] * R_fun(y) + v["yly"] * rnd(y * L(y)) + v["y"] * y
                + v["ly2"] * L(y + 2) + qy)
        return P, N

    out["W2y"] = verify_PN("W2y", w2y, Y0, Y1)
    tail_dominated("W2y", [(Interval(A.lo), Fraction(3), Fraction(0)), (rnd(-v["y2"] - Interval(0)), Fraction(2), Fraction(0)),
                           (rnd(Interval(-v["R"] * Fraction(58, 10))), Fraction(1), Fraction(2)),
                           (rnd(Interval(-v["R"] * Fraction(61, 10) - v["yly"])), Fraction(1), Fraction(1)),
                           (rnd(Interval(-v["R"] * Fraction(103, 10) - v["y"] - v["ly2"])), Fraction(1), Fraction(0)),
                           (Interval(-v["R"] * Fraction(35, 10)), Fraction(0), Fraction(2)),
                           (Interval(-v["R"] * 6), Fraction(0), Fraction(1)), (Interval(-v["R"] * 9 - 2 * v["ly2"]), Fraction(0), Fraction(0))],
                   Y1)
    # X-part: E(X) >= 5.5 X^2 + 60 X  >=  c_X X + c_XlX (X + 3) log2(X + 3) + c_1 for X >= Y0 + 1

    def w2x(X):
        P = Interval(Fraction(11, 2) * X * X + 60 * X)
        N = rnd(v["X"] * X + v["XlX"] * rnd((X + 3) * L(X + 3)) + v["1"])
        return P, N

    out["W2x"] = verify_PN("W2x", w2x, Y0 + 1, X1)
    tail_dominated("W2x", [(Interval(Fraction(11, 2)), Fraction(2), Fraction(0)),
                           (Interval(-2 * v["XlX"]), Fraction(1), Fraction(1)),
                           (Interval(-v["X"] - 6 * v["XlX"] - 60), Fraction(1), Fraction(0)),
                           (Interval(-v["1"] - 6 * v["XlX"]), Fraction(0), Fraction(0))], X1)
    # (W3) primitive Johnson node: Phi >= T(X, y, X) + E(X) with X >= 2y - ZDEF
    u = own_work_johnson_primitive()
    out["W3_coeffs"] = {b: float(c) for b, c in u.items() if c}
    if u["XlX"] or u["R"] > 4 or u["Xy"] > 10:
        raise CheckFailed("W3 shape")
    # slope in X: A y^2 + B X y + (B/2) y^2 + rho(y) + 4X + e(X) >= c_Xy y + c_X, since X >= y and
    # B y >= c_Xy fails only below c_Xy / B; use B X y >= B (2y - ZDEF) y

    def w3slope(y):
        P = rnd(A * y * y + B * (2 * y - ZDEF) * y + 60)
        N = rnd(u["Xy"] * y + u["X"])
        return P, N

    out["W3slope"] = verify_PN("W3slope", w3slope, Y0, Y1)
    tail_dominated("W3slope", [(Interval(A.lo + 2 * B.lo), Fraction(2), Fraction(0)),
                               (Interval(-u["Xy"]) - B * ZDEF, Fraction(1), Fraction(0)),
                               (Interval(-u["X"] + 60), Fraction(0), Fraction(0))], Y1)

    def w3(y):
        y = Fraction(y)
        Xp = 2 * y - ZDEF
        Elo = E_upper(Xp, 16).lo
        P = rnd(T_level(Xp, y, Xp) + Elo)
        N = _basis_value(u, Xp, y)
        return P, N

    out["W3"] = verify_PN("W3", w3, Y0, Fraction(64))
    # tail y >= 64 (Lemma 11.2): X = 2y - ZDEF lies in [1.98 y, 2y], so T(X, y, X) >= A X y^2 +
    # (B/2) X^2 y >= (1.98 A + 1.98^2 B/2) y^3, while the combination is at most
    # 2 c_Xy y^2 + c_y2 y^2 + c_R R(y) + c_yly y log y + (c_y + 2 c_X) y + c_ly2 (log y + 1) + c_1
    lead = rnd(A * Fraction(198, 100) + B / 2 * Fraction(198, 100) ** 2)
    terms = [(lead, Fraction(3), Fraction(0)),
             (Interval(-2 * u["Xy"] - u["y2"]), Fraction(2), Fraction(0)),
             (Interval(-u["R"] * Fraction(58, 10)), Fraction(1), Fraction(2)),
             (Interval(-u["R"] * Fraction(61, 10) - u["yly"]), Fraction(1), Fraction(1)),
             (Interval(-u["R"] * Fraction(103, 10) - u["y"] - 2 * u["X"]), Fraction(1), Fraction(0)),
             (Interval(-u["R"] * Fraction(35, 10)), Fraction(0), Fraction(2)),
             (Interval(-u["R"] * 6 - u["ly2"]), Fraction(0), Fraction(1)),
             (Interval(-u["R"] * 9 - u["ly2"] - u["1"]), Fraction(0), Fraction(0))]
    tail_dominated("W3", terms, Fraction(64))
    # (W4) small Gamma: T(g, g, X) + E(X) >= log2 m! + 23.79 + 7X + 1 at X = x_min(m)
    cnt = 0
    for mg in range(6, 4097):
        g = L(Fraction(mg)).lo
        Xa = x_min_small_gamma(mg)
        lhs = T_level(g, g, Xa) + Fraction(11, 2) * Xa * Xa + 60 * Xa
        if not (lhs - log2_factorial(mg) - Fraction(2479, 100) - 7 * Xa).lo >= 0:
            raise CheckFailed(f"W4 at {mg}")
        cnt += 1
    ma = 4097
    while ma <= (1 << 17):
        mb = min(1 << 17, ma + max(1, ma // 256))
        ga = L(Fraction(ma)).lo
        Xa = x_min_small_gamma(ma)
        Xb = x_min_small_gamma(mb)
        lhs = T_level(ga, ga, Xa) + Fraction(11, 2) * Xa * Xa + 60 * Xa
        if not (lhs - log2_factorial_upper(mb).hi - Fraction(2479, 100) - 7 * Xb).lo >= 0:
            raise CheckFailed(f"W4 on [{ma}, {mb}]")
        cnt += 1
        ma = mb + 1
    out["W4"] = cnt
    return out


# ------------------------------------------------------------ the bound U(X) and a(b)

U0 = Fraction(10)       # PROOF.md §13: covers the polynomial terms of the root call (Part III)


def _U_terms_upper(x: Fraction, Ex: Fraction, graph: bool) -> Fraction:
    """Upper end of U(x) (or U_GI(x)) given an upper bound Ex of E at x (resp. at 2x - 1)."""
    if graph:
        z = 2 * x - 1
        v = F(z, x, z) + z * rho(max(x, Fraction(1))) + C * z * z
    else:
        v = BSTAR * x ** 3 + x * rho(max(x, Fraction(1))) + C * x * x
    return rnd(v).hi + Ex + U0


def _excess_tail(b: Fraction, x1: Fraction, graph: bool) -> None:
    """b x^3 - U(x) >= 0 for x >= x1 (Lemma 13.1).  Strings: E(x) <= x e(x) <= 3 x^3/log^2 x
    + 11 x^2 + 60 x.  Graphs: U_GI(x) <= (2A + 3B) x^3 + Z rho(x) + 2 Z^2 + E(Z) + U0 (Lemma 13.3),
    and with Z = 2x - 1 <= 2x, log2(Z + 4) >= log2 x: Z rho(x) <= 10 x^2 l^2 + 6 x^2 l + 24 x^2,
    2 Z^2 <= 8 x^2, E(Z) <= Z e(Z) <= 24 x^3/log^2 x + 44 x^2 + 120 x."""
    if graph:
        lead = rnd(b - BGI)
        terms = [(lead, Fraction(3), Fraction(0)), (Interval(Fraction(-24)), Fraction(3), Fraction(-2)),
                 (Interval(Fraction(-10)), Fraction(2), Fraction(2)), (Interval(Fraction(-6)), Fraction(2), Fraction(1)),
                 (Interval(Fraction(-24 - 8 - 44)), Fraction(2), Fraction(0)), (Interval(Fraction(-120)), Fraction(1), Fraction(0)),
                 (Interval(-U0), Fraction(0), Fraction(0))]
    else:
        lead = rnd(b - BSTAR)
        terms = [(lead, Fraction(3), Fraction(0)), (Interval(Fraction(-3)), Fraction(3), Fraction(-2)),
                 (Interval(Fraction(-5)), Fraction(2), Fraction(2)), (Interval(Fraction(-3)), Fraction(2), Fraction(1)),
                 (Interval(Fraction(-12 - 2 - 11)), Fraction(2), Fraction(0)), (Interval(Fraction(-60)), Fraction(1), Fraction(0)),
                 (Interval(-U0), Fraction(0), Fraction(0))]
    tail_dominated("excess", terms, x1)


def log2_a_upper(b: Fraction, graph: bool = False, ratio: Fraction = Fraction(10001, 10000),
                 x1: Optional[Fraction] = None) -> Tuple[Fraction, Fraction]:
    """An exact upper bound of max_{x >= 0} (U(x) - b x^3) (resp. with U_GI, x = log2 v >= 1):
    on [x_j, x_{j+1}] the excess is at most U(x_{j+1}) - b x_j^3, with E(x_{j+1}) bounded by the
    upper sum of e over the grid (e nondecreasing); beyond x1 the excess is negative
    (``_excess_tail``).  Returns (bound, argmax grid point)."""
    b = Fraction(b)
    lead = BGI if graph else BSTAR
    if not (b - lead).lo > 0:
        raise ValueError("b must exceed the leading constant")
    if x1 is None:
        x1 = _tail_start(b, graph)
    x = Fraction(1) if graph else Fraction(0)
    zprev = 2 * x - 1 if graph else x
    Ez = Fraction(0)          # upper bound of E at the current argument (E(1) for graphs at x = 1)
    if graph:
        Ez = e_fun(Fraction(1)).hi
    best = _U_terms_upper(x, Ez, graph) if graph else U0
    arg = x
    h0 = Fraction(1, 64)
    while x < x1:
        nx = max(x + h0, _up(x * ratio, 30))
        z = 2 * nx - 1 if graph else nx
        Ez += (z - zprev) * e_fun(z).hi
        zprev = z
        v = _U_terms_upper(nx, Ez, graph) - (b * x ** 3)
        if v > best:
            best, arg = v, x
        x = nx
    return best, arg


# ------------------------------------------------------------ the exact value of a(b)
#
# PROOF.md §13.3.  For b > b* the smallest a with 2^{U(log2 n)} <= a 2^{b log2^3 n} for every
# integer n >= 1 is a(b) = 2^{M(b)}, M(b) = max_n f(log2 n), f(x) = U(x) - b x^3 (for graphs
# U_GI and v >= 2).  ``log2_a_bracket`` returns exact rationals lo <= M(b) <= hi:
#   lo is f at explicit integers n, evaluated with a lower bound of E;
#   hi bounds f on every cell of a partition of [x0, x1] (beyond x1 f < 0, ``_excess_tail``).
# f = P - N with P, N nondecreasing (Lemma 13.3), so on a cell [s, t]
#   f <= P(t) - N(s)                                        (monotone bound)
#   f <= f(m) + (t - s)/2 * max(P'(t) - N'(s), N'(t) - P'(s))  (mean value bound, m = (s+t)/2)
# because P' and N' are nondecreasing too.  E is bracketed by the midpoint and trapezoid sums
# of e, which bound the integral from below and above because e is convex (Lemma 13.2).


def check_e_convex() -> None:
    """The numerical facts of Lemma 13.2 (e is convex on [0, oo)): 8/sqrt(3) <= 4.62 <= e^3 - 4,
    and 8.62 ln 8.62 > 4 * 4.62."""
    if not Fraction(64, 3) <= Fraction(462, 100) ** 2:
        raise CheckFailed("8/sqrt(3) > 4.62")
    if not (L(Fraction(862, 100)) * LN2).hi <= 3:
        raise CheckFailed("ln 8.62 > 3")
    if not (Fraction(862, 100) * L(Fraction(862, 100)) * LN2).lo > Fraction(1848, 100):
        raise CheckFailed("8.62 ln 8.62 <= 18.48")


ALPHA_I = Fraction(117, 100)    # I(X) <= X^3/(3 L^2) + ALPHA_I X^3/(3 L^3), L = log2(X + 4) (Lemma 4.2)


def check_I_bound() -> None:
    """Lemma 4.2: with t = X + 4 and kappa = (3 ln 2 / 2) ALPHA_I,
    h(t) = (kappa - 1) t ln t + 4 ln t - kappa t + 4 kappa >= 0 for t >= 4: on [4, 512] by bisection
    (P = (kappa - 1) t ln t + 4 ln t + 4 kappa and N = kappa t are nondecreasing), and beyond 512
    because (kappa - 1) ln 512 >= kappa."""
    kappa = rnd(3 * LN2 * ALPHA_I / 2, 60)
    if not (kappa - 1).lo > 0:
        raise CheckFailed("kappa <= 1")

    def PN(t: Fraction) -> Tuple[Interval, Interval]:
        lt = rnd(L(t) * LN2)
        return rnd((kappa - 1) * t * lt + 4 * lt + 4 * kappa), rnd(kappa * t)

    verify_PN("I-bound", PN, Fraction(4), Fraction(512))
    if not ((kappa - 1) * L(Fraction(512)) * LN2 - kappa).lo >= 0:
        raise CheckFailed("I-bound: tail from t = 512")


AG = rnd(A + 5 * B / 2, 60)     # U_GI(V) = (2A + 3B) V^3 - (A + 5B/2) V^2 + B V / 2 + ... (Lemma 13.3)


def _poly(x: Fraction, graph: bool) -> Tuple[Interval, Interval]:
    """The part of P without E(Z) + U0, and its derivative (Lemma 13.3):
    strings  x rho(max(x, 1)) + C x^2;   graphs  B x / 2 + Z rho(x) + C Z^2,  Z = 2x - 1."""
    if graph:
        z = 2 * x - 1
        l = L(x)
        r = RA * x * l * l + RB * x * l + RC * x
        rp = RA * l * l + (2 * RA * INV_LN2 + RB) * l + RB * INV_LN2 + RC
        return rnd(B * x / 2 + z * r + C * z * z), rnd(B / 2 + 2 * r + z * rp + 4 * C * z)
    if x < 1:                       # rho(1) = RC; the left derivative at 1 is below the right one
        return rnd(RC * x + C * x * x), rnd(RC + 2 * C * x)
    l = L(x)
    p = RA * x * x * l * l + RB * x * x * l + RC * x * x + C * x * x
    dp = (2 * RA * x * l * l + (2 * RA * INV_LN2 + 2 * RB) * x * l + (RB * INV_LN2 + 2 * RC) * x
          + 2 * C * x)
    return rnd(p), rnd(dp)


def _N(x: Fraction, eps: Interval, graph: bool) -> Tuple[Interval, Interval]:
    """N and N': strings (b - b*) x^3;  graphs (b - 2A - 3B) x^3 + (A + 5B/2) x^2."""
    if graph:
        return rnd(eps * x ** 3 + AG * x * x), rnd(3 * eps * x * x + 2 * AG * x)
    return rnd(eps * x ** 3), rnd(3 * eps * x * x)


_GRIDS: dict = {}


def _grid(graph: bool, xmax: Fraction, ratio: Fraction = Fraction(501, 500),
          h0: Fraction = Fraction(1, 64)) -> dict:
    """Grid x_0 < x_1 < ... reaching xmax, with Z_j = Z(x_j), e(Z_j) and E_lo(Z_j) <= E(Z_j) <= E_hi(Z_j)
    (midpoint and trapezoid sums of e over the grid of Z, Lemma 13.2).  Independent of b; cached."""
    g = _GRIDS.get((graph, ratio, h0))
    if g is None:
        if graph:
            # E(1) from 64 cells of [0, 1]
            lo = hi = Fraction(0)
            prev = e_fun(Fraction(0))
            for j in range(64):
                u0, u1 = Fraction(j, 64), Fraction(j + 1, 64)
                cur = e_fun(u1)
                lo += (u1 - u0) * e_fun((u0 + u1) / 2).lo
                hi += (u1 - u0) * (prev.hi + cur.hi) / 2
                prev = cur
            g = {"x": [Fraction(1)], "z": [Fraction(1)], "e": [prev], "Elo": [lo], "Ehi": [hi]}
        else:
            g = {"x": [Fraction(0)], "z": [Fraction(0)], "e": [e_fun(Fraction(0))],
                 "Elo": [Fraction(0)], "Ehi": [Fraction(0)]}
        _GRIDS[(graph, ratio, h0)] = g
    xs, zs, es, los, his = g["x"], g["z"], g["e"], g["Elo"], g["Ehi"]
    while xs[-1] < xmax:
        x, z = xs[-1], zs[-1]
        nx = max(x + h0, _up(x * ratio, 30))
        nz = 2 * nx - 1 if graph else nx
        ez = e_fun(nz)
        los.append(_dn(los[-1] + (nz - z) * e_fun((z + nz) / 2).lo))
        his.append(_up(his[-1] + (nz - z) * (es[-1].hi + ez.hi) / 2))
        xs.append(nx)
        zs.append(nz)
        es.append(ez)
    return g


def _E_at(g: dict, z: Fraction) -> Tuple[Fraction, Fraction, Interval]:
    """(lower, upper bound of E(z), e(z)) from the grid point below z and one more midpoint or
    trapezoid cell (Lemma 13.2)."""
    j = bisect_right(g["z"], z) - 1
    if j < 0:
        raise ValueError("below the grid")
    zj = g["z"][j]
    if z == zj:
        return g["Elo"][j], g["Ehi"][j], g["e"][j]
    ez = e_fun(z)
    lo = g["Elo"][j] + (z - zj) * e_fun((zj + z) / 2).lo
    hi = g["Ehi"][j] + (z - zj) * (g["e"][j].hi + ez.hi) / 2
    return lo, hi, ez


_P_CACHE: dict = {}


def _P_at(g: dict, x: Fraction, graph: bool) -> Tuple[Fraction, Fraction, Fraction, Fraction]:
    """(P_lo, P_hi, P'_lo, P'_hi) at x; P does not depend on b, so the values are cached."""
    r = _P_CACHE.get((graph, x))
    if r is None:
        z = 2 * x - 1 if graph else x
        elo, ehi, ez = _E_at(g, z)
        p, dp = _poly(x, graph)
        zp = 2 if graph else 1
        r = (p.lo + elo + U0, p.hi + ehi + U0, dp.lo + zp * ez.lo, dp.hi + zp * ez.hi)
        _P_CACHE[(graph, x)] = r
    return r


def _tail_start(b: Fraction, graph: bool) -> Fraction:
    x1 = Fraction(16)
    while True:
        try:
            _excess_tail(b, x1, graph)
            return x1
        except CheckFailed:
            x1 *= 2


def log2_a_bracket(b: Fraction, graph: bool = False, rel_tol: Fraction = Fraction(1, 10 ** 7)
                   ) -> Tuple[Fraction, Fraction, Fraction]:
    """Exact rationals lo <= log2 a(b) <= hi (PROOF.md §13.3, Lemma 13.4), normally with
    hi - lo = max(1/100, rel_tol * lo, twice the width of the bracket of E at the maximum);
    and log2 of the integer n at which lo is attained."""
    b = Fraction(b)
    lead = BGI if graph else BSTAR
    eps = rnd(b - lead, 60)
    if not eps.lo > 0:
        raise ValueError("b must exceed the leading constant")
    x1 = _tail_start(b, graph)
    g = _grid(graph, x1)
    nmin = 2 if graph else 1

    def pt(x: Fraction):
        return _P_at(g, x, graph)

    def f_int(n: int) -> Tuple[Fraction, Fraction]:
        """lower and upper bound of f(log2 n)."""
        if n & (n - 1) == 0:
            X = Interval(Fraction(n.bit_length() - 1))
        else:
            X = L(Fraction(n))
        lo = pt(X.lo)[0] - _N(X.hi, eps, graph)[0].hi
        hi = pt(X.hi)[1] - _N(X.lo, eps, graph)[0].lo
        return lo, hi

    best = {"lo": None, "x": None}

    def try_int(n: int) -> Fraction:
        lo, hi = f_int(n)
        if best["lo"] is None or lo > best["lo"]:
            best["lo"], best["x"] = lo, Fraction(n)
        return hi

    def near(x: Fraction) -> List[int]:
        """integers n with log2 n just below and just above x."""
        if x < 30:
            n = int(2.0 ** float(x))
            return [k for k in (n - 1, n, n + 1, n + 2) if k >= nmin]
        base = int(floor(x)) - 20
        k = int(2.0 ** float(x - base))
        return [(k + d) << base for d in (0, 1)]

    try_int(nmin)
    # the best grid point locates the maximum
    xs = g["x"]
    m = next(j for j in range(len(xs)) if xs[j] >= x1)
    jb = max(range(m + 1), key=lambda j: pt(xs[j])[0] - _N(xs[j], eps, graph)[0].hi)
    for n in near(xs[jb]):
        try_int(n)
    # the bracket of E is a floor for the precision: tol covers twice its width at the maximum
    tol = max(Fraction(1, 100), abs(best["lo"]) * rel_tol, 2 * (g["Ehi"][jb] - g["Elo"][jb]))
    hi_final = best["lo"] + tol          # raised to the bound of every cell that is not pruned
    stack = [(xs[j], xs[j + 1]) for j in range(m)]
    while stack:
        s, t = stack.pop()
        thr = best["lo"] + tol
        Ps, Pt = pt(s), pt(t)
        Ns, Nt = _N(s, eps, graph), _N(t, eps, graph)
        ub = Pt[1] - Ns[0].lo
        if ub <= thr:
            continue
        if t <= 40 and 2.0 ** float(t) - 2.0 ** float(s) <= 48:
            # few integers: evaluate f at each of them (a superset of those with log2 n in [s, t])
            lo_n = max(nmin, int(2.0 ** float(s)) - 1)
            while lo_n > nmin and not L(Fraction(lo_n - 1)).hi < s:
                lo_n -= 1
            hi_n = int(2.0 ** float(t)) + 1
            while not L(Fraction(hi_n + 1)).lo > t:
                hi_n += 1
            for n in range(lo_n, hi_n + 1):
                hi_final = max(hi_final, try_int(n))
            continue
        mid = (s + t) / 2
        Pm, Nm = pt(mid), _N(mid, eps, graph)
        if Pm[0] - Nm[0].hi > thr:
            for n in near(mid):
                try_int(n)
        D = max(Pt[3] - Ns[1].lo, Nt[1].hi - Ps[2], Fraction(0))
        ub = min(ub, Pm[1] - Nm[0].lo + (t - s) / 2 * D)
        if ub <= best["lo"] + tol:
            continue
        if t - s <= max(Fraction(1, 1 << 30), s / (1 << 24)):
            hi_final = max(hi_final, ub)
            continue
        stack.append((s, mid))
        stack.append((mid, t))
    return best["lo"], max(hi_final, best["lo"] + tol), L(best["x"]).lo if best["x"] > 1 else Fraction(0)


# ------------------------------------------------------------ the table of a(b)

B_TABLE_SI = [Fraction(27, 10), Fraction(28, 10), Fraction(3), Fraction(35, 10), Fraction(4), Fraction(5),
              Fraction(6), Fraction(8), Fraction(10), Fraction(20)]
B_TABLE_GI = [Fraction(65, 10), Fraction(7), Fraction(8), Fraction(10), Fraction(15), Fraction(20), Fraction(30)]


def a_table(verbose: bool = True, which: Sequence[bool] = (False, True)) -> dict:
    """Exact brackets lo <= log2 a(b) <= hi for the b of the tables in PROOF.md §13.3."""
    out = {}
    for graph, bs in ((False, B_TABLE_SI), (True, B_TABLE_GI)):
        if graph not in which:
            continue
        for b in bs:
            lo, hi, arg = log2_a_bracket(b, graph=graph)
            out[(graph, b)] = (lo, hi, arg)
            if verbose:
                print(f"{'GI' if graph else 'SI'} b = {float(b):5.2f}: {_dec(lo, False)} <= log2 a(b) <= "
                      f"{_dec(hi, True)} (maximum at {'v' if graph else 'n'} = 2^{float(arg):.6g})", flush=True)
    return out


def _dec(q: Fraction, up: bool, digits: int = 2) -> str:
    """q rounded down (or up) to the given number of decimals."""
    s = 10 ** digits
    k = -((-q.numerator * s) // q.denominator) if up else (q.numerator * s) // q.denominator
    sign = "-" if k < 0 else ""
    k = abs(k)
    return f"{sign}{k // s}.{k % s:0{digits}d}"


# ------------------------------------------------------------ driver

Y1 = Fraction(1 << 10)        # end of the bisection range for the y-inequalities
X1 = Fraction(1 << 12)        # ... and for the X-inequalities


def check_constants() -> None:
    if not L(Fraction(90)).lo >= Y0:
        raise CheckFailed("Y0 > log2 90")
    if not (2 * B * DELTA - 1).width() < Fraction(1, 1 << 50):
        raise CheckFailed("2 B delta != 1")
    if not ((3 * A + B) * DELTA - BETA).width() < Fraction(1, 1 << 50):
        raise CheckFailed("(3A + B) delta != beta")
    if not (Q1_MARGIN + Q2_MARGIN - CC0).lo >= 0:
        raise CheckFailed("Q1 + Q2 margins below CC0")
    # 2 y - z_min(y) = 1 - log2(1 - 2^-y) <= 1 - log2(1 - 1/90) for y >= log2 90
    if not (1 - L(Fraction(89, 90))).hi <= ZDEF:
        raise CheckFailed("ZDEF")
    # w_J <= log2(1 + 2^((y+1)/2)) <= (y+1)/2 + 2^(-(y+1)/2)/ln 2, and 2^(-(Y0+1)/2) <= 3/40
    # because log2((40/3)^2) <= Y0 + 1
    if not (2 * L(Fraction(40, 3))).hi <= Y0 + 1:
        raise CheckFailed("2^(-(Y0+1)/2) > 3/40")
    if not (Fraction(1, 2) + Fraction(3, 40) * INV_LN2).hi <= OMEGA_J:
        raise CheckFailed("OMEGA_J")


def run_all(verbose: bool = True) -> dict:
    out = {}

    def log(msg):
        if verbose:
            print(msg, flush=True)

    check_constants()
    check_e_convex()
    check_I_bound()
    log(f"delta = {DELTA!r}\nbeta = {BETA!r}\nA = {A!r}\nB = {B!r}\nb* = A + B = {BSTAR!r}\n2A + 3B = {BGI!r}")
    out["Q1"] = verify_PN("Q1", q1_PN, Y0, Y1)
    q1_tail(Y1)
    out["Q2"] = verify_PN("Q2", q2_PN, Y0 + 1, X1)
    q2_tail(X1)
    out["Q3"] = verify_PN("Q3", q3_PN, Y0, Y1)
    q3_tail(Y1)
    out["Q4"] = verify_PN("Q4", q4_PN, Y0, Y1)
    q4_tail(Y1)
    out["Q5"] = verify_PN("Q5", q5_PN, Y0, Y1)
    q5_tail(Y1)
    brk = integer_breaks(Y0 + 1, X1)
    out["Q6"] = verify_PN("Q6", q6_PN, Y0 + 1, X1, breaks=brk)
    q67_tail(X1, False)
    out["Q7"] = verify_PN("Q7", q7_PN, Y0 + 1, X1, breaks=brk)
    q67_tail(X1, True)
    log(f"Q1-Q7 verified: {out}")
    out["Q8"] = check_q8()
    check_q9()
    log(f"Q8, Q9 verified ({out['Q8']} cases)")
    out["W"] = check_own_work()
    log(f"W1-W4 verified: {out['W']}")
    return out


if __name__ == "__main__":
    import sys
    import time
    t0 = time.time()
    run_all()
    print(f"all checks passed in {time.time() - t0:.1f} s")
    if "--table" in sys.argv:
        a_table()
