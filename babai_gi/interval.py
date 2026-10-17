"""Exact interval arithmetic for the verification of the time bound (``PROOF.md``).

An ``Interval`` has ``Fraction`` endpoints; every operation returns an interval that
contains every value of the operation on points of the operands.  ``log2``, ``ln``
and ``sqrt`` are computed with exact rational arithmetic and explicit remainder
bounds, so the results do not depend on floating point.  The constants of the
bound (log2(3/2), pi^2) are enclosed in intervals the same way.  This makes the
numerical steps of the proof (finitely many inequalities between explicit
functions) checks of exact statements.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Union

Num = Union[int, Fraction, "Interval"]

# 30 binary digits suffice everywhere the module is used; more cost time only
_PREC_BITS = 60


def _F(v) -> Fraction:
    return v if isinstance(v, Fraction) else Fraction(v)


class Interval:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = _F(lo)
        hi = lo if hi is None else _F(hi)
        if lo > hi:
            raise ValueError("empty interval")
        self.lo, self.hi = lo, hi

    @staticmethod
    def of(v: Num) -> "Interval":
        return v if isinstance(v, Interval) else Interval(v)

    # ---------------------------------------------------------- arithmetic
    def __add__(self, o: Num) -> "Interval":
        o = Interval.of(o)
        return Interval(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, o: Num) -> "Interval":
        return self + (-Interval.of(o))

    def __rsub__(self, o: Num) -> "Interval":
        return Interval.of(o) - self

    def __mul__(self, o: Num) -> "Interval":
        o = Interval.of(o)
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Interval(min(p), max(p))

    __rmul__ = __mul__

    def __truediv__(self, o: Num) -> "Interval":
        o = Interval.of(o)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError("interval contains 0")
        return self * Interval(1 / o.hi, 1 / o.lo)

    def __rtruediv__(self, o: Num) -> "Interval":
        return Interval.of(o) / self

    def __pow__(self, e: int) -> "Interval":
        if not isinstance(e, int) or e < 0:
            raise ValueError("integer exponent >= 0 only")
        if e == 0:
            return Interval(1)
        if e % 2 == 1 or self.lo >= 0:
            return Interval(min(self.lo ** e, self.hi ** e), max(self.lo ** e, self.hi ** e))
        if self.hi <= 0:
            return Interval(self.hi ** e, self.lo ** e)
        return Interval(0, max(self.lo ** e, self.hi ** e))

    # ---------------------------------------------------------- order
    def __le__(self, o: Num) -> bool:
        """True iff every point of self is <= every point of o."""
        return self.hi <= Interval.of(o).lo

    def __ge__(self, o: Num) -> bool:
        return self.lo >= Interval.of(o).hi

    def __lt__(self, o: Num) -> bool:
        return self.hi < Interval.of(o).lo

    def __gt__(self, o: Num) -> bool:
        return self.lo > Interval.of(o).hi

    def hull(self, o: Num) -> "Interval":
        o = Interval.of(o)
        return Interval(min(self.lo, o.lo), max(self.hi, o.hi))

    def width(self) -> Fraction:
        return self.hi - self.lo

    def __repr__(self) -> str:
        return f"[{float(self.lo):.12g}, {float(self.hi):.12g}]"


# ------------------------------------------------------------- functions

def _ln_point(q: Fraction, bits: int = _PREC_BITS) -> Interval:
    """An interval containing ln q for a rational q > 0.

    q = 2^e r with r in [1, 2); ln r = 2 artanh(u), u = (r - 1)/(r + 1) in [0, 1/3),
    artanh(u) = sum_{j>=0} u^{2j+1}/(2j+1), and the tail after N terms is at most
    u^{2N+1}/((2N+1)(1 - u^2))."""
    if q <= 0:
        raise ValueError("ln of a non-positive number")
    e = q.numerator.bit_length() - q.denominator.bit_length()
    r = q / Fraction(2) ** e
    while r >= 2:
        r /= 2
        e += 1
    while r < 1:
        r *= 2
        e -= 1
    u = (r - 1) / (r + 1)
    s = Fraction(0)
    term = u
    j = 0
    eps = Fraction(1, 2 ** bits)
    while True:
        s += term / (2 * j + 1)
        j += 1
        term = term * u * u
        tail = term / ((2 * j + 1) * (1 - u * u))
        if tail < eps:
            break
    ln_r = Interval(2 * s, 2 * (s + tail))
    return ln_r + e * LN2


def _ln2_enclosure() -> Interval:
    # ln 2 = 2 artanh(1/3)
    u = Fraction(1, 3)
    s = Fraction(0)
    term = u
    j = 0
    eps = Fraction(1, 2 ** (_PREC_BITS + 4))
    while True:
        s += term / (2 * j + 1)
        j += 1
        term = term * u * u
        tail = term / ((2 * j + 1) * (1 - u * u))
        if tail < eps:
            break
    return Interval(2 * s, 2 * (s + tail))


LN2 = _ln2_enclosure()


def ln(x: Num) -> Interval:
    """ln is increasing: the enclosure of [ln lo, ln hi]."""
    x = Interval.of(x)
    return Interval(_ln_point(x.lo).lo, _ln_point(x.hi).hi)


def log2(x: Num) -> Interval:
    x = Interval.of(x)
    lo = _ln_point(x.lo) / LN2
    hi = _ln_point(x.hi) / LN2
    return Interval(lo.lo, hi.hi)


def _sqrt_point(q: Fraction, bits: int = _PREC_BITS) -> Interval:
    if q < 0:
        raise ValueError("sqrt of a negative number")
    if q == 0:
        return Interval(0)
    # integer square root of q * 4^bits, exact bracketing
    scale = 4 ** bits
    num = q.numerator * scale
    den = q.denominator
    from math import isqrt
    lo = Fraction(isqrt(num // den), 2 ** bits)
    hi = Fraction(isqrt(num // den) + 1, 2 ** bits)
    # lo^2 <= floor(q 4^bits)/4^bits <= q and hi^2 > q
    while lo * lo > q:
        lo -= Fraction(1, 2 ** bits)
    while hi * hi < q:
        hi += Fraction(1, 2 ** bits)
    return Interval(lo, hi)


def sqrt(x: Num) -> Interval:
    x = Interval.of(x)
    return Interval(_sqrt_point(x.lo).lo, _sqrt_point(x.hi).hi)


def pow_real(x: Num, p: Fraction) -> Interval:
    """x^p for x > 0 and rational p, as exp(p ln x) bracketed through 2^(p log2 x):
    computed by repeated square roots for p with denominator a power of 2."""
    x = Interval.of(x)
    p = Fraction(p)
    den = p.denominator
    if den & (den - 1):
        raise ValueError("only exponents with a power-of-two denominator")
    k = den.bit_length() - 1
    r = x
    for _ in range(k):
        r = sqrt(r)
    num = p.numerator
    if num >= 0:
        return r ** num
    return Interval(1) / (r ** (-num))


def _arctan_enclosure(u: Fraction, bits: int = _PREC_BITS + 8) -> Interval:
    """arctan u = sum_j (-1)^j u^{2j+1}/(2j+1) for 0 < u < 1: the terms decrease and
    alternate in sign, so consecutive partial sums bracket the value."""
    s = Fraction(0)
    term = u
    j = 0
    eps = Fraction(1, 2 ** bits)
    while True:
        nxt = s + (term if j % 2 == 0 else -term) / (2 * j + 1)
        j += 1
        term = term * u * u
        if term / (2 * j + 1) < eps:
            other = nxt + (term if j % 2 == 0 else -term) / (2 * j + 1)
            return Interval(min(nxt, other), max(nxt, other))
        s = nxt


def _pi_squared_enclosure() -> Interval:
    """pi = 16 arctan(1/5) - 4 arctan(1/239) (Machin)."""
    pi = 16 * _arctan_enclosure(Fraction(1, 5)) - 4 * _arctan_enclosure(Fraction(1, 239))
    return pi * pi


PI2 = _pi_squared_enclosure()
LOG2_3_2 = log2(Fraction(3, 2))
