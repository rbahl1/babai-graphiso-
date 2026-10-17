"""The numerical part of the time bound (PROOF.md Part II, §11 and §13): the identities
between the constants, the exact checks of the reduced inequalities, and the table of a(b)."""
from fractions import Fraction
from math import log2, pi

import pytest

from babai_gi import bounds, timebound as tb


def test_constant_identities():
    d = log2(1.5)
    s2 = 0.5 + pi * pi / 6
    assert abs(bounds.B * 2 * d - 1) < 1e-12
    assert abs((3 * bounds.A + bounds.B) * d - s2 / d) < 1e-12
    assert abs(bounds.BSTAR - (s2 + d) / (3 * d * d)) < 1e-12
    assert abs(bounds.BSTAR - 2.6593095) < 1e-6
    assert abs(bounds.BSTAR_GI - 6.1733746) < 1e-6
    assert abs(float(tb.BSTAR.lo) - bounds.BSTAR) < 1e-12 and abs(float(tb.BGI.lo) - bounds.BSTAR_GI) < 1e-12
    assert bounds.U0 == float(tb.U0)
    tb.check_constants()


def test_all_reduced_inequalities():
    """(Q1)-(Q9) with exact interval arithmetic: the numerical steps of the proof."""
    out = tb.run_all(verbose=False)
    assert set(out) >= {"Q1", "Q2", "Q3", "Q4", "Q5", "Q6", "Q7", "Q8"}


@pytest.mark.parametrize("b", [20, 10])
def test_a_of_b_exact_upper_bound_matches_float_estimate(b):
    exact, _ = tb.log2_a_upper(Fraction(b))
    approx = bounds.log2_a(float(b))
    assert approx <= float(exact) + 1e-6
    assert float(exact) <= approx * 1.05 + 10


@pytest.mark.parametrize("graph,b", [(False, 20), (True, 30)])
def test_a_of_b_exact_bracket(graph, b):
    """lo <= log2 a(b) <= hi (PROOF.md Lemma 13.4): tight, and below the coarse upper bound."""
    lo, hi, _ = tb.log2_a_bracket(Fraction(b), graph=graph)
    up, _ = tb.log2_a_upper(Fraction(b), graph=graph)
    assert lo <= hi <= up
    assert hi - lo <= Fraction(2, 100)


def test_e_convex_and_I_bound():
    """Lemma 13.2 (e is convex) and Lemma 4.2 (the closed-form bracket of I)."""
    tb.check_e_convex()
    tb.check_I_bound()


def test_a_is_infinite_at_the_leading_constant():
    with pytest.raises(ValueError):
        bounds.log2_a(bounds.BSTAR)
    with pytest.raises(ValueError):
        tb.log2_a_upper(Fraction(2))
    with pytest.raises(ValueError):
        tb.log2_a_bracket(Fraction(6), graph=True)
    # U(X) - b* X^3 is unbounded: it exceeds every fixed value for large X
    vals = [bounds.U(x) - bounds.BSTAR * x ** 3 for x in (10.0, 100.0, 1000.0)]
    assert vals[0] < vals[1] < vals[2]


def test_time_bound_is_monotone_and_quasipolynomial():
    prev = 0.0
    for n in (2, 3, 10, 100, 10 ** 4, 10 ** 8):
        v = bounds.log2_time_bound(n)
        assert v > prev
        prev = v
    x = 64.0
    assert bounds.log2_time_bound(2 ** 64) <= 3 * x ** 3 + 10 ** 6
