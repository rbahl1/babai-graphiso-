"""The proved operation bound (``PROOF.md``, Theorems A and B), for numerical use.

``string_isomorphism`` on a domain of ``n`` points executes at most ``2^{U(log2 n)}``
operations, and ``graph_isomorphism`` on ``v`` vertices at most ``2^{U_GI(log2 v)}``, with

    U(X)    = b* X^3 + X rho(X) + 2 X^2 + E(X) + U0,
    U_GI(V) = F(2V - 1, V, 2V - 1) + (2V - 1) rho(V) + 2 (2V - 1)^2 + E(2V - 1) + U0,

where ``b* = (S2 + delta)/(3 delta^2)`` and ``rho``, ``E``, ``F`` are the functions of
``timebound`` (PROOF.md §4, §6).  These functions use floating point and are meant for
tables and plots; the proof's numerical steps are the exact checks in ``timebound``.

For ``b > b*`` the bound has the form ``a(b) * 2^{b (log2 n)^3}`` with
``log2 a(b) = max_{n >= 1} (U(log2 n) - b log2^3 n)``; ``log2_a`` estimates it in floating point
(over real X), and ``timebound.log2_a_bracket`` proves lower and upper bounds (PROOF.md §13.3).
"""

from __future__ import annotations

from math import floor, log2, pi

DELTA = log2(1.5)
S2 = 0.5 + pi * pi / 6
BETA = S2 / DELTA
B = 1 / (2 * DELTA)
A = (BETA - 0.5) / (3 * DELTA)
BSTAR = A + B              # 2.6593095...
BSTAR_GI = 2 * A + 3 * B   # 6.1733746...
C = 2.0
U0 = 10.0                  # PROOF.md §13 (timebound.U0)


def k_paper(n: int) -> int:
    """The test-set size of Local Certificates, max(9, floor(log2 n) + 3) (main.Params.k_paper)."""
    return max(9, max(n, 1).bit_length() + 2)


def rho(w: float) -> float:
    l = log2(w)
    return 5 * w * l * l + 3 * w * l + 12 * w


def e(u: float) -> float:
    return 3 * u * u / log2(u + 4) ** 2 + 11 * u + 60


def E(X: float, steps: int = 400) -> float:
    """An upper Riemann sum of int_0^X e (e is nondecreasing)."""
    if X <= 0:
        return 0.0
    h = X / steps
    return h * sum(e(h * j) for j in range(1, steps + 1))


def F(z: float, w: float, Y: float) -> float:
    return z * (A * w * w + B * w * (Y - (z - w) / 2))


def U(X: float) -> float:
    return BSTAR * X ** 3 + X * rho(max(X, 1.0)) + C * X * X + E(X) + U0


def U_GI(V: float) -> float:
    Z = 2 * V - 1
    return F(Z, V, Z) + Z * rho(max(V, 1.0)) + C * Z * Z + E(Z) + U0


def log2_time_bound(n: int) -> float:
    """log2 of the proved bound on the operations of string_isomorphism on n points."""
    return U(log2(n)) if n >= 2 else U0


def log2_time_bound_graph(v: int) -> float:
    """log2 of the proved bound on the operations of graph_isomorphism on v vertices."""
    return U_GI(log2(v)) if v >= 2 else U0


def log2_a(b: float, graph: bool = False, x_max: float = 2.0 ** 15, steps: int = 400000) -> float:
    """The maximum of U(X) - b X^3 (resp. U_GI(V) - b V^3) on a grid of [0, x_max], with E summed
    incrementally (upper sums); b must exceed the leading constant.  The proved two-sided
    bounds of the table in PROOF.md §13.3 are computed by ``timebound.log2_a_bracket``."""
    lead = BSTAR_GI if graph else BSTAR
    if b <= lead:
        raise ValueError("b must exceed the leading constant (a(b) is infinite at and below it)")
    h = x_max / steps
    best = U0
    Ez = 0.0          # E at the current argument (X, or Z = 2V - 1 for graphs)
    zprev = 0.0
    for j in range(1, steps + 1):
        x = h * j
        z = 2 * x - 1 if graph else x
        if z > zprev:
            Ez += (z - zprev) * e(z)
            zprev = z
        if graph:
            if x < 1:
                continue
            u = F(z, x, z) + z * rho(x) + C * z * z + Ez + U0
        else:
            u = BSTAR * x ** 3 + x * rho(max(x, 1.0)) + C * x * x + Ez + U0
        v = u - b * x ** 3
        if v > best:
            best = v
    return best
