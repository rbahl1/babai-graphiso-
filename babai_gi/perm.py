"""Permutations of {0,...,n-1} as tuples, with Babai's right-action conventions.

Babai, Sec. 2.2: for sigma in S(Omega) and x in Omega we write x^sigma for the
image of x; products act on the right, x^{sigma tau} = (x^sigma)^tau.
A permutation p is a tuple with p[i] = i^p.  ``mul(p, q)`` is "p then q".

Strings (Babai Sec. 3.1, eq. (11)): x^tau(u^tau) = x(u).
"""

from __future__ import annotations

from typing import Iterable, Sequence, Tuple

Perm = Tuple[int, ...]


def identity(n: int) -> Perm:
    return _ident(n)


_ID_CACHE = {}


def _ident(n: int) -> Perm:
    r = _ID_CACHE.get(n)
    if r is None:
        r = tuple(range(n))
        _ID_CACHE[n] = r
    return r


def is_identity(p: Perm) -> bool:
    return p == _ident(len(p))


def mul(p: Perm, q: Perm) -> Perm:
    """Product "p then q": (p q)[i] = q[p[i]], so i^{pq} = (i^p)^q."""
    return tuple(map(q.__getitem__, p))


def mul_all(perms: Sequence[Perm], n: int) -> Perm:
    r = identity(n)
    for p in perms:
        r = mul(r, p)
    return r


def inv(p: Perm) -> Perm:
    r = [0] * len(p)
    for i, v in enumerate(p):
        r[v] = i
    return tuple(r)


def identity_perm(n: int) -> Perm:
    return _ident(n)


def conj(p: Perm, g: Perm) -> Perm:
    """g^{-1} p g (acts on images: (i^g)^{p^g} = (i^p)^g)."""
    return mul(mul(inv(g), p), g)


def from_cycles(n: int, cycles: Iterable[Sequence[int]]) -> Perm:
    r = list(range(n))
    for cyc in cycles:
        k = len(cyc)
        for i in range(k):
            r[cyc[i]] = cyc[(i + 1) % k]
    return tuple(r)


def cycles(p: Perm) -> list:
    seen = [False] * len(p)
    out = []
    for i in range(len(p)):
        if not seen[i] and p[i] != i:
            c = []
            j = i
            while not seen[j]:
                seen[j] = True
                c.append(j)
                j = p[j]
            out.append(c)
    return out


def parity(p: Perm) -> int:
    """0 for even, 1 for odd."""
    seen = [False] * len(p)
    par = 0
    for i in range(len(p)):
        if not seen[i]:
            j = i
            length = 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                length += 1
            par ^= (length - 1) & 1
    return par


def support(p: Perm) -> list:
    return [i for i, v in enumerate(p) if v != i]


def act_string(x: Sequence, p: Perm) -> tuple:
    """x^p with x^p(u^p) = x(u) (Babai eq. (11))."""
    r = [None] * len(x)
    for u, letter in enumerate(x):
        r[p[u]] = letter
    return tuple(r)


def act_set(S: Iterable[int], p: Perm) -> frozenset:
    return frozenset(p[s] for s in S)


def act_tuple(T: Sequence[int], p: Perm) -> tuple:
    return tuple(p[s] for s in T)


def restrict(p: Perm, points: Sequence[int], index: dict) -> Perm:
    """Restriction of p to an invariant set ``points`` (re-indexed by ``index``)."""
    return tuple(index[p[s]] for s in points)


def is_string_automorphism(x: Sequence, p: Perm) -> bool:
    for u, letter in enumerate(x):
        if x[p[u]] != letter:
            return False
    return True


def maps_string(x: Sequence, y: Sequence, p: Perm) -> bool:
    """True iff x^p = y, i.e. x(u) = y(u^p) for all u (Babai eq. (12))."""
    for u, letter in enumerate(x):
        if y[p[u]] != letter:
            return False
    return True


def sym_gens(points: Sequence[int], n: int) -> list:
    """Generators of Sym(points) inside S_n (a transposition and a cycle)."""
    pts = list(points)
    if len(pts) < 2:
        return []
    out = [from_cycles(n, [pts[:2]])]
    if len(pts) > 2:
        out.append(from_cycles(n, [pts]))
    return out


def alt_gens(points: Sequence[int], n: int) -> list:
    """Generators of Alt(points) inside S_n."""
    pts = list(points)
    if len(pts) < 3:
        return []
    out = [from_cycles(n, [pts[:3]])]
    if len(pts) > 3:
        if len(pts) % 2 == 1:
            out.append(from_cycles(n, [pts]))
        else:
            out.append(from_cycles(n, [pts[1:]]))
    return out
