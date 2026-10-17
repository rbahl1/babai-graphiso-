"""k-ary relational structures, configurations and k-dimensional Weisfeiler-Leman
refinement (Babai Sec. 2.3, 2.8; HBD Sec. 2.3-2.5, Algorithms 2 and 3).

* ``KStructure``: a coloring of Gamma^k (a "k-ary partition structure", HBD 2.3)
  stored as a flat list indexed by the base-|Gamma| encoding of the tuple.
* ``to_configuration`` implements HBD's functor F_2: the new color of a tuple
  x is (rho(x), (c(tau(x)))_tau) over all maps tau: [k] -> [k], so that the color
  of x "knows" the equality pattern and the colors of all coordinate
  substitutions (Babai Def. 2.3.4 (ii),(iii)).
* ``weisfeiler_leman`` implements HBD Algorithm 3 (Babai Sec. 2.8.2): the new
  color of x is (c(x), multiset over z of (c(x^1(z)), ..., c(x^k(z)))).  Colors
  are re-indexed by sorting the signatures lexicographically, so the final
  coloring is canonical and canonically ordered (HBD Exercise B on ordering).
  Several structures are refined *jointly* (shared indexer), which realizes the
  canonicity of the refinement for the pair of input strings (Babai eq. (10)).
* Individualization is read off the stable configuration by substitution
  (HBD Sec. 2.4): c_x(y) = c(x y); ``prefix_vertex_coloring`` and
  ``prefix_pair_coloring`` give X_x^{(1)} and X_x^{(2)}.
"""

from __future__ import annotations

from itertools import product
from typing import Callable, Dict, Hashable, List, Optional, Sequence, Tuple

from .canon import canon


class KStructure:
    """A coloring of Gamma^k, Gamma = range(n); colors are ints."""

    __slots__ = ("n", "k", "colors", "ncolors")

    def __init__(self, n: int, k: int, colors: List[int], ncolors: Optional[int] = None):
        self.n = n
        self.k = k
        self.colors = colors
        self.ncolors = ncolors if ncolors is not None else (max(colors) + 1 if colors else 0)

    def index(self, tup: Sequence[int]) -> int:
        n = self.n
        i = 0
        for v in tup:
            i = i * n + v
        return i

    def color(self, tup: Sequence[int]) -> int:
        return self.colors[self.index(tup)]

    def vertex_color(self, v: int) -> int:
        return self.colors[self.index((v,) * self.k)]

    def prefix_vertex_coloring(self, prefix: Sequence[int]) -> List[int]:
        """X_{prefix}^{(1)}: v -> c(prefix, v, v, ..., v) (HBD Sec. 2.4)."""
        k = self.k
        rest = k - len(prefix)
        return [self.colors[self.index(tuple(prefix) + (v,) * rest)] for v in range(self.n)]

    def prefix_pair_coloring(self, prefix: Sequence[int]) -> Callable[[int, int], int]:
        """X_{prefix}^{(2)}: (u,v) -> c(prefix, u, v, ..., v)."""
        k = self.k
        rest = k - len(prefix) - 1
        pre = tuple(prefix)
        colors = self.colors
        index = self.index

        def c(u: int, v: int) -> int:
            return colors[index(pre + (u,) + (v,) * rest)]

        return c


def structure_from_function(n: int, k: int, f: Callable[[Tuple[int, ...]], Hashable],
                            indexer: Optional[Dict[Hashable, int]] = None) -> Tuple[KStructure, Dict[Hashable, int]]:
    """Build a k-ary structure from an arbitrary (hashable) coloring function.

    The indexer maps raw colors to ints; it is shared between jointly refined
    structures so that equal raw colors get equal ints.  Raw colors are
    assigned ints in sorted order of first appearance *after* collection, so the
    numbering is canonical when the raw colors are canonical.
    """
    raw = [f(t) for t in product(range(n), repeat=k)]
    if indexer is None:
        indexer = {}
    for r in raw:
        if r not in indexer:
            indexer[r] = -1
    return KStructure(n, k, raw, 0), indexer  # type: ignore[arg-type]


def finalize_raw(structures: List[KStructure], indexer: Dict[Hashable, int]) -> List[KStructure]:
    """Assign canonical int colors (sorted raw colors) to raw-colored structures."""
    keys = sorted(indexer.keys(), key=_sort_key)
    for i, kk in enumerate(keys):
        indexer[kk] = i
    out = []
    for s in structures:
        cols = [indexer[r] for r in s.colors]
        out.append(KStructure(s.n, s.k, cols, len(keys)))
    return out


def _sort_key(x):
    # canonical, value-faithful ordering of heterogeneous colours (see ``canon``)
    return canon(x)


def _all_maps(k: int) -> List[Tuple[int, ...]]:
    return [tuple(m) for m in product(range(k), repeat=k)]


def to_configuration(structures: List[KStructure], trace: Optional[Callable[[Hashable], None]] = None) -> List[KStructure]:
    """HBD functor F_2: make the coloring a k-ary configuration (jointly).

    ``trace`` (if given) receives a canonical summary of the color classes so
    that separately refined structures can be compared (see Sec. "canonicity"
    in structure.py).
    """
    if not structures:
        return []
    k = structures[0].k
    maps = _all_maps(k)
    sigs_per = []
    all_sigs: Dict[tuple, int] = {}
    for s in structures:
        n = s.n
        colors = s.colors
        sigs = []
        for tup in product(range(n), repeat=k):
            rho = []
            for i in range(k):
                for j in range(i + 1, k):
                    rho.append(tup[i] == tup[j])
            sub = []
            for m in maps:
                idx = 0
                for i in m:
                    idx = idx * n + tup[i]
                sub.append(colors[idx])
            sig = (tuple(rho), tuple(sub))
            sigs.append(sig)
            all_sigs.setdefault(sig, 0)
        sigs_per.append(sigs)
    order = sorted(all_sigs.keys())
    for i, sg in enumerate(order):
        all_sigs[sg] = i
    if trace is not None:
        trace(("F2", _summary(order, sigs_per)))
    return [KStructure(s.n, s.k, [all_sigs[sg] for sg in sigs], len(order)) for s, sigs in zip(structures, sigs_per)]


def _summary(order: list, sigs_per: list) -> Hashable:
    """Canonical summary of a refinement round: the sorted signatures (hashed)
    together with the class sizes.  Isomorphic inputs give equal summaries."""
    counts = []
    for sigs in sigs_per:
        d: Dict[tuple, int] = {}
        for sg in sigs:
            d[sg] = d.get(sg, 0) + 1
        counts.append(tuple(d[sg] for sg in order))
    return (hash(tuple(order)), tuple(counts))


def weisfeiler_leman(structures: List[KStructure], max_rounds: Optional[int] = None,
                     trace: Optional[Callable[[Hashable], None]] = None) -> List[KStructure]:
    """k-dimensional WL refinement run jointly on the given k-ary configurations."""
    if not structures:
        return []
    k = structures[0].k
    cur = list(structures)
    rounds = 0
    while True:
        rounds += 1
        total_before = cur[0].ncolors
        sigs_per = []
        all_sigs: Dict[tuple, int] = {}
        for s in cur:
            n = s.n
            colors = s.colors
            pw = [n ** (k - 1 - j) for j in range(k)]
            sigs = []
            for idx, tup in enumerate(product(range(n), repeat=k)):
                base = [idx - tup[j] * pw[j] for j in range(k)]
                rows = []
                for z in range(n):
                    rows.append(tuple(colors[base[j] + z * pw[j]] for j in range(k)))
                rows.sort()
                sig = (colors[idx], tuple(rows))
                sigs.append(sig)
                all_sigs.setdefault(sig, 0)
            sigs_per.append(sigs)
        order = sorted(all_sigs.keys())
        for i, sg in enumerate(order):
            all_sigs[sg] = i
        if trace is not None:
            trace(("WL", rounds, _summary(order, sigs_per)))
        new = [KStructure(s.n, s.k, [all_sigs[sg] for sg in sigs], len(order)) for s, sigs in zip(cur, sigs_per)]
        if len(order) == total_before or (max_rounds is not None and rounds >= max_rounds):
            # stable: the new coloring refines the old one; equal counts means no split
            return new
        cur = new


def refine_structures(structures: List[KStructure], trace: Optional[Callable[[Hashable], None]] = None) -> List[KStructure]:
    """F_2 followed by F_3 (configuration + WL), jointly."""
    return weisfeiler_leman(to_configuration(structures, trace), trace=trace)


def classical_wl(n: int, vertex_color: Callable[[int], Hashable], pair_color: Callable[[int, int], Hashable],
                 trace: Optional[Callable[[Hashable], None]] = None) -> KStructure:
    """Classical (2-dimensional) WL on a binary structure given by colorings of
    vertices and ordered pairs (Babai Sec. 2.8.1).  Returns the stable 2-ary
    coherent configuration with canonically ordered colors."""
    raw = []
    for u in range(n):
        for v in range(n):
            if u == v:
                raw.append(("d", vertex_color(u)))
            else:
                raw.append(("e", pair_color(u, v)))
    keys = sorted(set(raw), key=_sort_key)
    idx = {kk: i for i, kk in enumerate(keys)}
    X = KStructure(n, 2, [idx[r] for r in raw], len(keys))
    if trace is not None:
        trace(("init2", tuple(raw.count(kk) for kk in keys), hash(tuple(keys))))
    return refine_structures([X], trace)[0]
