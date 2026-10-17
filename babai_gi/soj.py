"""Split-or-Johnson (Babai Sec. 7; HBD Sec. 5.2 with Babai's January 2017 fix).

Three mutually recursive procedures:

* ``upcc_split_or_johnson`` -- Babai Thm. 7.3.1 / Lemma 7.4.1 (UPCC-to-bipartite),
  HBD Thm. 5.2: individualize x, color by c(x, .), pass to the bipartite case.
* ``bipartite_split_or_johnson`` -- Babai Thm. 7.3.2 / Procedure Bipartite
  Split-or-Johnson (Sec. 7.5-7.11), in the form of HBD Prop. 5 ("Una partita a
  poker"), which replaces Babai's Sec. 7.11 (Johnson scheme on the small part)
  by the Ray-Chaudhuri-Wilson design bound and the Design Lemma on V2.
* ``coherent_split_or_johnson`` -- HBD Prop. 6 (Coherent Split-or-Johnson),
  containing Babai's imprimitive case (Sec. 7.7, Procedure ImprimitiveCase,
  Lemma 7.7.2 contracting components) and the UPCC case with the 2017 fix
  (HBD footnote 15: fix y in C2, violet/blue colors, no forked reduction).

All procedures operate on a global ``Structure`` on Gamma (the canonical
colored partition being built) and make their non-canonical choices through a
``Chooser`` (Babai Sec. 4, "canonical relative to an arbitrary choice at a
multiplicative cost").  Vertices of V2 may be "ideal points" (blocks of
canonical partitions, Babai Sec. 1.3.3); fixing an ideal point is recorded by
marking the underlying set of vertices of Gamma.

Every step either returns a valid structure or recurses on a strictly smaller
instance; whenever the hypotheses of a lemma fail (which can only happen below
the papers' size thresholds) a correct but expensive fallback (individualizing
all of V2) is used.
"""

from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations, product
from fractions import Fraction
from math import ceil, comb, log
from typing import Any, Callable, Dict, FrozenSet, Hashable, List, Optional, Sequence, Tuple

from .cc import ClassicalCC
from .errors import fallback
from .structure import Chooser, Fixed, Structure, JohnsonCell, _hk
from .wl import KStructure, classical_wl, refine_structures

#: Execution counters of the combinatorial procedures (which branches of the
#: Design Lemma / Split-or-Johnson actually ran).  Purely diagnostic; the tests
#: use them to prove that the branches execute.
STATS: Counter = Counter()


class SOJParams:
    """Thresholds of Bipartite Split-or-Johnson (HBD Prop. 5 / Babai Sec. 7.5).
    The defaults are the papers' values:

    small_v1
        HBD Prop. 5 "|V1| <= c, c a constant" (Babai 7.5 step 1 "n_1 <= C_0"):
        individualize (1 - beta)|V1| vertices.  The papers leave c unspecified.
    small_v2
        HBD Prop. 5 "|V2| <= (6 log|V1|)^{3/2}": individualize all of V2 (cost
        |V2|!).  None = that formula (natural logarithm); an int replaces it by a
        constant.  The default 0 disables the step: with the arity rule of
        ``arity`` the proof of Prop. 5 does not need it (the design argument checks
        C(|V2|, s) > |V1'| directly), and without it the number of choice sequences
        has no |V2|! factor (PROOF.md).
    max_dim
        Cap on the arity d of the d-ary structure on V2 (``arity``: d = d_1 if
        d_1 <= 2s, else 2s, s the smallest integer with C(|V2|, s) > |V1'|; HBD eq. (7)
        has s = 3 ceil(l)).  None = no cap.
    dl_alpha
        The alpha of the Design Lemma applied on V2 (HBD Prop. 5: 2/3).
    """

    def __init__(self, small_v1: int = 6, small_v2: Optional[int] = 0, max_dim: Optional[int] = None,
                 dl_alpha=Fraction(2, 3), allow_fallbacks: bool = False):
        self.small_v1 = small_v1
        self.small_v2 = small_v2
        self.max_dim = max_dim
        self.dl_alpha = Fraction(dl_alpha)
        # exact but expensive fallbacks for situations HBD's lemmas exclude (only below
        # the papers' thresholds); otherwise errors.TheoremViolation is raised
        self.allow_fallbacks = allow_fallbacks

    @classmethod
    def small_scale(cls, **overrides) -> "SOJParams":
        """Constants small enough for the procedures to run on Python-sized
        inputs: |V2| <= 3 individualized, arity capped at 4 (HBD's formula gives
        (6 log|V1|)^{3/2} >= 50 for |V1| >= 10, i.e. every reachable V2 would be
        individualized wholesale and the design / Design-Lemma steps never run)."""
        kw = dict(small_v1=6, small_v2=3, max_dim=4, allow_fallbacks=True)
        kw.update(overrides)
        return cls(**kw)

    def small_v2_bound(self, n1: int) -> int:
        """An integer s(n1) >= (6 ln n1)^{3/2} (HBD Prop. 5.7: "|V2| <= (6 log|V1|)^{3/2}"),
        nondecreasing in n1: the float value plus a margin far above the floating-point
        error, rounded up.  The proof only needs |V2| > s(n1) => |V2| > (6 ln n1)^{3/2}."""
        if self.small_v2 is not None:
            return self.small_v2
        v = (6.0 * log(max(n1, 2))) ** 1.5
        return int(v * (1 + 1e-9)) + 1

    def arity(self, d1: int, n1p: int, n2: int) -> int:
        """The arity d of the structure on V2 (HBD eq. (7)): d = d_1 if d_1 <= 2s, else
        d = 2s, where s is the smallest integer with C(|V2|, s) > |V1'|.

        HBD take s = 3 ceil(l), l = log|V1'| / log|V2|; the only property used is that a
        2s-design on |V2| points with |V1'| blocks cannot exist, which holds as soon as
        C(|V2|, s) > |V1'| (Ray-Chaudhuri-Wilson, HBD Prop. 2.20).  For |V2| above HBD's
        small-V2 threshold (6 ln|V1|)^{3/2}, s = 3 ceil(l) has this property (HBD's proof),
        so the smallest such s is at most 3 ceil(l) and d is at most HBD's 6 ceil(l).  The
        search stops at 2s >= d_1; then d = d_1 and the structure is the d_1-uniform
        hypergraph itself, which is not constant because it is not complete.  The smaller
        d lowers the number of Design-Lemma prefixes, |V2|^{d-1}, which sets the leading
        constant of the time bound (PROOF.md)."""
        s, c = 1, n2              # c = C(n2, s)
        while c <= n1p and 2 * s < d1:
            c = c * (n2 - s) // (s + 1)
            s += 1
        d = d1 if d1 <= 2 * s else 2 * s
        if self.max_dim is not None:
            d = min(d, self.max_dim)
        return max(2, min(d, d1))


def flatten(obj: Any) -> FrozenSet[int]:
    """Underlying set of vertices of Gamma of an (ideal) point."""
    if isinstance(obj, int):
        return frozenset([obj])
    out = set()
    for o in obj:
        out |= flatten(o)
    return frozenset(out)


def select_min(cands: Sequence[Any], key: Callable[[Any], Hashable], chooser: Chooser) -> Any:
    """Canonical selection: the candidate with minimal key; ties -> explicit choice."""
    best = None
    bestk = None
    for c in cands:
        kc = _hk(key(c))
        if bestk is None or kc < bestk:
            bestk, best = kc, [c]
        elif kc == bestk:
            best.append(c)
    if best is None:
        raise ValueError("no candidates")
    if len(best) == 1:
        chooser.check(("selmin", 1))
        return best[0]
    return chooser.choose([Fixed(b) for b in best]).value


def dominant_cell(base: Structure, inside: FrozenSet[int], bound: float) -> Optional[FrozenSet[int]]:
    big = [c for k, c in base.cells if c <= inside and len(c) > bound]
    if len(big) == 1:
        return big[0]
    return None


# ------------------------------------------------------------------ twins

def twin_classes_bipartite(V1: Sequence[int], adj: Dict[int, FrozenSet],
                           cell_of: Optional[Dict[int, int]] = None) -> List[List[int]]:
    """Twin classes in V1 of the bipartite graph (V1, V2; adj); with ``cell_of``, of the
    vertex-coloured graph (twins must lie in the same cell, Babai Def. 7.2.1)."""
    groups: Dict[Any, List[int]] = {}
    for v in V1:
        key = adj[v] if cell_of is None else (cell_of[v], adj[v])
        groups.setdefault(key, []).append(v)
    return list(groups.values())


def max_twin_class(V1: Sequence[int], adj: Dict[int, FrozenSet]) -> int:
    return max(len(c) for c in twin_classes_bipartite(V1, adj)) if V1 else 0


def restricted_adj(V1: Sequence[int], adj: Dict[int, FrozenSet], V2sub: Sequence[Any]) -> Dict[int, FrozenSet]:
    S = frozenset(V2sub)
    return {v: adj[v] & S for v in V1}


def reduce_part2_by_color(V1: Sequence[int], adj: Dict[int, FrozenSet], C1: Sequence[Any], C2: Sequence[Any]) -> Optional[Sequence[Any]]:
    """Procedure Reduce-Part2-by-Color (Babai 7.4, Lemma 7.4.2; HBD Exercise 5.2).

    Returns C1 if no twin class of V1 w.r.t. C1 exceeds |V1|/2 + 1, else C2 if
    C2 satisfies it, else None.  Prefers C1 (canonical rule).
    """
    n1 = len(V1)
    for C in (C1, C2):
        if not C:
            continue
        if 2 * max_twin_class(V1, restricted_adj(V1, adj, C)) <= n1 + 2:
            return C
    return None


def twin_classes_kary(nV: int, d: int, colors: List[int]) -> List[List[int]]:
    """Classes of the strong-twin relation of a d-ary coloring of range(nV)^d (Obs. 2.4.9)."""
    parent = list(range(nV))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    tuples = list(product(range(nV), repeat=d))
    index = {t: i for i, t in enumerate(tuples)}
    for u in range(nV):
        for v in range(u + 1, nV):
            if find(u) == find(v):
                continue
            ok = True
            for i, t in enumerate(tuples):
                if u in t or v in t:
                    s = tuple(v if a == u else u if a == v else a for a in t)
                    if colors[index[s]] != colors[i]:
                        ok = False
                        break
            if ok:
                parent[find(v)] = find(u)
    groups: Dict[int, List[int]] = {}
    for i in range(nV):
        groups.setdefault(find(i), []).append(i)
    return list(groups.values())


# ----------------------------------------------------------- Design Lemma

def design_lemma(X: KStructure, alpha: float, chooser: Chooser,
                 objs: Optional[Sequence[Any]] = None) -> Optional[Tuple[Tuple[int, ...], str, List[int]]]:
    """HBD Prop. 4 (Design Lemma, Babai Thm. 6.1.1) search over prefixes.

    Returns (prefix, kind, vertex coloring) where kind is 'a' (no alpha-dominant
    color) or 'b' (dominant class C with (X_prefix)^(2)[C] not a clique), or
    None if no prefix works (the hypotheses of the lemma were violated).  The
    prefix is chosen among all working prefixes of minimal length (a canonical
    set), at multiplicative cost |Gamma|^{len(prefix)}.  ``objs`` maps vertex
    indices to the actual (ideal) points presented to the chooser.
    """
    n, k = X.n, X.k
    STATS["design_lemma"] += 1
    if objs is None:
        objs = list(range(n))
    for ell in range(0, k):
        work: List[Tuple[Tuple[int, ...], str]] = []
        for tup in permutations(range(n), ell):
            col1 = X.prefix_vertex_coloring(tup)
            groups: Dict[int, List[int]] = {}
            for v, c in enumerate(col1):
                groups.setdefault(c, []).append(v)
            dom = [vs for vs in groups.values() if len(vs) > alpha * n]
            if not dom:
                work.append((tup, "a"))
                continue
            if ell < k - 1:
                C = dom[0]
                c2 = X.prefix_pair_coloring(tup)
                seen = set()
                for u in C:
                    for v in C:
                        if u != v:
                            seen.add(c2(u, v))
                            if len(seen) > 1:
                                break
                    if len(seen) > 1:
                        break
                if len(seen) > 1:
                    work.append((tup, "b"))
        chooser.check(("dl", ell, len(work)))
        if work:
            cands = [(tuple(objs[i] for i in tup), kind) for tup, kind in work]
            chosen = chooser.choose(cands)
            idx = cands.index(chosen)
            tup, kind = work[idx]
            STATS[f"design_lemma_{kind}_prefix{ell}"] += 1
            return tup, kind, X.prefix_vertex_coloring(tup)
    STATS["design_lemma_failed"] += 1
    return None


# ------------------------------------------------------- UPCC Split-or-Johnson

def upcc_split_or_johnson(cc: ClassicalCC, alpha: float, base: Structure, chooser: Chooser,
                          params: SOJParams, depth: int = 0) -> Structure:
    """Babai Thm. 7.3.1 via Lemma 7.4.1 (UPCC-to-bipartite); HBD Thm. 5.2.

    ``cc`` is a uniprimitive coherent configuration on a subset V of Gamma
    (vertices are ints).  Returns a Structure on Gamma whose cells inside V
    have size <= alpha|V| or contain a Johnson scheme on >= alpha|V| vertices.
    """
    V = cc.vertices
    nV = len(V)
    Vset = frozenset(V)
    STATS["upcc_soj"] += 1
    chooser.check(("upcc", nV, len(cc.colors)))
    x = chooser.choose(sorted(V))
    xi = cc.pos[x]
    row = cc.c[xi]
    base = base.individualize(x, ("upcc-x", depth))
    coloring = {v: cc.key(row[cc.pos[v]]) for v in V}
    base = base.refine(lambda v: coloring.get(v, None), ("upcc-col", depth))
    # Colours with equal keys (possible when the colours carry no canonical names, e.g.
    # the orbital configuration of case 2b) are split into their actual colour classes,
    # as interchangeable blocks: tied colours have equal valency (the key records it),
    # so this is an equipartition of the key class, and it is canonical.  Afterwards
    # every cell inside V \ {x} is a single colour class.
    by_key: Dict[Hashable, Dict[Any, List[int]]] = {}
    for v in V:
        if v != x:
            by_key.setdefault(coloring[v], {}).setdefault(row[cc.pos[v]], []).append(v)
    for kk in sorted(by_key, key=_hk):
        groups = by_key[kk]
        if len(groups) > 1:
            blocks = list(groups.values())
            if len(set(len(b) for b in blocks)) != 1:
                raise RuntimeError("tied colours of different valency")
            if len(blocks[0]) == 1:
                # valency 1: the configuration is a cycle (CORRECTNESS.md, case 2b)
                return _thin_cycle_structure(cc, x, [b[0] for b in blocks], base, chooser, depth)
            base = split_by_blocks(base, [v for b in blocks for v in b], blocks, ("upcc-tie", depth))
    bound = alpha * nV
    V1 = dominant_cell(base, Vset, bound)
    chooser.check(("upcc-dom", V1 is not None))
    if V1 is None:
        return base
    # V1 (> alpha|V| >= |V|/2 points) is one colour class, and the only one with its key
    aqua = row[cc.pos[next(iter(V1))]]
    if any(row[cc.pos[v]] != aqua for v in V1):
        raise RuntimeError("dominant cell is not a colour class")
    V1 = sorted(V1)
    diag = cc.diagonal_colors()
    cand = set()
    for y in V:
        beige = row[cc.pos[y]]
        if beige == aqua or beige in diag:
            continue
        for z in V1:
            cyan = cc.c[cc.pos[z]][cc.pos[y]]
            if cyan == aqua or cyan in diag:
                continue
            cand.add((beige, cyan))
    cands = sorted(cand, key=lambda bc: (_hk(cc.key(bc[0])), _hk(cc.key(bc[1]))))
    chooser.check(("upcc-cand", len(cands)))
    if not cands:
        # unreachable for a uniprimitive coherent configuration (HBD Ex. B.7; CORRECTNESS.md)
        fallback(params.allow_fallbacks, "UPCC: no (beige, cyan) pair (HBD Ex. B.7)")
        STATS["upcc_fallback"] += 1
        return individualize_until(base, V, bound, chooser, ("upcc-fb", depth))
    STATS["upcc_to_bipartite"] += 1
    beige, cyan = select_min(cands, lambda bc: (cc.key(bc[0]), cc.key(bc[1])), chooser)
    V2 = [y for y in V if row[cc.pos[y]] == beige]
    adj = {z: frozenset(y for y in V2 if cc.c[cc.pos[z]][cc.pos[y]] == cyan) for z in V1}
    beta = bound / len(V1)
    return bipartite_split_or_johnson(V1, V2, adj, beta, base, chooser, params, depth + 1)


def _thin_cycle_structure(cc: ClassicalCC, x: int, cands: Sequence[int], base: Structure, chooser: Chooser,
                          depth: int) -> Structure:
    """A primitive coherent configuration with a colour c of valency 1: the c-relation
    is a permutation of V whose cycles are the components of c, so it is one cycle of
    length |V|.  Choose y among ``cands`` (the points whose colour from x is tied with
    another colour of valency 1), let c be the colour of (x, y), and give the vertex
    reached from x by j steps along c the colour j.  The result is discrete on V and
    canonical relative to the choices of x and y."""
    y = chooser.choose(sorted(cands))
    pos = cc.pos
    c = cc.c[pos[x]][pos[y]]
    nxt = {}
    for u in cc.vertices:
        row = cc.c[pos[u]]
        nxt[u] = [v for v in cc.vertices if row[pos[v]] == c]
    place = {x: 0}
    u = x
    for j in range(1, len(cc.vertices)):
        if len(nxt[u]) != 1:
            raise RuntimeError("tied colour of valency 1 is not a permutation")
        u = nxt[u][0]
        if u in place:
            raise RuntimeError("colour of valency 1 in a primitive configuration is not one cycle")
        place[u] = j
    return base.refine(lambda v: place.get(v, None), ("upcc-cycle", depth))


def individualize_until(base: Structure, V: Sequence[int], bound: float, chooser: Chooser, tag: Hashable) -> Structure:
    """Fallback: individualize vertices of the dominant cell until all cells inside V are small."""
    STATS["individualize_until"] += 1
    Vset = frozenset(V)
    step = 0
    while True:
        big = [c for k, c in base.cells if c <= Vset and len(c) > bound]
        chooser.check(("ind-until", len(big)))
        if not big:
            return base
        big.sort(key=lambda c: sorted(c))
        v = chooser.choose(sorted(big[0]))
        base = base.individualize(v, (tag, step))
        step += 1


# ------------------------------------------------- Bipartite Split-or-Johnson

def bipartite_split_or_johnson(V1: Sequence[int], V2: Sequence[Any], adj: Dict[int, FrozenSet], beta: float,
                               base: Structure, chooser: Chooser, params: SOJParams, depth: int = 0,
                               n1_orig: Optional[int] = None) -> Structure:
    """HBD Prop. 5 (Babai Thm. 7.3.2).  V1 subset of Gamma; V2 a list of (ideal) points;
    adj[v] = neighbourhood of v in V2.  Result: cells inside V1 of size <= beta*n1_orig,
    or a Johnson scheme on a cell of size >= beta*n1_orig."""
    V1 = sorted(V1)
    V2 = list(V2)
    n1 = len(V1)
    if n1_orig is None:
        n1_orig = n1
    bound = beta * n1_orig
    n2 = len(V2)
    STATS["bipartite_soj"] += 1
    chooser.check(("bsoj", depth, n1, n2))
    V1set = frozenset(V1)
    if n1 == 0 or dominant_cell(base, V1set, bound) is None:
        return base
    # (every recursive call below strictly decreases |V2|, so the recursion terminates)

    # Step 1 (Babai 7.5 step 1 / HBD "|V1| <= c"): individualize (1-beta) n1 vertices.
    if n1 <= params.small_v1:
        STATS["bipartite_soj_small_v1"] += 1
        return individualize_until(base, V1, bound, chooser, ("bsoj-small", depth))

    # Step 2 (HBD "|V2| <= (6 log|V1|)^{3/2}"; disabled by default, SOJParams.small_v2 = 0):
    # individualize all of V2, color V1 by neighbourhoods.
    if n2 <= params.small_v2_bound(n1):
        STATS["bipartite_soj_small_v2"] += 1
        return _individualize_v2(V1, V2, adj, base, chooser, depth)

    # Step 3: twins and degrees (of the vertex-coloured graph: twins lie in one cell).
    tw = twin_classes_bipartite(V1, adj, base.cell_of())
    twsize = {}
    for cl in tw:
        for v in cl:
            twsize[v] = len(cl)
    colv = {v: (twsize[v], len(adj[v])) for v in V1}
    base = base.refine(lambda v: colv.get(v, None), ("bsoj-tw", depth))
    V1p_set = dominant_cell(base, V1set, bound)
    chooser.check(("bsoj-dom", V1p_set is not None))
    if V1p_set is None:
        return base
    V1p = sorted(V1p_set)
    if twsize[V1p[0]] > 1:
        # the dominant class consists of twin classes of equal size c >= 2: they form a
        # canonical equipartition of the class (HBD Prop. 5, "colored beta-partition
        # unless ... vertices without twins"); if a twin class is still too large the
        # hypothesis of the proposition is violated and we fall back to individualizing
        # every twin class meeting the cell V1' lies in it and has size twsize >= 2
        blocks = [cl for cl in tw if cl[0] in V1p_set]
        if any(len(b) != twsize[V1p[0]] or not set(b) <= V1p_set for b in blocks):
            raise RuntimeError("twin classes do not partition the dominant cell")
        chooser.check(("bsoj-twin-blocks", len(blocks), twsize[V1p[0]]))
        if twsize[V1p[0]] <= bound:
            STATS["bipartite_soj_twin_equipartition"] += 1
            return split_by_blocks(base, V1p, blocks, ("bsoj-twins", depth))
        fallback(params.allow_fallbacks, "bipartite SoJ: twin class larger than the bound (HBD Prop. 5.7)")
        return individualize_until(base, V1, bound, chooser, ("bsoj-twins", depth))
    d1 = len(adj[V1p[0]])
    V2set = frozenset(V2)
    adjp = {v: adj[v] & V2set for v in V1p}
    complemented = False
    if 2 * d1 > n2:
        adjp = {v: V2set - adjp[v] for v in V1p}
        d1 = n2 - d1
        complemented = True
    chooser.check(("bsoj-d1", d1, complemented))
    if d1 == 0:
        fallback(params.allow_fallbacks, "bipartite SoJ: degree 0 on a twin-free cell")
        return individualize_until(base, V1, bound, chooser, ("bsoj-deg", depth))

    # Step 4: the neighbourhood hypergraph H on V2.
    H = {adjp[v] for v in V1p}
    idx2 = {p: i for i, p in enumerate(V2)}
    if len(H) == comb(n2, d1):
        chooser.check(("bsoj-complete", d1, n2))
        if d1 >= 2 and n2 >= 2 * d1 + 1:
            STATS["bipartite_soj_johnson_scheme"] += 1
            labels = {v: frozenset(idx2[p] for p in adjp[v]) for v in V1p}
            cell_index = [i for i, (k, c) in enumerate(base.cells) if c == V1p_set][0]
            return base.with_johnson(cell_index, JohnsonCell(n2, d1, labels))
        # |V2| = 2 d1 (J(2 d1, d1) is not a Johnson scheme in Babai's sense): individualize
        # one point of V2 and split V1' by containment into two halves of |V1'|/2 points.
        # d1 = 1 is impossible: then |V1'| = |V2| < bound < |V1'|.
        if d1 < 2:
            fallback(params.allow_fallbacks, "bipartite SoJ: complete hypergraph with d1 = 1")
        STATS["bipartite_soj_half_split"] += 1
        pt = chooser.choose(list(V2))
        base = base.mark(flatten(pt), ("bsoj-half", depth))
        return base.refine(lambda v: (1 if pt in adjp[v] else 0) if v in adjp else None, ("bsoj-halfc", depth))

    # Step 5: a d-ary structure on V2 (HBD eq. (7)); d = d_1 or 2s (SOJParams.arity).
    d = params.arity(d1, len(V1p), n2)
    Hidx = [frozenset(idx2[p] for p in e) for e in H]
    counts: Dict[FrozenSet[int], int] = {}
    if d == d1:
        for e in Hidx:
            counts[e] = 1
    else:
        for e in Hidx:
            for sub in combinations(sorted(e), d):
                fs = frozenset(sub)
                counts[fs] = counts.get(fs, 0) + 1
    tuples = list(product(range(n2), repeat=d))
    raw = []
    for t in tuples:
        if len(set(t)) < d:
            raw.append(-1)
        else:
            raw.append(counts.get(frozenset(t), 0))
    distinct = sorted(set(raw))
    cmap = {c: i for i, c in enumerate(distinct)}
    X0 = KStructure(n2, d, [cmap[r] for r in raw], len(distinct))
    chooser.check(("bsoj-dary", d, tuple(raw.count(c) for c in distinct)))
    if len([c for c in distinct if c != -1]) <= 1:
        fallback(params.allow_fallbacks, "bipartite SoJ: d-ary structure constant (Ray-Chaudhuri-Wilson)")
        return _individualize_v2(V1p, V2, adjp, base, chooser, depth)
    twk = twin_classes_kary(n2, d, X0.colors)
    big = [cl for cl in twk if 2 * len(cl) > n2]
    chooser.check(("bsoj-twk", len(big)))
    if big:
        S = [V2[i] for i in big[0]]
        Sset = set(S)
        rest = [p for p in V2 if p not in Sset]
        chosen = reduce_part2_by_color(V1p, adjp, S, rest)
        if chosen is None:
            fallback(params.allow_fallbacks, "Reduce-Part2-by-Color failed (HBD Ex. 5.5)")
            chosen = S
        chooser.check(("bsoj-twk-pick", chosen is S))
        return bipartite_split_or_johnson(V1p, chosen, restricted_adj(V1p, adjp, chosen), beta, base, chooser, params,
                                          depth + 1, n1_orig)

    # Step 6: refine (F2, F3) and apply the Design Lemma with alpha = 2/3 on V2.
    X = refine_structures([X0], chooser.check)[0]
    res = design_lemma(X, params.dl_alpha, chooser, V2)
    if res is None:
        fallback(params.allow_fallbacks, "Design Lemma failed on V2 (HBD Prop. 5.1)")
        return _individualize_v2(V1p, V2, adjp, base, chooser, depth)
    tup, kind, col1 = res
    for i, p in enumerate(tup):
        base = base.mark(flatten(V2[p]), ("bsoj-dl", depth, i))
    if kind == "a":
        return _split_by_coloring_of_v2(V1p, V2, adjp, col1, beta, base, chooser, params, depth, n1_orig)
    # kind 'b': dominant class C of V2 with non-clique configuration Y on C
    groups2: Dict[int, List[int]] = {}
    for i, c in enumerate(col1):
        groups2.setdefault(c, []).append(i)
    C = sorted(max(groups2.values(), key=len))
    c2 = X.prefix_pair_coloring(tup)
    Cset = set(C)
    N1 = len(V1p)
    Ntot = N1 + n2
    adj_idx = {i: frozenset(idx2[p] for p in adjp[v]) for i, v in enumerate(V1p)}
    keyv = base.key_of_vertex()

    def vcol(u: int) -> Hashable:
        if u < N1:
            return ("v1", _hk(keyv[V1p[u]]))
        p = V2[u - N1]
        return ("v2", col1[u - N1], _hk(keyv[p]) if isinstance(p, int) else None)

    def pcol(u: int, v: int) -> Hashable:
        if u < N1 and v < N1:
            return ("11",)
        if u < N1 <= v:
            return ("12", (v - N1) in adj_idx[u])
        if v < N1 <= u:
            return ("21", (u - N1) in adj_idx[v])
        a, b = u - N1, v - N1
        if a in Cset and b in Cset:
            return ("22C", c2(a, b))
        return ("22",)

    Xc = classical_wl(Ntot, vcol, pcol, chooser.check)
    cc = ClassicalCC(list(range(Ntot)), lambda u, v: Xc.color((u, v)))
    vclasses: Dict[Hashable, List[int]] = {}
    for i in range(Ntot):
        vclasses.setdefault(cc.vcol[i], []).append(i)
    v2_classes = [vs for vs in vclasses.values() if vs[0] >= N1]
    col_v1 = {V1p[i]: cc.vcol[i] for i in range(N1)}
    base = base.refine(lambda v: col_v1.get(v, None), ("bsoj-wl1", depth))
    dom2 = [vs for vs in v2_classes if len(vs) >= params.dl_alpha * n2]
    chooser.check(("bsoj-wl-dom2", len(dom2)))
    if not dom2:
        col_v2 = [cc.vcol[N1 + i] for i in range(n2)]
        return _split_by_coloring_of_v2(V1p, V2, adjp, col_v2, beta, base, chooser, params, depth, n1_orig)
    C2 = [i - N1 for i in dom2[0]]
    C1_set = dominant_cell(base, V1p_set, bound)
    chooser.check(("bsoj-wl-dom1", C1_set is not None))
    if C1_set is None:
        return base
    C1 = sorted(V1p.index(v) for v in C1_set)
    seen = set()
    for u in C1:
        for w in C2:
            seen.add(cc.c[u][N1 + w])
            if len(seen) > 1:
                break
        if len(seen) > 1:
            break
    chooser.check(("bsoj-c1c2", len(seen)))
    if len(seen) <= 1:
        C2set = set(C2)
        rest = [p for i, p in enumerate(V2) if i not in C2set]
        if not rest:
            fallback(params.allow_fallbacks, "bipartite SoJ: C2 = V2 with a constant C1 x C2 colour")
            return _individualize_v2(V1p, V2, adjp, base, chooser, depth)
        return bipartite_split_or_johnson(V1p, rest, restricted_adj(V1p, adjp, rest), beta, base, chooser, params,
                                          depth + 1, n1_orig)
    sub2 = cc.induced([N1 + w for w in C2])
    chooser.check(("bsoj-sub2clique", sub2.is_clique()))
    if sub2.is_clique():
        fallback(params.allow_fallbacks, "bipartite SoJ: X[C2] is a clique (HBD Ex. 2.15)")
        return _individualize_v2(V1p, V2, adjp, base, chooser, depth)
    STATS["bipartite_soj_to_coherent"] += 1
    local = cc.induced(list(C1) + [N1 + w for w in C2])
    kind2, data, base = coherent_split_or_johnson(local, list(C1), [N1 + w for w in C2],
                                                  lambda u: V1p[u], lambda w: V2[w - N1], base, chooser, depth,
                                                  params.allow_fallbacks)
    if kind2 == "coloring":
        return base
    W1, W2, adjW = data
    chooser.check(("bsoj-cohout", len(W1), len(W2)))
    if len(W1) <= bound or not W2:
        return base
    return bipartite_split_or_johnson(W1, W2, adjW, beta, base, chooser, params, depth + 1, n1_orig)


def _individualize_v2(V1: Sequence[int], V2: Sequence[Any], adj: Dict[int, FrozenSet], base: Structure,
                      chooser: Chooser, depth: int) -> Structure:
    """Individualize all points of V2 (in a chosen order) and color V1 by neighbourhoods."""
    STATS["individualize_v2"] += 1
    remaining = list(V2)
    order = []
    i = 0
    while remaining:
        p = chooser.choose(remaining)
        remaining = [q for q in remaining if q != p]
        base = base.mark(flatten(p), ("v2ind", depth, i))
        order.append(p)
        i += 1
    pos = {p: i for i, p in enumerate(order)}
    nb = {v: tuple(sorted(pos[p] for p in adj[v])) for v in V1}
    return base.refine(lambda v: nb.get(v, None), ("v2nb", depth))


def _split_by_coloring_of_v2(V1p: Sequence[int], V2: Sequence[Any], adjp: Dict[int, FrozenSet], col: Sequence[Hashable],
                             beta: float, base: Structure, chooser: Chooser, params: SOJParams, depth: int,
                             n1_orig: int) -> Structure:
    """HBD Prop. 5, case (a): no dominant color on V2.  Pick a canonical union S of
    color classes with |V2|/3 < |S| <= 2|V2|/3 and reduce V2 by Exercise 5.2."""
    n2 = len(V2)
    groups: Dict[Hashable, List[int]] = {}
    for i, c in enumerate(col):
        groups.setdefault(c, []).append(i)
    keys = sorted(groups, key=_hk)
    mid = [k for k in keys if n2 < 3 * len(groups[k]) <= 2 * n2]
    if mid:
        S_idx = groups[mid[0]]
    else:
        S_idx = []
        for k in keys:
            S_idx.extend(groups[k])
            if 3 * len(S_idx) > n2:
                break
    S_set = set(S_idx)
    S = [V2[i] for i in S_idx]
    rest = [V2[i] for i in range(n2) if i not in S_set]
    chosen = reduce_part2_by_color(V1p, adjp, S, rest)
    if chosen is None:
        fallback(params.allow_fallbacks, "Reduce-Part2-by-Color failed (HBD Ex. 5.5)")
        chosen = S
    chooser.check(("split-v2", len(S), chosen is S))
    if len(chosen) >= n2:
        fallback(params.allow_fallbacks, "bipartite SoJ: no proper part of V2")
        return _individualize_v2(V1p, V2, adjp, base, chooser, depth)
    return bipartite_split_or_johnson(V1p, chosen, restricted_adj(V1p, adjp, chosen), beta, base, chooser, params,
                                      depth + 1, n1_orig)


# ---------------------------------------------------- Coherent Split-or-Johnson

def coherent_split_or_johnson(X: ClassicalCC, C1: List[int], C2: List[int], v1_of, v2_of, base: Structure,
                              chooser: Chooser, depth: int, allow_fallbacks: bool = False):
    """HBD Prop. 6.  X is a coherent configuration on C1 + C2 (vertex indices of X),
    |C1| > |C2|, c nonconstant on C1 x C2 and on C2 x C2.  ``v1_of``/``v2_of`` map
    indices back to vertices of Gamma / points of V2.

    Returns ("coloring", None, base') where base' already contains a colored
    1/2-partition of C1, or ("bipartite", (W1, W2, adj), base') with W1 a list
    of vertices of Gamma, W2 a list of (ideal) points, |W1| >= |C1|/2,
    |W2| <= |C2|/2 and no twin class in W1 larger than |W1|/2.
    """
    n1, n2 = len(C1), len(C2)
    pos = X.pos
    c = X.c
    X1 = X.induced(C1)
    X2 = X.induced(C2)
    v1_vertices = [v1_of(u) for u in C1]
    STATS["coherent_soj"] += 1
    chooser.check(("coh", n1, n2, len(X.colors)))
    # X[C1] imprimitive -> components of the reddest disconnected relation
    disc1 = X1.disconnected_off_diagonal_colors()
    chooser.check(("coh-disc1", len(disc1)))
    if disc1:
        STATS["coherent_soj_c1_imprimitive"] += 1
        col = select_min(disc1, X1.key, chooser)
        comps = X1.components(col)
        blocks = [[v1_of(X1.vertices[i]) for i in cmp] for cmp in comps]
        base = split_by_blocks(base, v1_vertices, blocks, ("coh-comp1", depth))
        return "coloring", None, base
    disc2 = X2.disconnected_off_diagonal_colors()
    chooser.check(("coh-disc2", len(disc2)))
    if disc2:
        # imprimitive case (Babai 7.7 / HBD)
        STATS["coherent_soj_c2_imprimitive"] += 1
        col = select_min(disc2, X2.key, chooser)
        comps = X2.components(col)
        B = [[X2.vertices[i] for i in cmp] for cmp in comps]
        w0 = C2[0]
        deg: Dict[Hashable, int] = {}
        for u in C1:
            k = c[pos[u]][pos[w0]]
            deg[k] = deg.get(k, 0) + 1
        big = [k for k, dk in deg.items() if 2 * dk > n1]
        chooser.check(("coh-imp-deg", len(big)))
        if not big:
            objs = [v2_of(w) for w in sorted(C2)]
            w = sorted(C2)[objs.index(chooser.choose(objs))]
            base = base.mark(flatten(v2_of(w)), ("coh-imp-w", depth))
            colw = {v1_of(u): X.key(c[pos[u]][pos[w]]) for u in C1}
            base = base.refine(lambda v: colw.get(v, None), ("coh-imp-col", depth))
            return "coloring", None, base
        violet = big[0]
        acceptable = []
        for i, blk in enumerate(B):
            adj_i = {v1_of(u): frozenset(v2_of(w) for w in blk if c[pos[u]][pos[w]] == violet) for u in C1}
            if 2 * max_twin_class(v1_vertices, adj_i) <= n1:
                acceptable.append(i)
        chooser.check(("coh-imp-acc", len(acceptable)))
        if acceptable:
            ys = []
            for i in acceptable:
                ys.extend(sorted(B[i]))
            objs = [v2_of(w) for w in ys]
            y = ys[objs.index(chooser.choose(objs))]
            i = next(i for i in acceptable if y in B[i])
            base = base.mark(flatten(v2_of(y)), ("coh-imp-y", depth))
            blk = B[i]
            W2 = [v2_of(w) for w in blk]
            adjW = {v1_of(u): frozenset(v2_of(w) for w in blk if c[pos[u]][pos[w]] == violet) for u in C1}
            return "bipartite", (v1_vertices, W2, adjW), base
        # contract the blocks (Babai Lemma 7.7.2 / HBD Exercise 2.6)
        greens = [k for k in deg if k != violet]
        green = select_min(greens, X.key, chooser)
        W2 = [frozenset(v2_of(w) for w in blk) for blk in B]
        adjW = {}
        for u in C1:
            s = set()
            for bi, blk in enumerate(B):
                if any(c[pos[u]][pos[w]] == green for w in blk):
                    s.add(W2[bi])
            adjW[v1_of(u)] = frozenset(s)
        return "bipartite", (v1_vertices, W2, adjW), base
    # X[C2] primitive, not a clique: the 2017 fix (HBD footnote 15)
    STATS["coherent_soj_c2_primitive_2017fix"] += 1
    objs = [v2_of(w) for w in sorted(C2)]
    y = sorted(C2)[objs.index(chooser.choose(objs))]
    base = base.mark(flatten(v2_of(y)), ("coh-prim-y", depth))
    deg = {}
    for u in C1:
        k = c[pos[u]][pos[y]]
        deg[k] = deg.get(k, 0) + 1
    big = [k for k, dk in deg.items() if 2 * dk > n1]
    chooser.check(("coh-prim-deg", len(big)))
    if not big:
        coly = {v1_of(u): X.key(c[pos[u]][pos[y]]) for u in C1}
        base = base.refine(lambda v: coly.get(v, None), ("coh-prim-col", depth))
        return "coloring", None, base
    violet = big[0]
    V1 = [u for u in C1 if c[pos[u]][pos[y]] == violet]
    blues = []
    for col in X2.off_diagonal_colors():
        dg = X2.out_degree(X2.pos[y], col)
        if 0 < 2 * dg < n2:
            blues.append(col)
    chooser.check(("coh-prim-blues", len(blues)))
    if not blues:
        fallback(allow_fallbacks, "coherent SoJ: no blue colour (X[C2] not a clique)")
        return "coloring", None, individualize_until(base, v1_vertices, Fraction(n1, 2), chooser, ("coh-prim-fb", depth))
    blue = select_min(blues, X2.key, chooser)
    V2 = [w for w in C2 if c[pos[w]][pos[y]] == blue]
    W1 = [v1_of(u) for u in V1]
    W2 = [v2_of(w) for w in V2]
    adjW = {v1_of(u): frozenset(v2_of(w) for w in V2 if c[pos[u]][pos[w]] == violet) for u in V1}
    W1set = frozenset(W1)
    v1set = frozenset(v1_vertices)
    base = base.refine(lambda v: 1 if v in W1set else (0 if v in v1set else None), ("coh-prim-w1", depth))
    return "bipartite", (W1, W2, adjW), base


def split_by_blocks(base: Structure, cell_vertices: Sequence[int], blocks: Sequence[Sequence[int]],
                    tag: Hashable) -> Structure:
    """Partition the cells inside ``cell_vertices`` by a canonical partition into
    interchangeable blocks (a colored equipartition, Babai Def. 5.1.1).  If a
    block meets several cells, the pieces are made interchangeable within each
    cell; this yields a (possibly larger, still valid) automorphism group."""
    cv = frozenset(cell_vertices)
    blk_of = {}
    for bi, b in enumerate(blocks):
        for v in b:
            blk_of[v] = bi
    new_cells = []
    johnson = base.johnson
    jcell_set = base.cells[base.johnson_cell][1] if base.johnson_cell is not None else None
    jcell = None
    for k, c in base.cells:
        if c <= cv:
            groups: Dict[int, List[int]] = {}
            for v in c:
                groups.setdefault(blk_of[v], []).append(v)
            for g in groups.values():
                new_cells.append(((k, tag), frozenset(g)))
        else:
            if jcell_set is not None and c == jcell_set:
                jcell = len(new_cells)
            new_cells.append((k, c))
    if jcell is None:
        johnson = None
    return Structure(base.m, new_cells, johnson, jcell)
