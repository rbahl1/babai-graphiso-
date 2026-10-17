"""The parameter presets and the Cameron-group (product action) recognition.

* ``Params.paper()`` -- the papers' thresholds, the library default: on inputs
  where they are feasible (tiny graphs; String Isomorphism with a very small
  Gamma) the answers are compared with brute force and the counters prove that
  the paper's prescription was followed (Reduce-to-Johnson line 2 / line 5:
  enumeration; no Johnson case below ell(n)).
* ``Params.small_scale()`` -- the small constants used by the rest of the battery.
* ``recognize_cameron`` -- S_k^{(t)} wr S_s in product action (Babai Def. 3.2.2,
  Thm. 3.2.1), verified against the construction, and String Isomorphism on
  S_5^{(2)} wr S_2 (100 points, full coset against brute force) and
  S_6^{(2)} wr S_2 (225 points, |Aut| against the formula).
"""

import itertools
import random
from math import comb, factorial, log2

import networkx as nx
import pytest
from networkx.generators.atlas import graph_atlas_g

from babai_gi.graph import GraphInstance, graph_automorphisms, graph_isomorphism
from babai_gi.group import PermGroup
from babai_gi.johnson import (CameronStructure, johnson_group_gens, pairs_of, recognize_cameron, recognize_hamming,
                              recognize_johnson, subsets_of)
from babai_gi.main import Params, Solver, string_isomorphism
from babai_gi.perm import act_string, from_cycles, maps_string, mul
from babai_gi.soj import SOJParams

from .helpers import brute_aut_order, check_isomorphism, edges_of, relabel


# ------------------------------------------------------------------ presets

def test_default_params_are_the_papers():
    assert Solver().params.preset == "paper"
    P = Params()
    assert P.quotient_enum_limit is None and P.min_gamma is None and P.k_rule == "paper"
    assert P.soj.small_v2 == 0 and P.soj.max_dim is None
    assert Params.paper().brute_force_order == 5040 and Params.paper().cameron_maroti_degree == 25
    S = Params.small_scale()
    assert (S.quotient_enum_limit, S.min_gamma, S.k_rule) == (20000, 8, "small_scale")
    assert (S.soj.small_v1, S.soj.small_v2, S.soj.max_dim) == (6, 3, 4)
    assert Params.small_scale(min_gamma=6).min_gamma == 6
    with pytest.raises(ValueError):
        Params(k_rule="other")


def test_paper_formulas():
    P = Params.paper()
    # Cameron-Maroti bound (Thm. 3.2.3): enumeration below the integer threshold
    # m^{1+floor(log2 m)} <= m^{1+log2 m}; an unrecognised quotient below the cap
    # m^{2+floor(log2 m)} > m^{1+log2 m} may still be enumerated
    for m in (5, 12, 28, 225):
        thr = P.luks_threshold(m)
        assert thr == m ** (1 + int(log2(m))) and thr <= m ** (1 + log2(m))
        assert P.enumeration_cap(m) == m * thr > m ** (1 + log2(m))
        assert P.small_quotient(thr - 1, m) and not P.small_quotient(thr, m)
    assert Params.small_scale().small_quotient(20000, 225) and not Params.small_scale().small_quotient(20001, 225)
    # k > max{8, 2 + log2 n} (Thm. 8.3.5 / Thm. 10.1.3), the smallest such integer
    for n in (1, 10, 64, 65, 1000, 1024, 10 ** 6):
        k = P.k_paper(n)
        assert k > max(8, 2 + log2(n)) and k - 1 <= max(8, 2 + log2(n))
    assert P.k_paper(64) == 9 and P.k_paper(1024) == 13
    # ell(n) = 10 k(n): the smallest |Gamma| admitting k <= |Gamma|/10
    assert P.gamma_threshold(45) == 90 and P.gamma_threshold(2 ** 20) == 230
    assert P.k_for(45, 90) == 9 and P.k_for(2 ** 20, 230) == 23
    assert Params.small_scale().k_for(42, 7) == 4 and Params.small_scale().k_for(42, 5) == 3
    assert Params.small_scale(local_k=3).k_for(42, 7) == 3
    # Split-or-Johnson: HBD Prop. 5 "(6 log|V1|)^{3/2}"; d = d1 or 2s, s the smallest
    # integer with C(|V2|, s) > |V1'| (HBD eq. (7) has s = 3 ceil(l))
    soj = SOJParams()
    assert soj.small_v2_bound(14) == 0                    # the small-V2 step is disabled
    s14 = (6 * __import__("math").log(14)) ** 1.5
    assert s14 < SOJParams(small_v2=None).small_v2_bound(14) <= s14 + 1 + 1e-6
    assert soj.arity(d1=5, n1p=100, n2=20) == 4           # C(20, 2) = 190 > 100: s = 2
    assert soj.arity(d1=4, n1p=100, n2=20) == 4           # d1 <= 2s -> d = d1
    assert soj.arity(d1=3, n1p=100, n2=20) == 3           # the search stops at 2s >= d1
    assert soj.arity(d1=40, n1p=10 ** 6, n2=10 ** 4) == 4   # C(10^4, 2) > 10^6
    assert soj.arity(d1=40, n1p=10 ** 12, n2=10 ** 4) == 8  # C(10^4, 3) < 10^12 < C(10^4, 4)
    for n2 in (30, 100, 1000):
        for n1p in (n2 + 1, n2 ** 2, n2 ** 3 + 7):
            d = soj.arity(d1=n2 // 2, n1p=n1p, n2=n2)
            s = d // 2
            assert d == n2 // 2 or (comb(n2, s) > n1p and comb(n2, s - 1) <= n1p)
            cl = next(j for j in range(1, 50) if n2 ** j >= n1p)
            assert d <= 6 * cl
    assert SOJParams.small_scale().arity(d1=40, n1p=10 ** 6, n2=10 ** 4) == 4
    assert SOJParams.small_scale().small_v2_bound(14) == 3


# ------------------------------------------------- paper preset end-to-end

def _atlas(n):
    return [g for g in graph_atlas_g() if g.number_of_nodes() == n]


@pytest.mark.parametrize("n", [3, 4, 5])
def test_paper_preset_all_tiny_graphs_vs_brute_force(n):
    """|G| = n! <= C_0 = 5040: Reduce-to-Johnson line 2 (brute force), exact."""
    rng = random.Random(n)
    for g in _atlas(n):
        e = edges_of(g)
        inst = GraphInstance(n)
        s = Solver(Params.paper())
        C = s.iso(inst.G, inst.string(e), inst.string(e))
        assert C.group.order() == brute_aut_order(e, n)
        e2, _ = relabel(e, n, rng)
        iso = graph_isomorphism(e, n, e2, n, params=Params.paper())
        assert iso is not None
        check_isomorphism(e, e2, n, iso)
        assert s.stats["johnson_case"] == 0


@pytest.mark.parametrize("name,g", [
    ("Q3", nx.hypercube_graph(3)),
    ("K4,4", nx.complete_bipartite_graph(4, 4)),
    ("C8", nx.cycle_graph(8)),
    ("Wagner", nx.circulant_graph(8, [1, 4])),
    ("random", nx.gnm_random_graph(8, 12, seed=3)),
    ("2K4", nx.disjoint_union(nx.complete_graph(4), nx.complete_graph(4))),
])
def test_paper_preset_8_vertices_enumerates_sym(name, g):
    """8 vertices: |G| = 8! > C_0 and 8! < 28^{1+log2 28} (Cameron-Maroti bound on
    the 28 singleton blocks), so Reduce-to-Johnson line 5 enumerates Sym(8) by the
    strong Luks reduction -- the paper's prescription at this size."""
    e = edges_of(g)
    n = 8
    inst = GraphInstance(n)
    x = inst.string(e)
    s = Solver(Params.paper())
    C = s.iso(inst.G, x, x)
    assert C.group.order() == brute_aut_order(e, n)
    for h in C.group.gens:
        assert maps_string(x, x, h)
    assert s.stats["strong_luks"] >= 1 and s.stats["luks_small_quotient"] >= 1
    assert s.stats["johnson_case"] == 0 and s.stats["brute_force"] == 0
    assert s.stats["calls"] >= factorial(8)   # one recursive call per element of Sym(8)
    e2, perm = relabel(e, n, random.Random(len(name)))
    y = inst.string(e2)
    C2 = s.iso(inst.G, x, y)
    assert C2 is not None and maps_string(x, y, C2.rep) and C2.group.order() == C.group.order()
    # a non-isomorphic graph with the same number of edges
    h = nx.gnm_random_graph(n, len(e), seed=11)
    if not nx.is_isomorphic(g, h):
        assert s.iso(inst.G, x, inst.string(edges_of(h))) is None


def test_paper_preset_is_the_api_default():
    rng = random.Random(77)
    for n in (6, 7):
        for _ in range(3):
            g = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
            e = edges_of(g)
            e2, _ = relabel(e, n, rng)
            iso = graph_isomorphism(e, n, e2, n)           # no params: Params.paper()
            assert iso is not None
            check_isomorphism(e, e2, n, iso)
            gens, order = graph_automorphisms(e, n)
            assert order == brute_aut_order(e, n)
            h = nx.gnp_random_graph(n, 0.5, seed=rng.randrange(1 << 30))
            if h.number_of_edges() == len(e):
                assert (graph_isomorphism(e, n, edges_of(h), n) is not None) == nx.is_isomorphic(g, h)


# ------------------------------------------- SI with a very small Gamma (paper)

def _johnson_on_pairs_with_kernel(m):
    """Sym(m) on pairs(m) x {0,1} extended by the kernel (Z_2)^P swapping inside
    the standard blocks {(T,0),(T,1)} (t = 2, |Gamma| = m)."""
    pairs = pairs_of(m)
    P = len(pairs)
    n = 2 * P
    gens = [tuple(g[u % P] + P * (u // P) for u in range(n)) for g in johnson_group_gens(m, 2)]
    gens.append(tuple((u + P) % n if u % P == 0 else u for u in range(n)))
    return PermGroup(n, gens), pairs, P


def _reference_aut_order(m, x, P, pairs):
    col = {T: tuple(sorted((x[i], x[i + P]))) for i, T in enumerate(pairs)}
    cnt = sum(1 for p in itertools.permutations(range(m))
              if all(col[T] == col[tuple(sorted((p[T[0]], p[T[1]])))] for T in pairs))
    eq = sum(1 for i in range(P) if x[i] == x[i + P])
    return cnt * 2 ** eq


def _reference_iso_exists(m, x, y, P, pairs):
    cx = {T: tuple(sorted((x[i], x[i + P]))) for i, T in enumerate(pairs)}
    cy = {T: tuple(sorted((y[i], y[i + P]))) for i, T in enumerate(pairs)}
    return any(all(cx[T] == cy[tuple(sorted((p[T[0]], p[T[1]])))] for T in pairs)
               for p in itertools.permutations(range(m)))


@pytest.mark.parametrize("m", [6, 7])
def test_paper_preset_small_gamma_enumerates_sym_gamma(m):
    """|Gamma| = m < ell(n) = 90: the papers enumerate Sym(Gamma) (Babai Sec. 1.2 /
    3.4, HBD Sec. 3.1); here the quotient S^{(2)}(Gamma) on the binom(m,2) blocks
    has order m! < binom(m,2)^{1+log2 binom(m,2)}, so Reduce-to-Johnson line 5
    does exactly that (m! cosets of the kernel, Chain Rule inside)."""
    G, pairs, P = _johnson_on_pairs_with_kernel(m)
    rng = random.Random(m)
    x = tuple(rng.randrange(2) for _ in range(G.n))
    s = Solver(Params.paper())
    C = s.iso(G, x, x)
    assert C.group.order() == _reference_aut_order(m, x, P, pairs)
    for h in C.group.gens:
        assert maps_string(x, x, h)
    assert s.stats["johnson_case"] == 0 and s.stats["imprimitive_johnson"] == 0
    assert s.stats["strong_luks"] >= 1 and s.stats["chain_rule"] >= factorial(m)
    g = tuple(range(G.n))
    for _ in range(40):
        g = mul(g, rng.choice(G.gens))
    y = act_string(x, g)
    C2 = string_isomorphism(G, x, y)                        # default params = paper
    assert C2 is not None and maps_string(x, y, C2.rep) and C2.group.order() == C.group.order()
    for h in C2.group.gens:
        assert maps_string(x, x, h)
    # random strings with the same letter counts: ISO_G(x, y2) is nonempty iff some
    # permutation of Gamma carries the block colours {x(T,0), x(T,1)} onto those of y2
    checked = 0
    while checked < 3:
        y2 = list(x)
        rng.shuffle(y2)
        y2 = tuple(y2)
        ref = _reference_iso_exists(m, x, y2, P, pairs)
        assert (s.iso(G, x, y2) is not None) == ref
        checked += 1


# ---------------------------------------- non-Cameron quotient above the bound

def _m12():
    def cyc(*cs):
        return from_cycles(12, [[c - 1 for c in cc] for cc in cs])
    return PermGroup(12, [cyc([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]), cyc([3, 7, 11, 8], [4, 10, 5, 6]),
                          cyc([1, 12], [2, 11], [3, 6], [4, 8], [5, 9], [7, 10])])


def test_mathieu_m12_is_enumerated_as_a_bounded_exception():
    """M_12 (order 95040 >= 12^{1+log2 12}) is primitive but not a Cameron group:
    Thm. 3.2.3 only applies for m >= 25.  Both presets enumerate it (an absolute
    constant); the identification correctly fails and nothing is raised."""
    M12 = _m12()
    assert M12.order() == 95040 > 12 ** (1 + log2(12)) > Params.luks_threshold(12)
    assert recognize_johnson(M12) is None and recognize_cameron(M12) is None
    x = (0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3)
    ref = sorted(g for g in M12.elements() if maps_string(x, x, g))
    for P in (Params.paper(), Params.small_scale()):
        s = Solver(P)
        M = _m12()
        C = s.iso(M, x, x)
        assert sorted(C.group.elements()) == ref
        assert s.stats["fallback_enumeration"] == 1 and s.stats["fallback_enumeration_unexpected"] == 0
        y = act_string(x, M12.gens[2])
        C2 = s.iso(M, x, y)
        assert C2 is not None and maps_string(x, y, C2.rep)


# ------------------------------------------------- Cameron groups, s >= 2, t >= 2

def _wreath_johnson(k, t, s=2):
    """S_k^{(t)} wr S_s in product action on binom(k,t)^s points: Sym(k) on the
    first coordinate and the cyclic shift of the coordinates."""
    subs = subsets_of(k, t)
    idx = {T: i for i, T in enumerate(subs)}
    pts = list(itertools.product(range(len(subs)), repeat=s))
    pidx = {p: i for i, p in enumerate(pts)}
    gens = []
    for tau in (from_cycles(k, [[0, 1]]), from_cycles(k, [list(range(k))])):
        img = {i: idx[tuple(sorted(tau[v] for v in T))] for T, i in idx.items()}
        gens.append(tuple(pidx[(img[p[0]],) + p[1:]] for p in pts))
    gens.append(tuple(pidx[p[1:] + p[:1]] for p in pts))
    return PermGroup(len(pts), gens), pts, subs


@pytest.mark.parametrize("k,t", [(5, 2), (6, 2)])
def test_recognize_cameron_product_action_t2(k, t):
    G, pts, subs = _wreath_johnson(k, t)
    c = comb(k, t)
    assert G.n == c ** 2 and G.order() == 2 * factorial(k) ** 2
    assert recognize_johnson(G) is None and recognize_hamming(G) is None
    cs = recognize_cameron(G)
    assert isinstance(cs, CameronStructure) and (cs.k, cs.t, cs.s, cs.c) == (k, t, 2, c)
    # the coordinates: Sym(k) on coordinate 0 fixes both classes, the shift swaps them
    assert cs.class_images[0] == (0, 1) and cs.class_images[1] == (0, 1) and cs.class_images[2] == (1, 0)
    N = PermGroup(G.n, cs.N_gens)
    assert N.order() == factorial(k) ** 2
    # fibers = the points with a common first (or second) coordinate
    fib = {frozenset(f) for f in cs.fibers}
    coord = [{frozenset(i for i, p in enumerate(pts) if p[j] == a) for a in range(c)} for j in range(2)]
    assert fib in coord
    assert len(cs.fibers) == c and all(len(f) == c for f in cs.fibers)
    # layers = rows and columns, each a copy of J(k, t), two parallel classes
    rows = {frozenset(i for i, p in enumerate(pts) if p[0] == a) for a in range(c)}
    cols = {frozenset(i for i, p in enumerate(pts) if p[1] == a) for a in range(c)}
    assert set(cs.layers) == rows | cols
    row_classes = {cl for L, cl in zip(cs.layers, cs.layer_class) if L in rows}
    col_classes = {cl for L, cl in zip(cs.layers, cs.layer_class) if L in cols}
    assert len(row_classes) == 1 and len(col_classes) == 1 and row_classes != col_classes
    # N acts on the fibers as the Johnson group S_k^{(t)}
    Nact, _ = N.induced_action(cs.fibers)
    jh = recognize_johnson(Nact)
    assert jh is not None and (jh.m, jh.t) == (k, t)
    # a relabelled copy is recognised too
    perm = list(range(G.n))
    random.Random(k).shuffle(perm)
    inv = {perm[i]: i for i in range(G.n)}
    G2 = PermGroup(G.n, [tuple(perm[g[inv[i]]] for i in range(G.n)) for g in G.gens])
    cs2 = recognize_cameron(G2)
    assert cs2 is not None and (cs2.k, cs2.t, cs2.s) == (k, t, 2)


def test_cameron_t2_string_isomorphism_100_points_vs_brute_force():
    """S_5^{(2)} wr S_2 on 100 points (order 28800 > the small-scale cap): the
    product action is recognised, the weak Luks reduction passes to
    S_5^{(2)} x S_5^{(2)} (two cosets), which has the Johnson quotient on the
    fibers; the full coset ISO_G(x, y) is compared with brute force."""
    G, pts, subs = _wreath_johnson(5, 2)
    rng = random.Random(100)
    strings = [tuple(len(set(subs[p[0]]) & set(subs[p[1]])) for p in pts),   # Aut = diagonal Sym(5) x swap
               tuple(1 if p[0] == p[1] else 0 for p in pts),
               tuple(rng.randrange(2) for _ in pts)]
    for x in strings:
        s = Solver(Params.small_scale())
        C = s.iso(G, x, x)
        ref = sorted(g for g in G.elements() if maps_string(x, x, g))
        assert sorted(C.group.elements()) == ref
        assert s.stats["cameron_product_action"] >= 1 and s.stats["cameron_t2_s2"] >= 1
        assert s.stats["cameron_reduction"] >= 1
        g = tuple(range(G.n))
        for _ in range(25):
            g = mul(g, rng.choice(G.gens))
        y = act_string(x, g)
        C2 = s.iso(G, x, y)
        assert C2 is not None and maps_string(x, y, C2.rep)
        assert sorted(C2.elements()) == sorted(h for h in G.elements() if maps_string(x, y, h))
        y2 = tuple(rng.randrange(2) for _ in pts)
        if sorted(y2) == sorted(x):
            assert (s.iso(G, x, y2) is not None) == any(maps_string(x, y2, h) for h in G.elements())
    assert len(strings[0]) == 100


def test_cameron_t2_string_isomorphism_225_points():
    """S_6^{(2)} wr S_2 on 225 points (order 1036800).  x(T1, T2) = |T1 cap T2|:
    (g, h) tau^e preserves x iff g(T) = h(T) for all 2-sets T (take T1 = T2 = T),
    i.e. g = h, so |Aut| = |Sym(6)| * 2 = 1440."""
    G, pts, subs = _wreath_johnson(6, 2)
    x = tuple(len(set(subs[p[0]]) & set(subs[p[1]])) for p in pts)
    s = Solver(Params.small_scale())
    C = s.iso(G, x, x)
    assert C.group.order() == 2 * factorial(6)
    for h in C.group.gens:
        assert maps_string(x, x, h)
    assert s.stats["cameron_t2_s2"] >= 1 and s.stats["johnson_case"] == 0
    # the identification is also what Reduce-to-Johnson would need with the papers'
    # thresholds... except that the papers' bound 225^{1+log2 225} exceeds |G|, so
    # Params.paper() prescribes the enumeration of G there (not run: 10^6 cosets).
    assert G.order() < Params.luks_threshold(225)
    rng = random.Random(225)
    g = tuple(range(G.n))
    for _ in range(30):
        g = mul(g, rng.choice(G.gens))
    y = act_string(x, g)
    C2 = s.iso(G, x, y)
    assert C2 is not None and maps_string(x, y, C2.rep) and C2.group.order() == 1440
