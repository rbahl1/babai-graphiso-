"""String Isomorphism (Babai Thm. 1.1.1 / Def. 3.1.2) tests.

* small groups against brute force (the full coset ISO_G(x, y) is compared
  element by element), with the brute-force threshold disabled so that the
  Luks machinery (Chain Rule, strong Luks reduction) really runs;
* the identification of Johnson groups (``recognize_johnson``) and of the
  product action of Cameron groups (``recognize_hamming``);
* Johnson-group instances Sym(m) acting on 2-subsets, m = 7..9, forced through
  the Johnson case (Extended Design Lemma, Split-or-Johnson);
* imprimitive Johnson instances (standard blocks of size 2) that execute the
  Local Certificates procedure and each case of AggregateCertificates
  (Cases 1, 2a with the top action, 3 with certificate comparison);
* a graph instance (the Johnson graph J(6,2)) that runs Local Certificates.

The counters (``Solver.stats`` and ``babai_gi.soj.STATS``) prove that the
respective branches executed.
"""

import itertools
import random
from math import comb, factorial

import pytest

from babai_gi import soj
from babai_gi.graph import GraphInstance
from babai_gi.group import PermGroup
from babai_gi.johnson import johnson_group_gens, pairs_of, recognize_hamming, recognize_johnson, subsets_of
from babai_gi.main import Params, Solver, string_isomorphism
from babai_gi.perm import act_string, from_cycles, maps_string, mul

from .helpers import edges_of, johnson_graph, paley

# small-scale constants (the library default Params.paper() degenerates to enumeration at these sizes)
NO_BRUTE = Params.small_scale(brute_force_order=1)
FORCE_JOHNSON = Params.small_scale(brute_force_order=1, quotient_enum_limit=1, min_gamma=6)


# ------------------------------------------------------------ small groups

def sym_gens(points, n):
    pts = list(points)
    out = [from_cycles(n, [pts[:2]])]
    if len(pts) > 2:
        out.append(from_cycles(n, [pts]))
    return out


def wreath_s2_s2_s2():
    """S2 wr S2 wr S2 on 8 points (order 128): swap within pairs, swap pairs, swap halves."""
    n = 8
    return PermGroup(n, [from_cycles(n, [[0, 1]]), from_cycles(n, [[0, 2], [1, 3]]),
                         from_cycles(n, [[0, 4], [1, 5], [2, 6], [3, 7]])])


def wreath_s3_s2():
    n = 6
    return PermGroup(n, sym_gens([0, 1, 2], n) + [from_cycles(n, [[0, 3], [1, 4], [2, 5]])])


def agl17():
    """AGL(1,7) = {x -> ax + b} on Z_7 (order 42)."""
    return PermGroup(7, [tuple((x + 1) % 7 for x in range(7)), tuple((3 * x) % 7 for x in range(7))])


def pgl25():
    """PGL(2,5) acting on the projective line over F_5 (6 points, order 120)."""
    pts = list(range(5)) + ["inf"]

    def mobius(a, b, c, d):
        img = []
        for x in pts:
            if x == "inf":
                y = "inf" if c == 0 else (a * pow(c, -1, 5)) % 5
            else:
                den = (c * x + d) % 5
                y = "inf" if den == 0 else ((a * x + b) * pow(den, -1, 5)) % 5
            img.append(pts.index(y))
        return tuple(img)

    return PermGroup(6, [mobius(1, 1, 0, 1), mobius(2, 0, 0, 1), mobius(0, 1, 1, 0)])


def intransitive_product():
    """S3 on {0,1,2} x D4 on {3..6} x C2 on {7,8} (order 6*8*2 = 96)."""
    n = 9
    gens = sym_gens([0, 1, 2], n)
    gens.append(from_cycles(n, [[3, 4, 5, 6]]))
    gens.append(from_cycles(n, [[4, 6]]))
    gens.append(from_cycles(n, [[7, 8]]))
    return PermGroup(n, gens)


GROUPS = [
    ("C7", PermGroup(7, [from_cycles(7, [list(range(7))])])),
    ("D6", PermGroup(6, [from_cycles(6, [list(range(6))]), tuple((-i) % 6 for i in range(6))])),
    ("S3 wr S2", wreath_s3_s2()),
    ("S2 wr S2 wr S2", wreath_s2_s2_s2()),
    ("AGL(1,7)", agl17()),
    ("PGL(2,5)", pgl25()),
    ("S3 x D4 x C2", intransitive_product()),
    ("S5 on 5", PermGroup(5, sym_gens(range(5), 5))),
    ("A5 on 6 (PSL(2,5))", PermGroup(6, [g for g in pgl25().gens[:1]] + [mul(pgl25().gens[2], pgl25().gens[2])])),
]


def brute_iso(G, x, y):
    return sorted(g for g in G.elements() if maps_string(x, y, g))


@pytest.mark.parametrize("name,G", GROUPS, ids=[g[0] for g in GROUPS])
def test_small_groups_against_brute_force(name, G):
    rng = random.Random(len(name))
    n = G.n
    assert G.order() <= 5040
    for trial in range(6):
        alphabet = rng.choice([2, 2, 3])
        x = tuple(rng.randrange(alphabet) for _ in range(n))
        if trial % 2 == 0:
            g = tuple(range(n))
            for _ in range(20):
                g = mul(g, rng.choice(G.gens))
            y = act_string(x, g)
        else:
            y = tuple(rng.randrange(alphabet) for _ in range(n))
        ref = brute_iso(G, x, y)
        C = string_isomorphism(G, x, y, params=NO_BRUTE)
        if not ref:
            assert C is None
            continue
        assert C is not None
        assert maps_string(x, y, C.rep)
        assert sorted(C.elements()) == ref
        assert C.group.order() == len(ref)
        # the returned group is Aut_G(x)
        assert sorted(C.group.elements()) == brute_iso(G, x, x)


def test_luks_machinery_runs_without_brute_force():
    G = wreath_s2_s2_s2()
    x = (0, 1, 0, 1, 0, 0, 1, 1)
    s = Solver(NO_BRUTE)
    C = s.iso(G, x, x)
    assert C.group.order() == len(brute_iso(G, x, x))
    assert s.stats["chain_rule"] >= 1 and s.stats["strong_luks"] >= 1
    assert s.stats["brute_force"] == 0


# ------------------------------------------------- recognizing Johnson groups

@pytest.mark.parametrize("m,t", [(7, 2), (8, 2), (9, 2), (7, 3), (10, 2)])
def test_recognize_johnson_group(m, t):
    subs = subsets_of(m, t)
    G = PermGroup(len(subs), johnson_group_gens(m, t))
    jh = recognize_johnson(G)
    assert jh is not None and (jh.m, jh.t) == (m, t)
    # the recovered labelling is consistent with the action: point i <-> t-subset
    index = {}
    for i, T in enumerate(jh.T_of_point):
        assert len(T) == t
        index[T] = i
    assert len(index) == len(subs)
    for g, tau in zip(G.gens, jh.phi_gens):
        for i in range(len(subs)):
            assert index[frozenset(tau[v] for v in jh.T_of_point[i])] == g[i]


def test_recognize_alternating_johnson_group():
    m, t = 7, 2
    subs = subsets_of(m, t)
    index = {T: i for i, T in enumerate(subs)}
    from babai_gi.johnson import induced_on_subsets
    gens = [induced_on_subsets(from_cycles(m, [[0, 1, 2]]), subs, index),
            induced_on_subsets(from_cycles(m, [list(range(m))]), subs, index)]
    G = PermGroup(len(subs), gens)
    assert G.order() == factorial(m) // 2
    jh = recognize_johnson(G)
    assert jh is not None and (jh.m, jh.t) == (m, t)


def test_recognize_giant_and_non_johnson():
    G = PermGroup(9, sym_gens(range(9), 9))
    jh = recognize_johnson(G)
    assert jh is not None and jh.t == 1 and jh.m == 9
    assert recognize_johnson(agl17()) is None
    assert recognize_johnson(pgl25()) is None


def test_recognize_hamming_product_action():
    """S3 wr S2 in product action on [3]^2 (9 points): a Cameron group with s = 2."""
    pts = [(a, b) for a in range(3) for b in range(3)]
    idx = {p: i for i, p in enumerate(pts)}
    gens = [tuple(idx[((a + 1) % 3, b)] for a, b in pts), tuple(idx[(1 if a == 0 else 0 if a == 1 else 2, b)] for a, b in pts),
            tuple(idx[(b, a)] for a, b in pts)]
    G = PermGroup(9, gens)
    assert G.order() == 72
    hs = recognize_hamming(G)
    assert hs is not None and (hs.c, hs.s) == (3, 2)
    assert recognize_johnson(G) is None
    N = PermGroup(9, hs.N_gens)
    assert N.order() == 36
    assert recognize_hamming(PermGroup(9, sym_gens(range(9), 9))) is None


# ---------------------------------------------- primitive Johnson instances

def _pairs_string(m, edges, letters=(0, 1)):
    E = {tuple(sorted(e)) for e in edges}
    return tuple(letters[1] if T in E else letters[0] for T in pairs_of(m))


def _nx_colored_aut(m, x):
    """|Aut| of the string x on pairs(m) under Sym(m) = automorphisms of the edge-coloured complete graph."""
    cnt = 0
    pairs = pairs_of(m)
    col = {T: x[i] for i, T in enumerate(pairs)}
    for p in itertools.permutations(range(m)):
        if all(col[T] == col[tuple(sorted((p[T[0]], p[T[1]])))] for T in pairs):
            cnt += 1
    return cnt


@pytest.mark.parametrize("m,graph,expected", [
    (7, [(i, (i + 1) % 7) for i in range(7)], 14),                                  # C7: dihedral
    (8, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (6, 7)], 72 * 2),           # 2K3 + K2
    (9, edges_of(paley(9)), 1296),                                                   # Paley(9) = 3x3 rook's graph (UPCC)
])
def test_johnson_group_on_pairs_string_isomorphism(m, graph, expected):
    G = PermGroup(comb(m, 2), johnson_group_gens(m, 2))
    assert getattr(G, "johnson_hint", None) is None  # the Johnson structure must be re-identified
    x = _pairs_string(m, graph)
    soj.STATS.clear()
    s = Solver(FORCE_JOHNSON)
    C = s.iso(G, x, x)
    assert C.group.order() == expected
    if m <= 8:
        assert _nx_colored_aut(m, x) == expected
    assert s.stats["johnson_case"] >= 1 and s.stats["primitive_johnson"] >= 1
    assert s.stats["brute_force"] == 0
    assert soj.STATS["extended_design_lemma"] >= 1
    # isomorphism with a shifted copy, with the full coset
    rng = random.Random(m)
    g = tuple(range(G.n))
    for _ in range(30):
        g = mul(g, rng.choice(G.gens))
    y = act_string(x, g)
    C2 = Solver(FORCE_JOHNSON).iso(G, x, y)
    assert C2 is not None and maps_string(x, y, C2.rep) and C2.group.order() == expected
    for h in C2.group.gens:
        assert maps_string(x, x, h)
    # a non-isomorphic string with the same letter counts
    y2 = _pairs_string(m, [(0, i) for i in range(1, len(graph) + 1)]) if len(graph) < m else None
    if y2 is not None and sorted(y2) == sorted(x):
        assert Solver(FORCE_JOHNSON).iso(G, x, y2) is None


def test_paley13_string_runs_split_or_johnson():
    """Paley(13) is a uniprimitive coherent configuration (rank 3): the Extended
    Design Lemma must hand it to UPCC Split-or-Johnson (Babai Thm. 7.3.1)."""
    m = 13
    inst = GraphInstance(m)
    x = inst.string(edges_of(paley(13)))
    soj.STATS.clear()
    s = Solver(Params.small_scale())
    C = s.iso(inst.G, x, x)
    assert C.group.order() == 78
    assert s.stats["primitive_johnson"] >= 1
    assert soj.STATS["extended_design_lemma"] >= 1
    assert soj.STATS["edl_upcc"] >= 1 and soj.STATS["upcc_soj"] >= 1
    # Paley(13) has valency 6 = (m-1)/2: individualizing one vertex already yields
    # a 3/4-coloring (Lemma 7.4.1 terminates before the bipartite case); the
    # bipartite / coherent procedures are unit-tested directly in test_soj.py.
    assert soj.STATS["upcc_to_bipartite"] == 0


# -------------------------------------------- imprimitive Johnson instances

def johnson_on_pairs_with_kernel(m, kernel="full"):
    """G on Omega = pairs(m) x {0,1}: Sym(m) acting on the pairs (both copies at
    once) extended by a kernel that swaps the two points of a block.  The blocks
    B_T = {(T,0),(T,1)} are the standard blocks of Babai Thm. 8.5.1 with t = 2;
    the quotient action is the Johnson group S^(2)(m)."""
    pairs = pairs_of(m)
    P = len(pairs)
    n = 2 * P
    gens = [tuple(g[u % P] + P * (u // P) for u in range(n)) for g in johnson_group_gens(m, 2)]
    if kernel == "full":        # (Z_2)^P: swap inside block 0 (its conjugates give all blocks)
        gens.append(tuple((u + P) % n if u % P == 0 else u for u in range(n)))
    elif kernel == "diag":      # Z_2: swap inside all blocks simultaneously
        gens.append(tuple((u + P) % n for u in range(n)))
    return PermGroup(n, gens), pairs, P


def string_from_graph(m, edges, letters=((0, 0), (1, 1))):
    pairs = pairs_of(m)
    P = len(pairs)
    E = {tuple(sorted(e)) for e in edges}
    x = [0] * (2 * P)
    for i, T in enumerate(pairs):
        a, b = letters[1] if T in E else letters[0]
        x[i], x[i + P] = a, b
    return tuple(x)


def reference_aut_order_full_kernel(m, x, P, pairs):
    """Brute force: an automorphism is a permutation of [m] preserving the
    colour {x(T,0), x(T,1)} (multiset) of every pair, combined with a swap in
    every block whose two letters are equal (2^(#equal blocks) choices)."""
    col = {T: tuple(sorted((x[i], x[i + P]))) for i, T in enumerate(pairs)}
    cnt = sum(1 for p in itertools.permutations(range(m))
              if all(col[T] == col[tuple(sorted((p[T[0]], p[T[1]])))] for T in pairs))
    eq = sum(1 for i in range(P) if x[i] == x[i + P])
    return cnt * 2 ** eq


def _run_imprimitive(m, edges, local_k):
    G, pairs, P = johnson_on_pairs_with_kernel(m, "full")
    x = string_from_graph(m, edges)
    params = Params.small_scale(brute_force_order=1, quotient_enum_limit=1, min_gamma=6, local_k=local_k)
    soj.STATS.clear()
    s = Solver(params)
    C = s.iso(G, x, x)
    assert C.group.order() == reference_aut_order_full_kernel(m, x, P, pairs)
    for h in C.group.gens:
        assert maps_string(x, x, h)
    assert s.stats["imprimitive_johnson"] >= 1
    assert s.stats["lc_full"] + s.stats["lc_notfull"] >= 1
    # an isomorphism to a shifted copy (exercises the x != y path of the same machinery)
    rng = random.Random(m + local_k)
    g = tuple(range(G.n))
    for _ in range(40):
        g = mul(g, rng.choice(G.gens))
    y = act_string(x, g)
    C2 = s.iso(G, x, y)
    assert C2 is not None and maps_string(x, y, C2.rep) and C2.group.order() == C.group.order()
    return s


def test_local_certificates_case_2a_top_action():
    """Quotient graph K4 + 3 isolated vertices: the 4-set of the K4 is full, F acts
    on it as Sym(4) > Alt(4): Case 2a (large symmetry) and the top action (Sec. 9)."""
    s = _run_imprimitive(7, list(itertools.combinations(range(4), 2)), local_k=4)
    assert s.stats["lc_full"] >= 1
    assert s.stats["agg_case_2a"] >= 1 and s.stats["case_2a"] >= 1
    assert s.stats["top_action"] >= 1


def test_local_certificates_case_1_orbit_coloring():
    """Quotient graph 2K3 + K1 with k = 3: the two triangles are full test sets,
    F has two orbits of length 3 = m/2 (not > m/2): Case 1 (colour by orbit length)."""
    s = _run_imprimitive(7, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)], local_k=3)
    assert s.stats["lc_full"] >= 2
    assert s.stats["agg_case_1"] >= 1


def test_local_certificates_case_3_certificate_comparison():
    """Quotient graph C5 + 2K1 with k = 3: no test set is full (|S| = 0 < m/2):
    Case 3, the k-ary relation from comparing certificates (Prop. 10.1.11)
    followed by the Extended Design Lemma."""
    s = _run_imprimitive(7, [(i, (i + 1) % 5) for i in range(5)], local_k=3)
    assert s.stats["lc_notfull"] >= 1 and s.stats["lc_full"] == 0
    assert s.stats["agg_case_3"] >= 1 and s.stats["case_3"] >= 1
    assert s.stats["cert_compare"] >= 1 and s.stats["cert_classes"] >= 2
    assert soj.STATS["extended_design_lemma"] >= 1


@pytest.mark.slow
def test_local_certificates_random_string_k4():
    G, pairs, P = johnson_on_pairs_with_kernel(7, "full")
    rng = random.Random(5)
    x = tuple(rng.randrange(2) for _ in range(G.n))
    s = Solver(Params.small_scale(brute_force_order=1, quotient_enum_limit=1, min_gamma=6, local_k=4))
    C = s.iso(G, x, x)
    assert C.group.order() == reference_aut_order_full_kernel(7, x, P, pairs)
    assert s.stats["agg_case_3"] >= 1 and s.stats["cert_compare"] >= 1


def test_diagonal_kernel_instance():
    G, pairs, P = johnson_on_pairs_with_kernel(7, "diag")
    rng = random.Random(3)
    x = tuple(rng.randrange(2) for _ in range(G.n))
    s = Solver(FORCE_JOHNSON)
    C = s.iso(G, x, x)
    ref = brute_iso(G, x, x)
    assert C.group.order() == len(ref) and sorted(C.group.elements()) == ref
    assert s.stats["johnson_case"] >= 1


# ------------------------------------------------- graph instance with LC

def test_graph_instance_runs_local_certificates():
    """The Johnson graph J(6,2) (15 vertices): in its recursion the group becomes
    imprimitive with a Johnson quotient, so AggregateCertificates / Local
    Certificates run on a genuine graph instance (Case 2b here)."""
    g = johnson_graph(6, 2)
    n = g.number_of_nodes()
    inst = GraphInstance(n)
    x = inst.string(edges_of(g))
    s = Solver(Params.small_scale())
    C = s.iso(inst.G, x, x)
    assert C.group.order() == 720
    assert s.stats["imprimitive_johnson"] >= 1
    assert s.stats["lc_full"] >= 1 and s.stats["lc_notfull"] >= 1
    assert s.stats["agg_case_2b"] >= 1 and s.stats["case_2b"] >= 1
