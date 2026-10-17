"""Structured graph families: regular graphs, strongly regular graphs
(Paley, Shrikhande vs. 4x4 rook's graph), Johnson graphs, hypercubes,
Petersen, complete multipartite graphs, disjoint unions, asymmetric trees."""

from math import factorial

import networkx as nx
import pytest

from babai_gi.main import Params, Solver

from .graphs import (asymmetric_tree, check_aut, check_pair, complete_multipartite, disjoint_union, hypercube,
                     johnson_graph, paley, random_regular, relabel, rook, shrikhande)


# ---------------------------------------------------------------- regular
@pytest.mark.parametrize("d,n,seed", [(3, 8, 1), (3, 10, 2), (4, 9, 3), (3, 12, 4), (4, 10, 5), (5, 12, 6), (3, 14, 7)])
def test_random_regular_planted(d, n, seed):
    g = random_regular(d, n, seed)
    g2, _ = relabel(g, seed + 5)
    check_pair(g, g2, True)


@pytest.mark.parametrize("d,n,seed", [(3, 8, 21), (3, 10, 22), (4, 10, 23), (3, 12, 24), (4, 12, 25)])
def test_random_regular_pairs(d, n, seed):
    """Two independently drawn regular graphs of the same degree; compared with NetworkX."""
    g = random_regular(d, n, seed)
    h = random_regular(d, n, seed + 500)
    check_pair(g, h)
    check_aut(g)


# ------------------------------------------------------ strongly regular
def test_shrikhande_vs_rook():
    S, R = shrikhande(), rook(4)
    # same parameters srg(16, 6, 2, 2): 2-WL cannot distinguish them
    for g in (S, R):
        assert all(d == 6 for _, d in g.degree())
    check_pair(S, R, False)


def test_shrikhande_and_rook_relabeled():
    S, R = shrikhande(), rook(4)
    S2, _ = relabel(S, 11)
    R2, _ = relabel(R, 12)
    check_pair(S, S2, True)
    check_pair(R, R2, True)


def test_shrikhande_and_rook_automorphisms():
    assert check_aut(shrikhande(), 192) == 192
    assert check_aut(rook(4), 1152) == 1152


@pytest.mark.parametrize("q", [5, 9, 13])
def test_paley(q):
    g = paley(q)
    g2, _ = relabel(g, q)
    check_pair(g, g2, True)
    # Paley graphs are self-complementary
    check_pair(g, nx.complement(g), True)
    expected = {5: 10, 9: 72, 13: 78}[q]
    check_aut(g, expected)


def test_paley9_vs_rook3():
    # Paley(9) is isomorphic to the 3x3 rook's graph
    check_pair(paley(9), rook(3), True)


# ---------------------------------------------------------------- Johnson
@pytest.mark.parametrize("m", [5, 6, 7])
def test_johnson_graphs(m):
    g = johnson_graph(m, 2)
    g2, _ = relabel(g, m)
    check_pair(g, g2, True)
    # Aut(J(m,2)) = S_m for m >= 5 (m = 4: J(4,2) is the octahedron, |Aut| = 48)
    check_aut(g, factorial(m))


def test_johnson_4_2_is_octahedron():
    g = johnson_graph(4, 2)
    check_pair(g, complete_multipartite(2, 2, 2), True)
    check_aut(g, 48)


def test_johnson_6_3_vs_complement_structure():
    # J(6,3): 20 vertices, Aut = S_6 x Z_2 (complementation of 3-sets)
    g = johnson_graph(6, 3)
    g2, _ = relabel(g, 63)
    check_pair(g, g2, True)
    check_aut(g, 2 * factorial(6))


# --------------------------------------------------- large automorphism groups
@pytest.mark.parametrize("d", [2, 3, 4])
def test_hypercubes(d):
    g = hypercube(d)
    g2, _ = relabel(g, d)
    check_pair(g, g2, True)
    check_aut(g, factorial(d) * 2 ** d)


def test_petersen():
    g = nx.petersen_graph()
    g2, _ = relabel(g, 10)
    check_pair(g, g2, True)
    check_aut(g, 120)
    # Petersen = complement of the line graph of K5 = Kneser(5, 2)
    kneser = nx.complement(nx.line_graph(nx.complete_graph(5)))
    check_pair(g, nx.convert_node_labels_to_integers(kneser), True)
    # a 3-regular graph on 10 vertices that is not Petersen
    other = random_regular(3, 10, 99)
    check_pair(g, other)


@pytest.mark.parametrize("sizes,order", [((4, 4), 2 * 24 * 24), ((2, 2, 2, 2), 2 ** 4 * 24), ((2, 3, 3), 2 * 6 * 6 * 2),
                                         ((3, 3, 3), 6 ** 3 * 6), ((1, 2, 3, 4), 2 * 6 * 24), ((5, 5), 2 * 120 * 120)])
def test_complete_multipartite(sizes, order):
    g = complete_multipartite(*sizes)
    g2, _ = relabel(g, sum(sizes))
    check_pair(g, g2, True)
    check_aut(g, order)


def test_complete_multipartite_nonisomorphic():
    check_pair(complete_multipartite(2, 2, 4), complete_multipartite(2, 3, 3), False)
    check_pair(complete_multipartite(4, 4), complete_multipartite(2, 2, 2, 2), False)


@pytest.mark.parametrize("n", [8, 10, 12, 16])
def test_cycles_and_complete(n):
    c = nx.cycle_graph(n)
    c2, _ = relabel(c, n)
    check_pair(c, c2, True)
    check_aut(c, 2 * n)
    check_aut(nx.complete_graph(n), factorial(n))
    check_aut(nx.empty_graph(n), factorial(n))
    check_pair(nx.complete_graph(n), nx.empty_graph(n), False)


# ------------------------------------------------------------ disjoint unions
def test_disjoint_unions():
    g = disjoint_union(nx.complete_bipartite_graph(3, 3), nx.complete_graph(3))
    g2, _ = relabel(g, 1)
    check_pair(g, g2, True)
    check_aut(g, 72 * 6)
    # two triangles + a hexagon vs. three squares... same degrees (all 2), both 12 vertices
    a = disjoint_union(nx.cycle_graph(3), nx.cycle_graph(3), nx.cycle_graph(6))
    b = disjoint_union(nx.cycle_graph(4), nx.cycle_graph(4), nx.cycle_graph(4))
    check_pair(a, b, False)
    check_aut(a, 6 * 6 * 2 * 12)
    check_aut(b, 8 ** 3 * 6)
    # 4 copies of a small asymmetric graph: Aut = S_4
    t = asymmetric_tree(7, 3)
    u = disjoint_union(t, t, t, t)
    u2, _ = relabel(u, 4)
    check_pair(u, u2, True)
    check_aut(u, factorial(4))
    # isolated vertices
    w = disjoint_union(nx.path_graph(4), nx.empty_graph(5))
    check_aut(w, 2 * 120)


# ---------------------------------------------------------------- trees
@pytest.mark.parametrize("n,seed", [(7, 1), (9, 2), (11, 3), (13, 4), (15, 5)])
def test_asymmetric_trees(n, seed):
    t = asymmetric_tree(n, seed)
    t2, _ = relabel(t, seed + 9)
    f = check_pair(t, t2, True)
    assert f is not None
    assert check_aut(t, 1) == 1
    # a different asymmetric tree on the same number of vertices
    s = asymmetric_tree(n, seed + 100)
    check_pair(t, s)


def test_solver_stats_exercise_johnson_machinery():
    """The 16-vertex instances must go through the Johnson-case branch of the
    algorithm (Extended Design Lemma / local certificates), not brute force."""
    s = Solver(Params.small_scale())
    S, R = shrikhande(), rook(4)
    check_pair(S, R, False, solver=s)
    assert s.stats["johnson_case"] >= 1
    assert s.stats["branch_calls"] >= 1
    assert s.stats["edl_primitive"] >= 1
