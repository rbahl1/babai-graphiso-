"""Graph families: random graphs with and without planted isomorphisms, random
regular graphs, strongly regular graphs (Paley; Shrikhande vs. 4x4 rook's
graph), CFI graphs, Johnson graphs J(m,2), disjoint unions, hypercubes, the
Petersen graph, complete multipartite graphs and asymmetric trees.

Every verdict is compared with networkx.is_isomorphic, every returned mapping
is verified to carry the edge set exactly onto the edge set, and automorphism
group orders are compared with brute force (n <= 8) or with known values."""

import itertools
import random

import networkx as nx
import pytest

from babai_gi.graph import graph_automorphisms, graph_isomorphism
from babai_gi.main import Solver

from .helpers import (brute_aut_order, cfi, check_aut, check_isomorphism, edges_of, johnson_graph,
                      nx_aut_order, nx_graph, paley, relabel, rook, run_pair, shrikhande)


# ------------------------------------------------------------ random graphs

@pytest.mark.parametrize("n", [8, 9, 10, 11])
def test_random_graphs_planted_isomorphism(n):
    rng = random.Random(100 + n)
    for trial in range(4):
        p = rng.choice([0.2, 0.35, 0.5, 0.7])
        edges = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < p]
        edges2, perm = relabel(edges, n, rng)
        iso, _ = run_pair(edges, edges2, n)
        assert iso is not None


@pytest.mark.parametrize("n", [8, 9, 10])
def test_random_graphs_independent_pairs(n):
    """Two independent G(n, p) graphs with the same number of edges: usually
    non-isomorphic; the verdict must agree with networkx either way."""
    rng = random.Random(200 + n)
    done = 0
    while done < 4:
        p = rng.choice([0.3, 0.5])
        e1 = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < p]
        e2 = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < p]
        if len(e1) != len(e2):
            continue
        run_pair(e1, e2, n)
        done += 1


@pytest.mark.parametrize("d,n,seed", [(3, 8, 1), (3, 10, 2), (4, 9, 3), (4, 10, 4), (3, 12, 5), (5, 10, 6)])
def test_random_regular_graphs(d, n, seed):
    rng = random.Random(seed)
    g1 = nx.random_regular_graph(d, n, seed=seed)
    g2 = nx.random_regular_graph(d, n, seed=seed + 100)
    e1, e2 = edges_of(g1), edges_of(g2)
    e1r, _ = relabel(e1, n, rng)
    iso, _ = run_pair(e1, e1r, n)
    assert iso is not None
    run_pair(e1, e2, n)  # verdict compared with networkx
    if n <= 8:
        check_aut(e1, n, brute_aut_order(e1, n))
    else:
        check_aut(e1, n, nx_aut_order(nx_graph(e1, n)))


# --------------------------------------------------- strongly regular graphs

def test_paley_9():
    e = edges_of(paley(9))
    rng = random.Random(9)
    e2, _ = relabel(e, 9, rng)
    iso, _ = run_pair(e, e2, 9)
    assert iso is not None
    check_aut(e, 9, 1296)  # |Aut(Paley(9))| = |Aut(K3 x K3)| = 2 * 3!^2 * 2 ... = 1296 (brute force below)
    assert brute_aut_order(e, 9) == 1296


def test_paley_13():
    e = edges_of(paley(13))
    rng = random.Random(13)
    e2, _ = relabel(e, 13, rng)
    iso, solver = run_pair(e, e2, 13)
    assert iso is not None
    # Paley(13) is a UPCC (strongly regular, rank 3): Split-or-Johnson must run.
    check_aut(e, 13, 78)  # |Aut(Paley(q))| = q(q-1)/2 for prime q


def test_shrikhande_vs_rook_not_isomorphic():
    """Both are srg(16,6,2,2); 2-WL cannot tell them apart.  Must be NOT isomorphic."""
    S, R = edges_of(shrikhande()), edges_of(rook(4))
    assert len(S) == len(R) == 48
    iso, _ = run_pair(S, R, 16)
    assert iso is None


def test_shrikhande_and_rook_relabeled():
    rng = random.Random(16)
    S, R = edges_of(shrikhande()), edges_of(rook(4))
    S2, _ = relabel(S, 16, rng)
    R2, _ = relabel(R, 16, rng)
    iso, _ = run_pair(S, S2, 16)
    assert iso is not None
    iso, _ = run_pair(R, R2, 16)
    assert iso is not None


def test_shrikhande_and_rook_automorphism_groups():
    check_aut(edges_of(shrikhande()), 16, 192)
    check_aut(edges_of(rook(4)), 16, 1152)  # (4!)^2 * 2


@pytest.mark.slow
def test_paley_17():
    e = edges_of(paley(17))
    rng = random.Random(17)
    e2, _ = relabel(e, 17, rng)
    iso, _ = run_pair(e, e2, 17)
    assert iso is not None
    check_aut(e, 17, 136)


# -------------------------------------------------------------- CFI graphs

@pytest.mark.parametrize("name,base", [("C3", nx.cycle_graph(3)), ("C4", nx.cycle_graph(4)), ("P3", nx.path_graph(3))])
def test_cfi_small_bases(name, base):
    rng = random.Random(hash(name) & 0xFFFF)
    A, B = cfi(base, False), cfi(base, True)
    n = A.number_of_nodes()
    eA, eB = edges_of(A), edges_of(B)
    assert not nx.is_isomorphic(A, B)
    iso, _ = run_pair(eA, eB, n)
    assert iso is None
    eA2, _ = relabel(eA, n, rng)
    iso, _ = run_pair(eA, eA2, n)
    assert iso is not None
    if n <= 8:
        check_aut(eA, n, brute_aut_order(eA, n))
    else:
        check_aut(eA, n, nx_aut_order(A))


def test_cfi_diamond():
    base = nx.complete_graph(4)
    base.remove_edge(0, 1)
    A, B = cfi(base, False), cfi(base, True)
    n = A.number_of_nodes()
    iso, _ = run_pair(edges_of(A), edges_of(B), n)
    assert iso is None


# ---------------------------------------------------------- Johnson graphs

@pytest.mark.parametrize("m", [5, 6])
def test_johnson_graphs(m):
    g = johnson_graph(m, 2)
    n = g.number_of_nodes()
    e = edges_of(g)
    rng = random.Random(m)
    e2, _ = relabel(e, n, rng)
    iso, _ = run_pair(e, e2, n)
    assert iso is not None
    from math import factorial
    expected = factorial(m) if m != 4 else 48
    check_aut(e, n, expected)  # Aut(J(m,2)) = S_m for m >= 5


@pytest.mark.slow
def test_johnson_graph_7():
    g = johnson_graph(7, 2)
    n = g.number_of_nodes()
    e = edges_of(g)
    e2, _ = relabel(e, n, random.Random(7))
    iso, _ = run_pair(e, e2, n)
    assert iso is not None
    check_aut(e, n, 5040)


def test_johnson_vs_nonisomorphic_regular():
    """J(5,2) is the complement of the Petersen graph (6-regular on 10 vertices);
    compare with another 6-regular graph on 10 vertices."""
    g = johnson_graph(5, 2)
    h = nx.complement(nx.random_regular_graph(3, 10, seed=8))
    run_pair(edges_of(g), edges_of(h), 10)


# --------------------------------------------------------- disjoint unions

@pytest.mark.parametrize("name,g1,g2,expect", [
    ("C5+C5 vs C10", nx.disjoint_union(nx.cycle_graph(5), nx.cycle_graph(5)), nx.cycle_graph(10), False),
    ("C3+C6 vs C4+C5", nx.disjoint_union(nx.cycle_graph(3), nx.cycle_graph(6)),
     nx.disjoint_union(nx.cycle_graph(4), nx.cycle_graph(5)), False),
    ("K3,3+K3 vs itself", nx.disjoint_union(nx.complete_bipartite_graph(3, 3), nx.complete_graph(3)),
     nx.disjoint_union(nx.complete_graph(3), nx.complete_bipartite_graph(3, 3)), True),
    ("2K4 vs K4,4", nx.disjoint_union(nx.complete_graph(4), nx.complete_graph(4)), nx.complete_bipartite_graph(4, 4), False),
    ("3K3 vs K3,3,3-complement", nx.disjoint_union_all([nx.complete_graph(3)] * 3),
     nx.complement(nx.complete_multipartite_graph(3, 3, 3)), True),
    ("P2+P3+C4 vs itself", nx.disjoint_union_all([nx.path_graph(2), nx.path_graph(3), nx.cycle_graph(4)]),
     nx.disjoint_union_all([nx.cycle_graph(4), nx.path_graph(3), nx.path_graph(2)]), True),
])
def test_disjoint_unions(name, g1, g2, expect):
    n = g1.number_of_nodes()
    assert g2.number_of_nodes() == n
    e1, e2 = edges_of(g1), edges_of(g2)
    e2, _ = relabel(e2, n, random.Random(len(name)))
    iso, _ = run_pair(e1, e2, n)
    assert (iso is not None) == expect


def test_disjoint_union_automorphisms():
    g = nx.disjoint_union_all([nx.complete_graph(3)] * 3)
    check_aut(edges_of(g), 9, 6 ** 3 * 6)
    g = nx.disjoint_union(nx.cycle_graph(5), nx.cycle_graph(5))
    check_aut(edges_of(g), 10, 10 * 10 * 2)


# --------------------------------------------- hypercubes, Petersen, multipartite

def test_hypercube_q3():
    e = edges_of(nx.hypercube_graph(3))
    e2, _ = relabel(e, 8, random.Random(3))
    iso, _ = run_pair(e, e2, 8)
    assert iso is not None
    check_aut(e, 8, 48)


def test_hypercube_q4_automorphisms():
    check_aut(edges_of(nx.hypercube_graph(4)), 16, 384)


def test_hypercube_q4_isomorphism():
    e = edges_of(nx.hypercube_graph(4))
    e2, _ = relabel(e, 16, random.Random(4))
    iso, _ = run_pair(e, e2, 16)
    assert iso is not None
    # a 4-regular bipartite graph on 16 vertices that is not Q4
    h = nx.circulant_graph(16, [1, 7])
    run_pair(e, edges_of(h), 16)


def test_petersen():
    e = edges_of(nx.petersen_graph())
    e2, _ = relabel(e, 10, random.Random(10))
    iso, _ = run_pair(e, e2, 10)
    assert iso is not None
    check_aut(e, 10, 120)
    # another 3-regular graph on 10 vertices (the 5-prism)
    run_pair(e, edges_of(nx.circular_ladder_graph(5)), 10)


@pytest.mark.parametrize("parts,order", [((2, 2, 2, 2), 384), ((2, 3, 3), 144), ((1, 2, 3), 12), ((3, 3, 3), 1296), ((4, 4), 1152), ((1, 1, 2, 2), 2 * 2 * 2 * 2)])
def test_complete_multipartite(parts, order):
    g = nx.complete_multipartite_graph(*parts)
    n = g.number_of_nodes()
    e = edges_of(g)
    e2, _ = relabel(e, n, random.Random(n))
    iso, _ = run_pair(e, e2, n)
    assert iso is not None
    check_aut(e, n, order)
    if n <= 8:
        assert brute_aut_order(e, n) == order


# -------------------------------------------------------- asymmetric trees

def _asymmetric_trees(n):
    out = []
    for t in nx.nonisomorphic_trees(n):
        if nx_aut_order(t) == 1:
            out.append(t)
    return out


@pytest.mark.parametrize("n", [7, 8, 9, 10])
def test_asymmetric_trees(n):
    trees = _asymmetric_trees(n)
    assert trees  # the smallest asymmetric tree has 7 vertices
    rng = random.Random(500 + n)
    for t in trees[:6]:
        e = edges_of(t)
        e2, perm = relabel(e, n, rng)
        iso, _ = run_pair(e, e2, n)
        assert iso is not None
        # a tree with trivial automorphism group has exactly one isomorphism onto a relabeling
        assert all(iso[v] == perm[v] for v in range(n))
        check_aut(e, n, 1)
    if len(trees) >= 2:
        iso, _ = run_pair(edges_of(trees[0]), edges_of(trees[1]), n)
        assert iso is None
