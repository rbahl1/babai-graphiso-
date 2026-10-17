"""Exhaustive small cases: every graph with at most 7 vertices (networkx's
Atlas of Graphs: 1253 pairwise non-isomorphic graphs), under seeded random
relabelings, non-isomorphic pairs with equal degree sequences, and
automorphism group orders against brute force."""

import itertools
import random

import networkx as nx
import pytest
from networkx.generators.atlas import graph_atlas_g

from .helpers import brute_aut_order, check_aut, edges_of, relabel, run_pair

ATLAS = graph_atlas_g()


def by_nodes(n):
    return [g for g in ATLAS if g.number_of_nodes() == n]


def test_atlas_is_complete():
    assert len(ATLAS) == 1253
    assert [len(by_nodes(n)) for n in range(0, 8)] == [1, 1, 2, 4, 11, 34, 156, 1044]


@pytest.mark.parametrize("n", range(1, 8))
def test_every_graph_isomorphic_to_random_relabeling(n):
    rng = random.Random(1000 + n)
    for g in by_nodes(n):
        edges = edges_of(g)
        edges2, perm = relabel(edges, n, rng)
        iso, _ = run_pair(edges, edges2, n)
        assert iso is not None


def _equal_degree_pairs(rng, n, limit):
    groups = {}
    for g in by_nodes(n):
        key = tuple(sorted(d for _, d in g.degree()))
        groups.setdefault(key, []).append(g)
    pairs = []
    for gs in groups.values():
        pairs.extend(itertools.combinations(gs, 2))
    if limit is not None and len(pairs) > limit:
        pairs = rng.sample(pairs, limit)
    return pairs


@pytest.mark.parametrize("n,limit", [(5, None), (6, None), (7, 250)])
def test_nonisomorphic_pairs_with_equal_degree_sequences(n, limit):
    rng = random.Random(77 + n)
    pairs = _equal_degree_pairs(rng, n, limit)
    assert pairs
    for g1, g2 in pairs:
        e1, e2 = edges_of(g1), edges_of(g2)
        if len(e1) != len(e2):
            continue
        e2, _ = relabel(e2, n, rng)
        iso, _ = run_pair(e1, e2, n)
        assert iso is None  # atlas graphs are pairwise non-isomorphic


@pytest.mark.parametrize("n", range(1, 7))
def test_automorphism_orders_all_graphs(n):
    for g in by_nodes(n):
        edges = edges_of(g)
        check_aut(edges, n, brute_aut_order(edges, n))


def test_automorphism_orders_sample_n7():
    rng = random.Random(11)
    for g in rng.sample(by_nodes(7), 120):
        edges = edges_of(g)
        check_aut(edges, 7, brute_aut_order(edges, 7))


@pytest.mark.parametrize("name,g", [
    ("Q3", nx.hypercube_graph(3)),
    ("K4,4", nx.complete_bipartite_graph(4, 4)),
    ("C8", nx.cycle_graph(8)),
    ("K2,2,2,2", nx.complete_multipartite_graph(2, 2, 2, 2)),
    ("K2,3,3", nx.complete_multipartite_graph(2, 3, 3)),
    ("2K4", nx.disjoint_union(nx.complete_graph(4), nx.complete_graph(4))),
    ("Wagner", nx.circulant_graph(8, [1, 4])),
    ("random1", nx.gnm_random_graph(8, 12, seed=3)),
    ("random2", nx.gnm_random_graph(8, 15, seed=4)),
    ("tree", nx.random_labeled_tree(8, seed=5) if hasattr(nx, "random_labeled_tree") else nx.random_tree(8, seed=5)),
])
def test_automorphism_orders_n8_vs_brute_force(name, g):
    edges = edges_of(g)
    check_aut(edges, 8, brute_aut_order(edges, 8))
