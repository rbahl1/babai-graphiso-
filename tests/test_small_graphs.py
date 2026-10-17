"""Exhaustive checks on all graphs with at most 7 vertices (NetworkX atlas),
plus random graphs on 8..12 vertices with and without planted isomorphisms.

Every answer is compared with NetworkX (VF2) and every returned map is
verified to be an isomorphism; automorphism group orders are compared with an
exhaustive count."""

import random
from collections import defaultdict

import networkx as nx
import pytest
from networkx.generators.atlas import graph_atlas_g

from babai_gi.graph import graph_isomorphism
from babai_gi.main import Params

from .graphs import check_aut, check_pair, edges_of, random_graph, relabel

ATLAS = graph_atlas_g()
BY_N = defaultdict(list)
for _g in ATLAS:
    BY_N[_g.number_of_nodes()].append(_g)


@pytest.mark.parametrize("n", range(0, 8))
def test_atlas_relabeled_is_isomorphic(n):
    for i, g in enumerate(BY_N[n]):
        g2, perm = relabel(g, 1000 * n + i)
        f = check_pair(g, g2, True)
        assert f is not None


@pytest.mark.parametrize("n", range(1, 8))
def test_atlas_automorphism_orders(n):
    for g in BY_N[n]:
        check_aut(g)


@pytest.mark.parametrize("n", range(2, 8))
def test_atlas_nonisomorphic_same_degree_sequence(n):
    """All pairs of distinct atlas graphs on n vertices with the same degree
    sequence are (by construction of the atlas) non-isomorphic."""
    groups = defaultdict(list)
    for g in BY_N[n]:
        groups[tuple(sorted(d for _, d in g.degree()))].append(g)
    pairs = 0
    rng = random.Random(n)
    for key, gs in groups.items():
        all_pairs = [(i, j) for i in range(len(gs)) for j in range(i + 1, len(gs))]
        if len(all_pairs) > 25:
            all_pairs = rng.sample(all_pairs, 25)
        for i, j in all_pairs:
            # the atlas lists pairwise non-isomorphic graphs
            g2, _ = relabel(gs[j], rng.randrange(1 << 30))
            check_pair(gs[i], g2, False)
            pairs += 1
    assert pairs > 0 or n <= 4  # no two graphs on <= 4 vertices share a degree sequence


def test_trivial_sizes():
    assert graph_isomorphism([], 0, [], 0) == {}
    assert graph_isomorphism([], 1, [], 1) == {0: 0}
    assert graph_isomorphism([(0, 1)], 2, [(0, 1)], 2) == {0: 0, 1: 1}
    assert graph_isomorphism([(0, 1)], 2, [], 2) is None
    assert graph_isomorphism([(0, 1)], 3, [(0, 1), (1, 2)], 3) is None
    assert graph_isomorphism([], 3, [], 4) is None


@pytest.mark.parametrize("n,p,seed", [(8, 0.3, 1), (8, 0.5, 2), (9, 0.4, 3), (10, 0.5, 4), (11, 0.3, 5), (12, 0.5, 6),
                                      (12, 0.2, 7), (14, 0.5, 8)])
def test_random_graph_planted_isomorphism(n, p, seed):
    g = random_graph(n, p, seed)
    g2, perm = relabel(g, seed + 77)
    f = check_pair(g, g2, True)
    assert f is not None


@pytest.mark.parametrize("n,p,seed", [(8, 0.5, 11), (9, 0.5, 12), (10, 0.4, 13), (11, 0.5, 14), (12, 0.5, 15)])
def test_random_graph_pairs_reference(n, p, seed):
    """Independent random graphs (almost surely non-isomorphic) and graphs
    obtained by a single edge flip (same edge count); compared with NetworkX."""
    g = random_graph(n, p, seed)
    h = random_graph(n, p, seed + 1000)
    if g.number_of_edges() == h.number_of_edges():
        check_pair(g, h)
    # one edge moved: same number of edges, generally non-isomorphic
    rng = random.Random(seed)
    g3 = g.copy()
    e = rng.choice(list(g3.edges()))
    non = [(u, v) for u in range(n) for v in range(u + 1, n) if not g3.has_edge(u, v)]
    g3.remove_edge(*e)
    g3.add_edge(*rng.choice(non))
    check_pair(g, g3)


def test_vertex_colors():
    # path 0-1-2 with colors distinguishing the ends
    e = [(0, 1), (1, 2)]
    assert graph_isomorphism(e, 3, e, 3, colors1=[0, 1, 2], colors2=[0, 1, 2]) == {0: 0, 1: 1, 2: 2}
    assert graph_isomorphism(e, 3, e, 3, colors1=[0, 1, 2], colors2=[2, 1, 0]) == {0: 2, 1: 1, 2: 0}
    assert graph_isomorphism(e, 3, e, 3, colors1=[0, 1, 2], colors2=[1, 0, 2]) is None
    # C6 with colors: alternating vs two-and-two
    c6 = [(i, (i + 1) % 6) for i in range(6)]
    assert graph_isomorphism(c6, 6, c6, 6, colors1=[0, 1] * 3, colors2=[1, 0] * 3) is not None
    assert graph_isomorphism(c6, 6, c6, 6, colors1=[0, 1] * 3, colors2=[0, 0, 1, 1, 0, 1]) is None


def test_params_thresholds_do_not_change_answers():
    """Forcing the Johnson-case machinery (tiny brute-force threshold, no quotient
    enumeration) must agree with pure brute force and with the small-scale
    thresholds on small graphs (the paper preset is tested in test_presets.py)."""
    rng = random.Random(3)
    for n in (6, 7, 8):
        for _ in range(3):
            g = random_graph(n, 0.5, rng.randrange(1 << 30))
            g2, _ = relabel(g, rng.randrange(1 << 30))
            for P in (Params.small_scale(brute_force_order=1, quotient_enum_limit=1, min_gamma=6),
                      Params.small_scale(brute_force_order=10 ** 9), Params.small_scale()):
                check_pair(g, g2, True, params=P)
                check_aut(g, params=P)
