"""Shared helpers for the test battery.

networkx is used here ONLY as a graph container / generator and as the
reference isomorphism checker (``nx.is_isomorphic``); the algorithm under test
never calls it.
"""

from __future__ import annotations

import itertools
import random
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import networkx as nx

from babai_gi.graph import graph_automorphisms, graph_isomorphism
from babai_gi.main import Params, Solver

Edge = Tuple[int, int]


# ------------------------------------------------------------------ graphs

def edges_of(g: nx.Graph) -> List[Edge]:
    g = nx.convert_node_labels_to_integers(g)
    return [(int(u), int(v)) for u, v in g.edges()]


def relabel(edges: Sequence[Edge], n: int, rng: random.Random) -> Tuple[List[Edge], List[int]]:
    """Apply a random vertex permutation; returns (new edges, permutation)."""
    perm = list(range(n))
    rng.shuffle(perm)
    return [(perm[u], perm[v]) for u, v in edges], perm


def nx_graph(edges: Iterable[Edge], n: int) -> nx.Graph:
    g = nx.Graph()
    g.add_nodes_from(range(n))
    g.add_edges_from(edges)
    return g


def shrikhande() -> nx.Graph:
    """The Shrikhande graph: Cayley graph of Z4 x Z4 with connection set
    {(0,1),(0,3),(1,0),(3,0),(1,1),(3,3)}; srg(16,6,2,2) like the 4x4 rook's graph."""
    g = nx.Graph()
    conn = [(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)]
    for a in range(4):
        for b in range(4):
            for (da, db) in conn:
                g.add_edge((a, b), ((a + da) % 4, (b + db) % 4))
    return nx.convert_node_labels_to_integers(g)


def rook(k: int) -> nx.Graph:
    """The k x k rook's graph K_k x K_k (the line graph of K_{k,k})."""
    return nx.convert_node_labels_to_integers(nx.cartesian_product(nx.complete_graph(k), nx.complete_graph(k)))


def paley(q: int) -> nx.Graph:
    return nx.convert_node_labels_to_integers(nx.paley_graph(q).to_undirected())


def johnson_graph(m: int, t: int = 2) -> nx.Graph:
    """J(m, t): t-subsets of [m], adjacent iff they share t-1 elements."""
    subs = list(itertools.combinations(range(m), t))
    g = nx.Graph()
    g.add_nodes_from(range(len(subs)))
    for i, a in enumerate(subs):
        for j in range(i + 1, len(subs)):
            if len(set(a) & set(subs[j])) == t - 1:
                g.add_edge(i, j)
    return g


def cfi(base: nx.Graph, twist: bool) -> nx.Graph:
    """Cai-Furer-Immerman graph over ``base``.

    Every base edge e becomes two vertices (e,0), (e,1); every base vertex v of
    degree d becomes the 2^(d-1) "middle" vertices (v, bits) with an even number
    of 1-bits, (v, bits) being adjacent to (e_i, bits[i]) for the edges e_i at v.
    ``twist`` flips the parity at one endpoint of the first edge; the twisted and
    untwisted graphs are not isomorphic but are not distinguished by k-WL for
    small k (k depends on the base graph).
    """
    g = nx.Graph()
    edges = [tuple(sorted(e)) for e in base.edges()]
    for e in edges:
        g.add_node((e, 0))
        g.add_node((e, 1))
    first = True
    for v in base.nodes():
        Ev = [e for e in edges if v in e]
        d = len(Ev)
        for bits in itertools.product([0, 1], repeat=d):
            if sum(bits) % 2 == 0:
                mid = ("m", v, bits)
                g.add_node(mid)
                for e, b in zip(Ev, bits):
                    bb = b
                    if twist and first and e == edges[0]:
                        bb = 1 - b
                    g.add_edge(mid, (e, bb))
        if v in edges[0]:
            first = False
    return nx.convert_node_labels_to_integers(g)


# ------------------------------------------------------------------ checks

def check_isomorphism(edges1: Sequence[Edge], edges2: Sequence[Edge], n: int, iso: Dict[int, int]) -> None:
    """The mapping must be a bijection of the vertices carrying the edge set of
    graph 1 exactly onto the edge set of graph 2."""
    assert sorted(iso.keys()) == list(range(n))
    assert sorted(iso.values()) == list(range(n))
    E1 = {frozenset(e) for e in edges1}
    E2 = {frozenset(e) for e in edges2}
    mapped = {frozenset((iso[u], iso[v])) for u, v in E1}
    assert mapped == E2, "returned mapping does not carry the edge set onto the edge set"


def run_pair(edges1: Sequence[Edge], edges2: Sequence[Edge], n: int, params: Optional[Params] = None,
             solver: Optional[Solver] = None) -> Tuple[Optional[Dict[int, int]], Solver]:
    """Run the algorithm, compare the verdict with networkx and verify the mapping.

    The battery uses ``Params.small_scale()`` unless told otherwise: with the
    papers' thresholds (the library default) every graph below 160 vertices is
    solved by enumerating Sym(V), which is infeasible beyond ~9 vertices
    (tests/test_presets.py exercises the default on tiny inputs)."""
    solver = solver or Solver(params if params is not None else Params.small_scale())
    iso = graph_isomorphism(edges1, n, edges2, n, solver=solver)
    ref = nx.is_isomorphic(nx_graph(edges1, n), nx_graph(edges2, n))
    assert (iso is not None) == ref, f"verdict {iso is not None} disagrees with networkx {ref}"
    if iso is not None:
        check_isomorphism(edges1, edges2, n, iso)
    return iso, solver


def brute_aut_order(edges: Sequence[Edge], n: int) -> int:
    E = {frozenset(e) for e in edges}
    cnt = 0
    for p in itertools.permutations(range(n)):
        if all(frozenset((p[u], p[v])) in E for u, v in edges):
            cnt += 1
    return cnt


def nx_aut_order(g: nx.Graph) -> int:
    """|Aut(g)| by enumerating networkx's VF2 isomorphisms (reference only)."""
    gm = nx.algorithms.isomorphism.GraphMatcher(g, g)
    return sum(1 for _ in gm.isomorphisms_iter())


def check_aut(edges: Sequence[Edge], n: int, expected: int, params: Optional[Params] = None) -> Solver:
    solver = Solver(params if params is not None else Params.small_scale())
    gens, order = graph_automorphisms(edges, n, solver=solver)
    assert order == expected, f"|Aut| = {order}, expected {expected}"
    E = {frozenset(e) for e in edges}
    for g in gens:
        assert sorted(g) == list(range(n))
        assert {frozenset((g[u], g[v])) for u, v in edges} == E, "generator is not an automorphism"
    return solver
