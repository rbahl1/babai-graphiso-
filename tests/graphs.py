"""Graph families and checking helpers shared by the test modules.

NetworkX is used only as an independent reference (VF2 isomorphism test,
automorphism counting via the matcher) and as a convenient generator.
"""

from __future__ import annotations

import itertools
import random
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

from babai_gi.graph import graph_automorphisms, graph_isomorphism
from babai_gi.main import Params, Solver

Edges = List[Tuple[int, int]]


# ------------------------------------------------------------------ utilities
def edges_of(g: nx.Graph) -> Edges:
    return [(int(u), int(v)) for u, v in g.edges()]


def relabel(g: nx.Graph, seed: int) -> Tuple[nx.Graph, List[int]]:
    """A random relabeling of g (nodes must be 0..n-1); returns (graph, permutation)."""
    n = g.number_of_nodes()
    rng = random.Random(seed)
    perm = list(range(n))
    rng.shuffle(perm)
    return nx.relabel_nodes(g, {i: perm[i] for i in range(n)}), perm


def nx_aut_order(g: nx.Graph, cap: Optional[int] = None) -> int:
    """|Aut(g)| by exhaustive matching (reference; only for small groups)."""
    count = 0
    for _ in GraphMatcher(g, g).isomorphisms_iter():
        count += 1
        if cap is not None and count > cap:
            break
    return count


def is_iso_map(g1: nx.Graph, g2: nx.Graph, f: Dict[int, int]) -> bool:
    if sorted(f) != list(range(g1.number_of_nodes())) or sorted(f.values()) != list(range(g2.number_of_nodes())):
        return False
    E2 = {frozenset(e) for e in g2.edges()}
    if len(E2) != g1.number_of_edges():
        return False
    return all(frozenset((f[u], f[v])) in E2 for u, v in g1.edges())


def check_pair(g1: nx.Graph, g2: nx.Graph, expect: Optional[bool] = None, params: Optional[Params] = None,
               solver: Optional[Solver] = None) -> Optional[Dict[int, int]]:
    """Run babai_gi on (g1, g2); compare with NetworkX's answer (or ``expect``);
    verify any returned map is an isomorphism.  Returns the map."""
    n1, n2 = g1.number_of_nodes(), g2.number_of_nodes()
    if expect is None:
        expect = nx.is_isomorphic(g1, g2)
    if solver is None and params is None:
        params = Params.small_scale()   # the library default Params.paper() enumerates Sym(V) below 160 vertices
    f = graph_isomorphism(edges_of(g1), n1, edges_of(g2), n2, params=params, solver=solver)
    assert (f is not None) == expect, f"babai_gi says {'iso' if f else 'non-iso'}, expected {'iso' if expect else 'non-iso'}"
    if f is not None:
        assert is_iso_map(g1, g2, f), "returned map is not an isomorphism"
    return f


def check_aut(g: nx.Graph, expected_order: Optional[int] = None, params: Optional[Params] = None,
              solver: Optional[Solver] = None) -> int:
    """|Aut(g)| via babai_gi; generators are verified to be automorphisms."""
    n = g.number_of_nodes()
    if solver is None and params is None:
        params = Params.small_scale()
    gens, order = graph_automorphisms(edges_of(g), n, params=params, solver=solver)
    for p in gens:
        assert is_iso_map(g, g, {v: p[v] for v in range(n)}), "generator is not an automorphism"
    if expected_order is None:
        expected_order = nx_aut_order(g)
    assert order == expected_order, f"|Aut| = {order}, expected {expected_order}"
    return order


# -------------------------------------------------------------- generators
def paley(q: int) -> nx.Graph:
    """Paley graph on F_q, q = 1 (mod 4), for q prime or q = 9 (F_9 = F_3[i]/(i^2 + 1))."""
    assert q % 4 == 1
    if q == 9:
        elems = [(a, b) for a in range(3) for b in range(3)]

        def mulf(x, y):
            return ((x[0] * y[0] - x[1] * y[1]) % 3, (x[0] * y[1] + x[1] * y[0]) % 3)

        def sub(x, y):
            return ((x[0] - y[0]) % 3, (x[1] - y[1]) % 3)

        squares = {mulf(x, x) for x in elems if x != (0, 0)}
    else:
        elems = list(range(q))

        def sub(x, y):
            return (x - y) % q

        squares = {(a * a) % q for a in range(1, q)}
    g = nx.Graph()
    g.add_nodes_from(range(q))
    for i, a in enumerate(elems):
        for j in range(i + 1, q):
            if sub(elems[j], a) in squares:
                g.add_edge(i, j)
    return g


def shrikhande() -> nx.Graph:
    """Cayley graph of Z4 x Z4 with connection set {+-(0,1), +-(1,0), +-(1,1)}."""
    g = nx.Graph()
    conn = [(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)]
    for a in range(4):
        for b in range(4):
            for da, db in conn:
                g.add_edge((a, b), ((a + da) % 4, (b + db) % 4))
    return nx.convert_node_labels_to_integers(g, ordering="sorted")


def rook(k: int) -> nx.Graph:
    """k x k rook's graph = K_k [] K_k = line graph of K_{k,k}."""
    return nx.convert_node_labels_to_integers(nx.cartesian_product(nx.complete_graph(k), nx.complete_graph(k)),
                                              ordering="sorted")


def johnson_graph(m: int, t: int) -> nx.Graph:
    """J(m, t): t-subsets adjacent iff they share t-1 elements."""
    subsets = list(itertools.combinations(range(m), t))
    idx = {s: i for i, s in enumerate(subsets)}
    g = nx.Graph()
    g.add_nodes_from(range(len(subsets)))
    for s in subsets:
        for u in s:
            for v in range(m):
                if v in s:
                    continue
                s2 = tuple(sorted((set(s) - {u}) | {v}))
                if idx[s] < idx[s2]:
                    g.add_edge(idx[s], idx[s2])
    return g


def hypercube(d: int) -> nx.Graph:
    return nx.convert_node_labels_to_integers(nx.hypercube_graph(d), ordering="sorted")


def complete_multipartite(*sizes: int) -> nx.Graph:
    return nx.convert_node_labels_to_integers(nx.complete_multipartite_graph(*sizes), ordering="sorted")


def disjoint_union(*graphs: nx.Graph) -> nx.Graph:
    g = nx.Graph()
    off = 0
    for h in graphs:
        g.add_nodes_from(range(off, off + h.number_of_nodes()))
        g.add_edges_from((u + off, v + off) for u, v in h.edges())
        off += h.number_of_nodes()
    return g


def random_graph(n: int, p: float, seed: int) -> nx.Graph:
    return nx.gnp_random_graph(n, p, seed=seed)


def random_regular(d: int, n: int, seed: int) -> nx.Graph:
    return nx.random_regular_graph(d, n, seed=seed)


def asymmetric_tree(n: int, seed: int) -> nx.Graph:
    """A random tree on n >= 7 vertices with trivial automorphism group."""
    rng = random.Random(seed)
    for _ in range(10000):
        t = nx.random_labeled_tree(n, seed=rng.randrange(1 << 30))
        if nx_aut_order(t, cap=1) == 1:
            return t
    raise RuntimeError("no asymmetric tree found")


def cfi(base: nx.Graph, twist: bool) -> nx.Graph:
    """The Cai-Furer-Immerman graph over ``base``.

    Every edge e of the base graph becomes two vertices (e, 0), (e, 1); every
    base vertex v of degree d becomes the 2^{d-1} vertices ("m", v, bits) with
    even bit vectors, joined to (e, bit_e) for the edges e at v.  ``twist``
    flips the parity at one endpoint of one edge; the two graphs are
    non-isomorphic but k-WL equivalent for k below the treewidth of the base.
    """
    g = nx.Graph()
    edges = [tuple(sorted(e)) for e in base.edges()]
    for e in edges:
        g.add_node((e, 0))
        g.add_node((e, 1))
    twisted = False
    for v in base.nodes():
        Ev = [e for e in edges if v in e]
        for bits in itertools.product([0, 1], repeat=len(Ev)):
            if sum(bits) % 2 == 0:
                mid = ("m", v, bits)
                g.add_node(mid)
                for e, b in zip(Ev, bits):
                    bb = b
                    if twist and not twisted and e == edges[0]:
                        bb = 1 - b
                    g.add_edge(mid, (e, bb))
        if twist and not twisted and v in edges[0]:
            twisted = True
    return nx.convert_node_labels_to_integers(g)
