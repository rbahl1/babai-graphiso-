"""Graph Isomorphism as String Isomorphism (Babai Sec. 1.1.1 / HBD Sec. 1).

A graph on V = {0..n-1} is the binary string x on Omega = binom(V, 2) with
x({u,v}) = 1 iff uv is an edge; G = S^{(2)}(V) is the induced action of Sym(V)
on pairs.  Iso(X1, X2) corresponds bijectively to ISO_G(x1, x2) (for n >= 3 the
action on pairs is faithful).  Vertex colors are supported by appending the
color pattern to the letters (Cor. 1.1.4).
"""

from __future__ import annotations

from itertools import combinations
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

from .action import Coset
from .canon import canon, normalize_letters
from .group import PermGroup
from .johnson import induced_on_subsets, subsets_of
from .main import Params, Solver
from .perm import Perm, from_cycles


def _normalize_edges(edges: Iterable[Sequence[int]], n: int) -> Set[Tuple[int, int]]:
    out = set()
    for e in edges:
        u, v = int(e[0]), int(e[1])
        if u == v or not (0 <= u < n and 0 <= v < n):
            raise ValueError(f"bad edge {e!r}")
        out.add((min(u, v), max(u, v)))
    return out


class GraphInstance:
    """The String Isomorphism encoding of a pair of graphs on n vertices."""

    def __init__(self, n: int, colors1: Optional[Sequence] = None, colors2: Optional[Sequence] = None):
        self.n = n
        self.pairs = subsets_of(n, 2)
        self.index = {p: i for i, p in enumerate(self.pairs)}
        gens = []
        if n >= 2:
            gens.append(induced_on_subsets(from_cycles(n, [[0, 1]]), self.pairs, self.index))
        if n >= 3:
            gens.append(induced_on_subsets(from_cycles(n, [list(range(n))]), self.pairs, self.index))
        from math import factorial
        self.G = PermGroup(len(self.pairs), gens, known_order=factorial(n) if n >= 3 else None)
        if n >= 5:
            # The reduction knows that G = S^{(2)}(V) (Babai Sec. 1.1.1); record the
            # Johnson structure so that the solver need not re-identify it
            # (``recognize_johnson`` would find the same structure; see tests).
            from .johnson import JohnsonStructure
            self.G.johnson_hint = JohnsonStructure(  # type: ignore[attr-defined]
                n, 2, [from_cycles(n, [[0, 1]]), from_cycles(n, [list(range(n))])],
                [frozenset(p) for p in self.pairs])
        self.colors1 = list(colors1) if colors1 is not None else None
        self.colors2 = list(colors2) if colors2 is not None else None

    _shared: Dict[int, "GraphInstance"] = {}

    @classmethod
    def shared(cls, n: int) -> "GraphInstance":
        """The instance for n vertices, shared between calls: the group S^{(2)}(V)
        and its stabilizer chains (and the solver's caches on it) are reused."""
        inst = cls._shared.get(n)
        if inst is None:
            inst = cls(n)
            cls._shared[n] = inst
        return inst

    def string(self, edges: Iterable[Sequence[int]], colors: Optional[Sequence] = None) -> tuple:
        E = _normalize_edges(edges, self.n)
        out = []
        for (u, v) in self.pairs:
            bit = 1 if (u, v) in E else 0
            if colors is not None:
                out.append((bit, tuple(sorted((colors[u], colors[v]), key=canon))))
            else:
                out.append(bit)
        return tuple(out)

    def vertex_perm(self, p: Perm) -> List[int]:
        """Recover the vertex permutation inducing the pair permutation p (n >= 3)."""
        n = self.n
        img = [-1] * n
        for v in range(n):
            others = [u for u in range(n) if u != v][:2]
            a = self.pairs[p[self.index[tuple(sorted((v, others[0])))]]]
            b = self.pairs[p[self.index[tuple(sorted((v, others[1])))]]]
            common = set(a) & set(b)
            if len(common) != 1:
                raise ValueError("permutation of pairs not induced by a vertex permutation")
            img[v] = common.pop()
        return img


def graph_isomorphism(edges1: Iterable[Sequence[int]], n1: int, edges2: Iterable[Sequence[int]], n2: int,
                      params: Optional[Params] = None, solver: Optional[Solver] = None,
                      colors1: Optional[Sequence] = None, colors2: Optional[Sequence] = None) -> Optional[Dict[int, int]]:
    """An isomorphism (dict vertex -> vertex) from graph 1 to graph 2, or None."""
    if n1 != n2:
        return None
    n = n1
    E1 = _normalize_edges(edges1, n)
    E2 = _normalize_edges(edges2, n)
    if len(E1) != len(E2):
        return None
    if n <= 2:
        if colors1 is not None or colors2 is not None:
            c1 = sorted(colors1) if colors1 else []
            c2 = sorted(colors2) if colors2 else []
            if c1 != c2:
                return None
            if n == 2 and colors1[0] != colors2[0]:
                return {0: 1, 1: 0}
        return {v: v for v in range(n)}
    inst = GraphInstance.shared(n)
    x, y = normalize_letters(inst.string(E1, colors1), inst.string(E2, colors2))
    if solver is None:
        solver = Solver(params)
    C = solver.iso(inst.G, x, y)
    if C is None:
        return None
    img = inst.vertex_perm(C.rep)
    return {v: img[v] for v in range(n)}


def graph_automorphisms(edges: Iterable[Sequence[int]], n: int, params: Optional[Params] = None,
                        solver: Optional[Solver] = None, colors: Optional[Sequence] = None) -> Tuple[List[List[int]], int]:
    """Generators (as vertex permutations) and the order of Aut(X)."""
    if n <= 2:
        from math import factorial
        if colors is not None and n == 2 and colors[0] != colors[1]:
            return [], 1
        return ([[1, 0]] if n == 2 else []), factorial(n)
    inst = GraphInstance.shared(n)
    x = normalize_letters(inst.string(_normalize_edges(edges, n), colors), ())[0]
    if solver is None:
        solver = Solver(params)
    C = solver.iso(inst.G, x, x)
    assert C is not None
    gens = [inst.vertex_perm(g) for g in C.group.gens]
    return gens, C.group.order()


def graph_automorphism_group_order(edges: Iterable[Sequence[int]], n: int, params: Optional[Params] = None,
                                   solver: Optional[Solver] = None) -> int:
    return graph_automorphisms(edges, n, params, solver)[1]


def parse_edge_list(text: str) -> Tuple[int, List[Tuple[int, int]]]:
    """Simple edge-list format: first non-comment line "n m" (m optional), then "u v" lines."""
    lines = [ln.strip() for ln in text.splitlines()]
    lines = [ln for ln in lines if ln and not ln.startswith("#")]
    if not lines:
        raise ValueError("empty graph file")
    head = lines[0].split()
    n = int(head[0])
    edges = []
    for ln in lines[1:]:
        parts = ln.split()
        if len(parts) < 2:
            continue
        edges.append((int(parts[0]), int(parts[1])))
    return n, edges
