"""Classical (binary) coherent configurations: constituents, connectivity,
primitivity, twins (Babai Sec. 2.5; HBD Sec. 2.4, Exercises 2.4, 2.6).

A ``ClassicalCC`` is a coloring c: V x V -> colors (ints).  When built from
WL-refined colorings the colors are canonically ordered ints and ``key`` is the
identity.  When built from the orbitals of a canonical group (Babai Sec. 10.2
Case 2b, Sec. 13.1), the colors carry no canonical order; ``canonical_keys``
then computes invariant keys (a refinement of the color set by the structure
constants) so that colors with distinct keys are canonically distinguishable
and ties are resolved by explicit choices (multiplicative cost, Babai Sec. 4).
"""

from __future__ import annotations

from collections import defaultdict
from typing import Callable, Dict, FrozenSet, Hashable, List, Optional, Sequence, Set, Tuple

from .canon import canon


class ClassicalCC:
    def __init__(self, vertices: Sequence[int], color: Callable[[int, int], Hashable],
                 keys: Optional[Dict[Hashable, Hashable]] = None):
        self.vertices = list(vertices)
        self.N = len(self.vertices)
        V = self.vertices
        self.c = [[color(u, v) for v in V] for u in V]
        self.vcol = [self.c[i][i] for i in range(self.N)]
        self.pos = {v: i for i, v in enumerate(V)}
        cols = set()
        for row in self.c:
            cols.update(row)
        self.colors: List = sorted(cols, key=_hk)
        self._keys = keys
        self._paired: Optional[Dict] = None

    # ------------------------------------------------------------ basics
    def key(self, color) -> Hashable:
        if self._keys is None:
            return color
        return self._keys[color]

    def set_keys(self, keys: Dict) -> None:
        self._keys = keys

    def vertex_classes(self) -> Dict[Hashable, List[int]]:
        d: Dict[Hashable, List[int]] = defaultdict(list)
        for i, v in enumerate(self.vertices):
            d[self.vcol[i]].append(v)
        return dict(d)

    def is_homogeneous(self) -> bool:
        return len(set(self.vcol)) == 1

    def diagonal_colors(self) -> Set:
        return set(self.vcol)

    def off_diagonal_colors(self) -> List:
        d = self.diagonal_colors()
        return [col for col in self.colors if col not in d]

    def paired(self, color):
        """The color of reversed pairs (i^- in Babai's notation)."""
        if self._paired is None:
            p = {}
            for i in range(self.N):
                for j in range(self.N):
                    col = self.c[i][j]
                    if col not in p:
                        p[col] = self.c[j][i]
            self._paired = p
        return self._paired[color]

    def out_neighbors(self, i: int, color) -> List[int]:
        row = self.c[i]
        return [j for j in range(self.N) if row[j] == color]

    def in_neighbors(self, j: int, color) -> List[int]:
        return [i for i in range(self.N) if self.c[i][j] == color]

    def out_degree(self, i: int, color) -> int:
        return sum(1 for x in self.c[i] if x == color)

    def constituent_vertex_classes(self, color) -> Tuple[Set, Set]:
        """Vertex colors of out- and in-vertices of a constituent (Obs. 2.5.2)."""
        outs, ins = set(), set()
        for i in range(self.N):
            for j in range(self.N):
                if self.c[i][j] == color:
                    outs.add(self.vcol[i])
                    ins.add(self.vcol[j])
        return outs, ins

    def components(self, color) -> List[List[int]]:
        """Weakly connected components of the constituent digraph (indices)."""
        parent = list(range(self.N))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for i in range(self.N):
            row = self.c[i]
            for j in range(self.N):
                if row[j] == color and i != j:
                    ri, rj = find(i), find(j)
                    if ri != rj:
                        parent[ri] = rj
        groups: Dict[int, List[int]] = defaultdict(list)
        for i in range(self.N):
            groups[find(i)].append(i)
        return list(groups.values())

    def effective_vertices(self, color) -> List[int]:
        out = set()
        for i in range(self.N):
            row = self.c[i]
            for j in range(self.N):
                if row[j] == color:
                    out.add(i)
                    out.add(j)
        return sorted(out)

    def is_clique(self) -> bool:
        """Rank 2 on a homogeneous vertex set (Babai Def. 2.5.4)."""
        return self.is_homogeneous() and len(self.off_diagonal_colors()) <= 1

    def disconnected_off_diagonal_colors(self) -> List:
        """Off-diagonal colors whose constituent is disconnected on its effective vertex set."""
        out = []
        for col in self.off_diagonal_colors():
            effset = set(self.effective_vertices(col))
            ncomp = sum(1 for cmp in self.components(col) if effset.intersection(cmp))
            if ncomp > 1:
                out.append(col)
        return out

    def is_primitive(self) -> bool:
        """Homogeneous and every non-diagonal constituent connected (Def. 2.5.21)."""
        if not self.is_homogeneous():
            return False
        for col in self.off_diagonal_colors():
            if len(self.components(col)) > 1:
                return False
        return True

    def is_uniprimitive(self) -> bool:
        return self.is_primitive() and len(self.off_diagonal_colors()) >= 2

    def induced(self, subset: Sequence[int]) -> "ClassicalCC":
        """Induced subconfiguration on a subset of vertices (Def. 2.3.1)."""
        sub = list(subset)
        c = self.c
        pos = self.pos
        return ClassicalCC(sub, lambda u, v: c[pos[u]][pos[v]], keys=self._keys)

    # -------------------------------------------------------------- twins
    def strong_twin_classes(self) -> List[List[int]]:
        """Classes of the "strong twin or equal" relation (Def. 2.4.2 / 2.4.8).

        u, v are strong twins iff the transposition (u v) is an automorphism of
        the configuration.  Returns classes as lists of vertices (size >= 1).
        """
        N = self.N
        c = self.c
        parent = list(range(N))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for i in range(N):
            if find(i) != i:
                continue
            for j in range(i + 1, N):
                if find(j) == find(i):
                    continue
                if c[i][i] != c[j][j] or c[i][j] != c[j][i]:
                    continue
                ok = True
                ri, rj = c[i], c[j]
                for w in range(N):
                    if w == i or w == j:
                        continue
                    if ri[w] != rj[w] or c[w][i] != c[w][j]:
                        ok = False
                        break
                if ok:
                    parent[find(j)] = find(i)
        groups: Dict[int, List[int]] = defaultdict(list)
        for i in range(N):
            groups[find(i)].append(self.vertices[i])
        return list(groups.values())

    def largest_twin_class_size(self) -> int:
        return max(len(cl) for cl in self.strong_twin_classes())

    # ---------------------------------------------------------- invariants
    def canonical_keys(self) -> Dict:
        """Invariant keys for the colors by refinement over the structure constants.

        key_{i+1}(c) = (key_i(c), key_i(c^-), sorted multiset over (a,b) of
        (key_i(a), key_i(b), p^c_{ab})) starting from (is_diagonal, valency
        profile).  Used for configurations whose colors have no canonical names
        (orbital configurations of canonical groups).
        """
        N = self.N
        c = self.c
        cols = self.colors
        # structure constants p^k_{ij}: for each (x,y) with color k count z with c(x,z)=i, c(z,y)=j
        # (constant by coherence; we take it from a representative pair, but
        # average over representatives to be robust for non-coherent input)
        rep: Dict = {}
        for i in range(N):
            for j in range(N):
                rep.setdefault(c[i][j], (i, j))
        p: Dict[Hashable, Dict[Tuple, int]] = {}
        for col, (x, y) in rep.items():
            cnt: Dict[Tuple, int] = defaultdict(int)
            for z in range(N):
                cnt[(c[x][z], c[z][y])] += 1
            p[col] = dict(cnt)
        diag = self.diagonal_colors()
        key: Dict = {}
        for col in cols:
            x, y = rep[col]
            key[col] = (col in diag, self.out_degree(x, col), len(self.in_neighbors(y, col)))
        while True:
            new = {}
            for col in cols:
                items = sorted((key[a], key[b], v) for (a, b), v in p[col].items())
                new[col] = (key[col], key[self.paired(col)], tuple(items))
            # compress
            uniq = sorted(set(new.values()), key=_hk)
            idx = {u: i for i, u in enumerate(uniq)}
            comp = {col: idx[new[col]] for col in cols}
            if len(uniq) == len(set(key.values())):
                self._keys = comp
                return comp
            key = comp


def _hk(x):
    return canon(x)


def cc_from_pair_coloring(vertices: Sequence[int], c: Callable[[int, int], Hashable]) -> ClassicalCC:
    return ClassicalCC(vertices, c)
