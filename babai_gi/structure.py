"""Canonical structures on Gamma, choices at multiplicative cost, alignment.

Babai Sec. 5.1 (colored partitions), Sec. 4 (canonicity relative to choices,
Prop. 4.0.4), Sec. 11.1 (Procedure Align).

A ``Structure`` on Gamma = range(m) is a list of *cells* (disjoint subsets
covering Gamma), each with a canonical ``key``.  Cells with equal keys are
interchangeable (they have equal size); this encodes Babai's colored
equipartitions: a color class partitioned into blocks = several cells with the
same key.  Optionally one cell carries a canonically embedded Johnson scheme
J(m', t') (Babai Sec. 2.5.5, Thm. 7.3.1(b)): its vertices are labelled by
t'-subsets of an abstract m'-set.  The automorphism group of a structure in
Sym(Gamma) is the direct product over keys of (Sym(cell) wr Sym(#cells)), with
S^{(t')}(m') on the Johnson cell; it is explicitly generated (Align, step 2(iv)).

Choices ("individualization of ideal points", Babai Sec. 1.3.3/4) are made
through a ``Chooser``: the x-side records a trace and takes the first
candidate; the y-side replays all candidate sequences (Prop. 4.0.4: fix X' in
F(X), enumerate Y' in F(Y)), aborting early on any mismatch of canonical
invariants recorded in the trace.
"""

from __future__ import annotations

from math import comb
from typing import Any, Callable, Dict, FrozenSet, Hashable, Iterable, List, Optional, Sequence, Tuple

from .canon import canon
from .perm import Perm, from_cycles, identity, mul, parity


class Mismatch(Exception):
    """Raised on the y-side when a canonical invariant differs from the x-side trace."""


class Fixed:
    """Wrapper for choice candidates that are not permuted by Sym(Gamma) (e.g. colors)."""

    __slots__ = ("value",)

    def __init__(self, value):
        self.value = value

    def __eq__(self, other):
        return isinstance(other, Fixed) and other.value == self.value

    def __hash__(self):
        return hash(("Fixed", self.value))

    def __repr__(self):
        return f"Fixed({self.value!r})"

    def canon_value(self):
        return self.value


def apply_obj(obj: Any, sigma: Perm) -> Any:
    """Apply a permutation of Gamma to a choice object (vertices, tuples, sets of them)."""
    if isinstance(obj, bool):
        return obj
    if isinstance(obj, int):
        return sigma[obj]
    if isinstance(obj, Fixed) or isinstance(obj, str) or obj is None:
        return obj
    if isinstance(obj, tuple):
        return tuple(apply_obj(o, sigma) for o in obj)
    if isinstance(obj, frozenset):
        return frozenset(apply_obj(o, sigma) for o in obj)
    if isinstance(obj, list):
        return [apply_obj(o, sigma) for o in obj]
    raise TypeError(f"cannot permute choice object {obj!r}")


class Chooser:
    def choose(self, candidates: Sequence[Any]) -> Any:
        raise NotImplementedError

    def check(self, invariant: Hashable) -> None:
        raise NotImplementedError

    def choose_index(self, k: int) -> int:
        return self.choose(list(range(k)))


class RecordingChooser(Chooser):
    """x-side: take the first candidate, record the trace of events."""

    def __init__(self):
        self.trace: List[Tuple] = []
        self.chosen: List[Any] = []

    def choose(self, candidates: Sequence[Any]) -> Any:
        if not candidates:
            raise ValueError("empty candidate set")
        self.trace.append(("choice", len(candidates)))
        self.chosen.append(candidates[0])
        return candidates[0]

    def check(self, invariant: Hashable) -> None:
        self.trace.append(("inv", invariant))


class ReplayChooser(Chooser):
    """y-side: replay a path of choice indices against the x-side trace."""

    def __init__(self, trace: Sequence[Tuple], path: Sequence[int]):
        self.trace = trace
        self.path = list(path)
        self.taken: List[int] = []
        self.counts: List[int] = []
        self.chosen: List[Any] = []
        self.pos = 0

    def _next_event(self) -> Tuple:
        if self.pos >= len(self.trace):
            raise Mismatch("trace exhausted")
        ev = self.trace[self.pos]
        self.pos += 1
        return ev

    def choose(self, candidates: Sequence[Any]) -> Any:
        ev = self._next_event()
        if ev[0] != "choice" or ev[1] != len(candidates):
            raise Mismatch("candidate count differs")
        d = len(self.taken)
        idx = self.path[d] if d < len(self.path) else 0
        self.taken.append(idx)
        self.counts.append(len(candidates))
        self.chosen.append(candidates[idx])
        return candidates[idx]

    def check(self, invariant: Hashable) -> None:
        ev = self._next_event()
        if ev[0] != "inv" or ev[1] != invariant:
            raise Mismatch("invariant differs")


def enumerate_runs(proc: Callable[[Chooser], Any], trace: Sequence[Tuple]) -> Iterable[Tuple[Any, List[Any]]]:
    """Run ``proc`` for every sequence of choices consistent with ``trace``.

    Yields (result, chosen candidates) for each run that completes without a
    mismatch.  Runs are re-executed from scratch for each path (iterative DFS).
    """
    path: List[int] = []
    while True:
        ch = ReplayChooser(trace, path)
        try:
            result = proc(ch)
            if ch.pos != len(trace):
                raise Mismatch("trace not fully consumed")
            yield result, list(ch.chosen)
        except Mismatch:
            pass
        taken, counts = ch.taken, ch.counts
        i = len(taken) - 1
        while i >= 0 and taken[i] + 1 >= counts[i]:
            i -= 1
        if i < 0:
            return
        path = taken[:i] + [taken[i] + 1]


# --------------------------------------------------------------- structures

class JohnsonCell:
    """Vertices of a cell labelled by t'-subsets of an abstract m'-set."""

    __slots__ = ("m", "t", "labels")

    def __init__(self, m: int, t: int, labels: Dict[int, FrozenSet[int]]):
        self.m = m
        self.t = t
        self.labels = labels  # vertex -> frozenset subset of range(m)

    def invariant(self) -> Tuple:
        return ("johnson", self.m, self.t)


class Structure:
    def __init__(self, m: int, cells: Sequence[Tuple[Hashable, FrozenSet[int]]], johnson: Optional[JohnsonCell] = None,
                 johnson_cell: Optional[int] = None):
        self.m = m
        self.cells: List[Tuple[Hashable, FrozenSet[int]]] = [(k, frozenset(c)) for k, c in cells if c]
        self.johnson = johnson
        self.johnson_cell = johnson_cell
        self._normalize()

    def _normalize(self) -> None:
        # keys with cells of different sizes are refined by size (Prop. 5.1.3)
        cells = [((k, len(c)), c) for k, c in self.cells]
        jc = None
        if self.johnson is not None and self.johnson_cell is not None:
            jcell = self.cells[self.johnson_cell][1]
            for i, (k, c) in enumerate(cells):
                if c == jcell:
                    jc = i
        order = sorted(range(len(cells)), key=lambda i: (_hk(cells[i][0]), sorted(cells[i][1])))
        self.cells = [cells[i] for i in order]
        if jc is not None:
            self.johnson_cell = order.index(jc)
            k, c = self.cells[self.johnson_cell]
            self.cells[self.johnson_cell] = ((k, "johnson", self.johnson.m, self.johnson.t), c)

    # ------------------------------------------------------------ queries
    def cell_of(self) -> Dict[int, int]:
        d = {}
        for i, (k, c) in enumerate(self.cells):
            for v in c:
                d[v] = i
        return d

    def key_of_vertex(self) -> Dict[int, Hashable]:
        d = {}
        for k, c in self.cells:
            for v in c:
                d[v] = k
        return d

    def invariant(self) -> Tuple:
        return tuple(sorted(((_hk(k), len(c)) for k, c in self.cells))) + (
            self.johnson.invariant() if self.johnson else ("nojohnson",),)

    def max_cell_size(self) -> int:
        return max(len(c) for k, c in self.cells)

    def is_trivial(self) -> bool:
        return len(self.cells) == 1 and self.johnson is None

    # ---------------------------------------------------------- refinement
    def refine(self, f: Callable[[int], Hashable], tag: Hashable = "r") -> "Structure":
        """Refine every cell by the canonical function f (keys get (key, tag, f(v)))."""
        new = []
        jc_set = self.cells[self.johnson_cell][1] if self.johnson_cell is not None else None
        new_j = None
        for k, c in self.cells:
            groups: Dict[Hashable, List[int]] = {}
            for v in c:
                groups.setdefault(f(v), []).append(v)
            for fv in sorted(groups, key=_hk):
                new.append(((k, tag, fv), frozenset(groups[fv])))
            if jc_set is not None and c == jc_set and len(groups) > 1:
                new_j = "split"
        johnson = self.johnson
        jcell = None
        if johnson is not None and new_j != "split":
            for i, (k, c) in enumerate(new):
                if c == jc_set:
                    jcell = i
        if jcell is None:
            johnson = None
        return Structure(self.m, new, johnson, jcell)

    def individualize(self, v: int, tag: Hashable = "ind") -> "Structure":
        return self.refine(lambda u: 1 if u == v else 0, tag)

    def mark(self, S: Iterable[int], tag: Hashable = "mark") -> "Structure":
        S = frozenset(S)
        return self.refine(lambda u: 1 if u in S else 0, tag)

    def split_cell(self, cell_index: int, blocks: Sequence[Iterable[int]], tag: Hashable = "blocks") -> "Structure":
        """Partition a cell into interchangeable blocks (equal keys)."""
        k, c = self.cells[cell_index]
        new = list(self.cells)
        del new[cell_index]
        covered = set()
        for b in blocks:
            fb = frozenset(b)
            covered |= fb
            new.append(((k, tag), fb))
        if covered != c:
            raise ValueError("blocks must partition the cell")
        johnson = self.johnson if self.johnson_cell != cell_index else None
        jcell = None
        if johnson is not None:
            jset = self.cells[self.johnson_cell][1]
            for i, (kk, cc) in enumerate(new):
                if cc == jset:
                    jcell = i
        return Structure(self.m, new, johnson, jcell)

    def with_johnson(self, cell_index: int, jc: JohnsonCell) -> "Structure":
        return Structure(self.m, list(self.cells), jc, cell_index)

    # ------------------------------------------------------- automorphisms
    def aut_gens(self) -> List[Perm]:
        """Generators of Aut(structure) <= Sym(Gamma)."""
        m = self.m
        gens: List[Perm] = []
        by_key: Dict[Hashable, List[int]] = {}
        for i, (k, c) in enumerate(self.cells):
            by_key.setdefault(k, []).append(i)
        for k, idxs in by_key.items():
            first = sorted(self.cells[idxs[0]][1])
            if idxs[0] == self.johnson_cell:
                jc = self.johnson
                assert jc is not None
                gens.extend(_johnson_cell_gens(m, jc))
            elif len(first) >= 2:
                gens.append(from_cycles(m, [first[:2]]))
                if len(first) > 2:
                    gens.append(from_cycles(m, [first]))
            if len(idxs) >= 2:
                lists = [sorted(self.cells[i][1]) for i in idxs]
                # swap of the first two cells, cycle of all cells
                p = list(range(m))
                for a, b in zip(lists[0], lists[1]):
                    p[a], p[b] = b, a
                gens.append(tuple(p))
                if len(idxs) > 2:
                    p = list(range(m))
                    for j in range(len(lists)):
                        src, dst = lists[j], lists[(j + 1) % len(lists)]
                        for a, b in zip(src, dst):
                            p[a] = b
                    gens.append(tuple(p))
        return gens

    def aut_order(self) -> int:
        from math import factorial
        o = 1
        by_key: Dict[Hashable, List[int]] = {}
        for i, (k, c) in enumerate(self.cells):
            by_key.setdefault(k, []).append(i)
        for k, idxs in by_key.items():
            s = len(self.cells[idxs[0]][1])
            if idxs[0] == self.johnson_cell:
                o *= factorial(self.johnson.m)  # type: ignore[union-attr]
            else:
                o *= factorial(s) ** len(idxs)
            o *= factorial(len(idxs))
        return o

    def has_odd_automorphism(self) -> bool:
        by_key: Dict[Hashable, List[int]] = {}
        for i, (k, c) in enumerate(self.cells):
            by_key.setdefault(k, []).append(i)
        for k, idxs in by_key.items():
            s = len(self.cells[idxs[0]][1])
            if idxs[0] == self.johnson_cell:
                jc = self.johnson
                if comb(jc.m - 2, jc.t - 1) % 2 == 1:  # type: ignore[union-attr]
                    return True
            elif s >= 2:
                return True
            if len(idxs) >= 2 and s % 2 == 1:
                return True
        return False

    def odd_automorphism(self) -> Optional[Perm]:
        for g in self.aut_gens():
            if parity(g) == 1:
                return g
        # products of generators may be odd even if no generator is: not needed
        # because every generating set above contains an odd element when one exists
        return None


def _johnson_cell_gens(m: int, jc: JohnsonCell) -> List[Perm]:
    """Permutations of Gamma induced on the Johnson cell by generators of Sym(Lambda)."""
    label_to_vertex = {lab: v for v, lab in jc.labels.items()}
    gens = []
    lam_gens = []
    if jc.m >= 2:
        lam_gens.append(from_cycles(jc.m, [[0, 1]]))
    if jc.m >= 3:
        lam_gens.append(from_cycles(jc.m, [list(range(jc.m))]))
    for tau in lam_gens:
        p = list(range(m))
        for v, lab in jc.labels.items():
            p[v] = label_to_vertex[frozenset(tau[i] for i in lab)]
        gens.append(tuple(p))
    return gens


def align(A: Structure, B: Structure, need_even: bool) -> Optional[Perm]:
    """A permutation sigma of Gamma with A^sigma = B (cells to cells with equal keys), or None.

    If need_even, the returned permutation is even (composing with an odd
    automorphism of B when necessary); None if no even isomorphism exists.
    """
    if A.m != B.m or A.invariant() != B.invariant():
        return None
    m = A.m
    byA: Dict[Hashable, List[int]] = {}
    byB: Dict[Hashable, List[int]] = {}
    for i, (k, c) in enumerate(A.cells):
        byA.setdefault(k, []).append(i)
    for i, (k, c) in enumerate(B.cells):
        byB.setdefault(k, []).append(i)
    if set(byA) != set(byB):
        return None
    p = [-1] * m
    for k in byA:
        ia, ib = byA[k], byB[k]
        if len(ia) != len(ib):
            return None
        for a, b in zip(ia, ib):
            ca, cb = A.cells[a][1], B.cells[b][1]
            if len(ca) != len(cb):
                return None
            if a == A.johnson_cell:
                if b != B.johnson_cell or A.johnson is None or B.johnson is None:
                    return None
                if (A.johnson.m, A.johnson.t) != (B.johnson.m, B.johnson.t):
                    return None
                inv_b = {lab: v for v, lab in B.johnson.labels.items()}
                for v, lab in A.johnson.labels.items():
                    w = inv_b.get(lab)
                    if w is None:
                        return None
                    p[v] = w
            else:
                for u, w in zip(sorted(ca), sorted(cb)):
                    p[u] = w
    if any(v < 0 for v in p):
        return None
    sigma = tuple(p)
    if need_even and parity(sigma) == 1:
        odd = B.odd_automorphism()
        if odd is None:
            return None
        sigma = mul(sigma, odd)
    return sigma


def _hk(x):
    """Canonical sort key (value-faithful, see ``canon``)."""
    return canon(x)


def coloring_structure(m: int, coloring: Sequence[Hashable], tag: Hashable = "col") -> Structure:
    groups: Dict[Hashable, List[int]] = {}
    for v in range(m):
        groups.setdefault(coloring[v], []).append(v)
    return Structure(m, [((tag, k), frozenset(vs)) for k, vs in groups.items()])
