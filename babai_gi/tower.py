"""Towers of block systems carried through the recursion (HBD App. A.1).

A *tower* for a group G <= Sym(Omega), Omega = range(n), is a sequence of
G-invariant partitions P_1 < P_2 < ... < P_k of Omega, each strictly coarser than
the previous one, above the partition P_0 into singletons.  The recursion of the
solver passes to every recursive call a tower that is invariant under the group of
that call:

* the tower of a call is invariant under every subgroup of its group, so it can be
  passed unchanged to calls on subgroups (Luks reductions, the reduction of the
  group in ``branch``, the kernels used by local certificates);
* when a call restricts its group to an invariant window Delta (Chain Rule, windows
  of local certificates and of the top action), the tower is restricted to Delta:
  every partition is intersected with Delta, and partitions that become equal to the
  previous one, or trivial (one block), are dropped (:meth:`restrict`);
* a transitive call never looks at block systems that are not coarser than the top
  partition P_k of its tower: it computes a maximal (coarsest non-trivial) block
  system of the action of G on the blocks of P_k and appends it (:meth:`extend`).

So the top of the tower always records the level of the block structure at which
the current Johnson (or Luks) reduction acts, and the levels below it are those that
the recursion will meet after descending into kernels.  This is what makes the
potential of HBD App. A.2 decrease (``PROOF.md``):

    rho(T) = sum over consecutive pairs (P_{i-1}, P_i), i = 1..k+1, P_{k+1} = {Omega},
             of f(r_i),   f(r) = 2 floor(log2 r) - 1,

where r_i is the number of blocks of P_{i-1} contained in one block of P_i (all
equal, G being transitive on the blocks of each level when G is transitive).

A partition is stored as a tuple ``blk`` with ``blk[p]`` = index of the block of
point p; block indices are 0..r-1 in order of first occurrence.
"""

from __future__ import annotations

from typing import List, Sequence, Tuple


class Tower:
    __slots__ = ("n", "levels")

    def __init__(self, n: int, levels: Sequence[Tuple[int, ...]] = ()) -> None:
        self.n = n
        self.levels: Tuple[Tuple[int, ...], ...] = tuple(tuple(b) for b in levels)

    @staticmethod
    def trivial(n: int) -> "Tower":
        return Tower(n, ())

    def is_trivial(self) -> bool:
        return not self.levels

    # ------------------------------------------------------------- queries
    def top_blocks(self) -> List[List[int]]:
        """The blocks of the top partition (singletons for the trivial tower), each
        sorted, in order of their smallest point."""
        if not self.levels:
            return [[p] for p in range(self.n)]
        blk = self.levels[-1]
        groups: List[List[int]] = []
        index = {}
        for p in range(self.n):
            b = blk[p]
            i = index.get(b)
            if i is None:
                index[b] = len(groups)
                groups.append([p])
            else:
                groups[i].append(p)
        return groups

    def block_counts(self) -> List[int]:
        """Number of blocks of P_0 (= n), P_1, ..., P_k."""
        return [self.n] + [len(set(b)) for b in self.levels]

    def potential(self) -> int:
        """rho(T) of HBD App. A.2 (with the top ratio included), for a tower of a
        transitive group: sum of f(r_i), f(r) = 2 floor(log2 r) - 1."""
        counts = self.block_counts() + [1]
        total = 0
        for a, b in zip(counts, counts[1:]):
            r = a // b
            if r >= 2:
                total += 2 * (r.bit_length() - 1) - 1
        return total

    # ---------------------------------------------------------- operations
    def extend(self, blocks: Sequence[Sequence[int]]) -> "Tower":
        """The tower with a new top partition ``blocks`` (which must be coarser than
        the current top and have at least two blocks)."""
        blk = [0] * self.n
        for i, b in enumerate(blocks):
            for p in b:
                blk[p] = i
        return Tower(self.n, self.levels + (tuple(blk),))

    def restrict(self, pts: Sequence[int]) -> "Tower":
        """The tower restricted to the invariant window ``pts`` (point ``pts[i]``
        becomes point ``i``)."""
        new_levels: List[Tuple[int, ...]] = []
        prev = len(pts)
        for blk in self.levels:
            ids: dict = {}
            nb = tuple(ids.setdefault(blk[p], len(ids)) for p in pts)
            c = len(ids)
            if c == 1:
                break               # this level and all coarser ones are trivial on the window
            if c == prev:
                continue            # equal to the previous level on the window
            new_levels.append(nb)
            prev = c
        return Tower(len(pts), new_levels)

    def __repr__(self) -> str:
        return f"Tower(n={self.n}, counts={self.block_counts()})"
