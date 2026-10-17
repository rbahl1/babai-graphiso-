"""Johnson groups and the identification of a primitive group as a Johnson group.

Babai Sec. 1.2.1 / 2.2: S^{(t)}(Gamma), A^{(t)}(Gamma) acting on binom(Gamma, t)
("Johnson groups"); Babai Thm. 3.2.1 / HBD Thm. 3.1 (Cameron-Maroti) say large
primitive groups are Cameron groups; HBD Sec. 2.8 ([BLS]) gives the explicit
identification of such a group with Alt_m^{(k)} that we implement here:

    Upsilon = an orbital, Delta = another orbital;
    B(x,y) = {z : (x,z) not in Delta, (y,z) in Delta}  for (x,y) in Upsilon;
    C(x,y) = Gamma \\ union_{z in B(x,y)} {r : (z,r) in Delta};
    Lambda = {C(x,y)};  iota(omega) = {lambda in Lambda : omega in lambda}.

(HBD use the smallest/largest orbitals when m > (k+1)^2 - 2 and warn that the
roles must be swapped for small parameters; we simply try all ordered pairs of
orbitals and verify the result, which is at most (t+1)^2 attempts.)

Cameron groups with s >= 2 (Babai Def. 3.2.2: (A_k^{(t)})^s <= G <= S_k^{(t)} wr S_s
in product action on binom(k,t)^s points, transitive on the s factors) are
recognized by ``recognize_cameron`` from the orbital that is the Cartesian
product of s copies of the Johnson graph J(k, t) (the Hamming graph for t = 1):
its layers, their parallel classes (= the coordinates), the epimorphism onto
S_s and the kernel N, which acts on the fibers of a coordinate as a Johnson
group (Thm. 3.2.1: N has index <= s! and a system of imprimitivity on which it
acts as A_k^{(t)}).
"""

from __future__ import annotations

from itertools import combinations
from math import comb, factorial
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

from .group import PermGroup
from .perm import Perm, from_cycles, identity


def subsets_of(m: int, t: int) -> List[Tuple[int, ...]]:
    return [tuple(c) for c in combinations(range(m), t)]


def pairs_of(m: int) -> List[Tuple[int, int]]:
    return subsets_of(m, 2)  # type: ignore


def induced_on_subsets(tau: Perm, subsets: Sequence[Tuple[int, ...]], index: Dict[Tuple[int, ...], int]) -> Perm:
    return tuple(index[tuple(sorted(tau[v] for v in T))] for T in subsets)


def johnson_group_gens(m: int, t: int) -> List[Perm]:
    """Generators of S^{(t)}_m = Sym(m) acting on t-subsets (lexicographic order)."""
    subs = subsets_of(m, t)
    index = {T: i for i, T in enumerate(subs)}
    gens = []
    if m >= 2:
        gens.append(induced_on_subsets(from_cycles(m, [[0, 1]]), subs, index))
    if m >= 3:
        gens.append(induced_on_subsets(from_cycles(m, [list(range(m))]), subs, index))
    return gens


class JohnsonStructure:
    """A primitive group identified as a Johnson group S^{(t)}(Gamma) or A^{(t)}(Gamma).

    Attributes:
        m, t: |Gamma| and the subset size.
        phi_gens: images of the group's generators as permutations of Gamma = range(m).
        T_of_point: for each point of the original domain, the t-subset of Gamma.
        point_of_T: inverse map.
    """

    def __init__(self, m: int, t: int, phi_gens: List[Perm], T_of_point: List[FrozenSet[int]]):
        self.m = m
        self.t = t
        self.phi_gens = phi_gens
        self.T_of_point = T_of_point
        self.point_of_T: Dict[FrozenSet[int], int] = {T: i for i, T in enumerate(T_of_point)}

    def __repr__(self) -> str:
        return f"JohnsonStructure(m={self.m}, t={self.t})"


class CameronStructure:
    """A primitive group recognized as a Cameron group with s >= 2 (Babai Def. 3.2.2):
    (A_k^{(t)})^s <= Gbar <= S_k^{(t)} wr S_s in product action on binom(k,t)^s
    points (t = 1: A_k^s <= Gbar <= S_k wr S_s on [k]^s, the Hamming scheme).

    Attributes: k, t, s; c = binom(k, t) (points per coordinate); ``class_images``
    = action of the generators on the s coordinates (the parallel classes of
    layers); ``N_gens`` = generators of the kernel N of that action (a normal
    subgroup of index <= s!, Babai Thm. 3.2.1 / Prop. 3.2.5); ``fibers`` = the c
    fibers of the first coordinate, a system of imprimitivity of N on which N
    acts as the Johnson group S_k^{(t)} or A_k^{(t)}; ``layers`` = the vertex sets
    of the s c^{s-1} layers (copies of J(k, t)) and ``layer_class`` their coordinate.
    """

    def __init__(self, k: int, t: int, s: int, class_images: List[Perm], N_gens: List[Perm],
                 fibers: List[List[int]], layers: Optional[List[FrozenSet[int]]] = None,
                 layer_class: Optional[List[int]] = None):
        self.k = k
        self.t = t
        self.s = s
        self.c = comb(k, t)
        self.class_images = class_images
        self.N_gens = N_gens
        self.fibers = fibers
        self.layers = layers if layers is not None else []
        self.layer_class = layer_class if layer_class is not None else []

    def __repr__(self) -> str:
        return f"CameronStructure(k={self.k}, t={self.t}, s={self.s})"


#: backwards-compatible name (t = 1)
HammingStructure = CameronStructure


def recognize_hamming(Gbar: PermGroup) -> Optional[CameronStructure]:
    """The t = 1 case of ``recognize_cameron``: S_c wr S_s in product action on
    [c]^s (Hamming graph; lines = maximal cliques through a vertex)."""
    return recognize_cameron(Gbar, ts=(1,))


def _cameron_candidates(N: int, ts: Optional[Sequence[int]]) -> List[Tuple[int, int, int, int]]:
    """All (k, t, s) with s >= 2, k >= 2t + 1, binom(k, t)^s = N (Def. 3.2.2 needs
    k >= max(2t, 5); c = k >= 3 is also accepted for t = 1, the reduction being
    verified anyway).  Returns tuples (k, t, s, c = binom(k, t))."""
    out = []
    if N < 9:
        return out
    # c >= 3 and c^s = N force s < bit_length(N)
    for s in range(2, N.bit_length()):
        c = iroot(N, s)
        if c < 3 or c ** s != N:
            continue
        if ts is None or 1 in ts:
            out.append((c, 1, s, c))
        t = 2
        while comb(2 * t + 1, t) <= c:
            if ts is None or t in ts:
                k = 2 * t + 1
                while comb(k, t) < c:
                    k += 1
                if comb(k, t) == c:
                    out.append((k, t, s, c))
            t += 1
    return out


def iroot(N: int, s: int) -> int:
    """floor(N^(1/s)) for integers N >= 0, s >= 1, by bisection in exact integer
    arithmetic: lo^s <= N < hi^s holds throughout, and hi - lo halves each step, so
    the loop runs floor(bit_length(N)/s) + 1 times."""
    lo, hi = 0, 1 << (N.bit_length() // s + 1)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** s <= N:
            lo = mid
        else:
            hi = mid
    return lo


def recognize_cameron(Gbar: PermGroup, ts: Optional[Sequence[int]] = None,
                      orbs: Optional[List[List[Tuple[int, int]]]] = None) -> Optional[CameronStructure]:
    """Recognize a Cameron group with s >= 2 (Babai Def. 3.2.2 / Thm. 3.2.1,
    "Cameron groups can be recognized and their structure mapped out in
    polynomial time [BaLS]") from its orbitals, for every t >= 1 (``ts``
    restricts the subset sizes tried).

    Gbar >= (A_k^{(t)})^s acts transitively on the s coordinates, so the pairs of
    points that differ in exactly one coordinate i, with |x_i \\ y_i| = 1, form a
    single orbital: the Cartesian product J(k,t) [] ... [] J(k,t) of s Johnson
    graphs (for t = 1 the Hamming graph H(s, k)).  In this graph
      * the neighbourhood of x splits into s connected components (one per
        coordinate, each a rook's graph K_t [] K_{k-t}; cliques K_{k-1} for t = 1);
      * the component of (x, i) under "(x, i) ~ (y, j) if y is in component i of x
        and x in component j of y" is the layer L_i(x) = {y : y_j = x_j for j != i},
        a copy of J(k, t) with binom(k,t) vertices;
      * two disjoint layers are parallel (same coordinate) iff the edges between
        them form a perfect matching; the parallel classes are the coordinates.
    The action on the s classes gives the epimorphism Gbar -> S_s whose kernel N
    (index <= s!) preserves the fibers {y : y_1 = T} of the first coordinate and
    acts on them as a Johnson group on Gamma_1 (verified with
    ``recognize_johnson``; for t = 1 as a giant).  Returns None if any check fails.
    """
    from .action import GroupWithAction
    N = Gbar.n
    cands = _cameron_candidates(N, ts)
    if not cands:
        return None
    if orbs is None:
        orbs = orbitals(Gbar)
    for k, t, s, c in cands:
        deg_coord = t * (k - t)                       # valency of J(k, t)
        deg = s * deg_coord
        for o in orbs:
            if len(o) != N * deg:
                continue
            adj: List[set] = [set() for _ in range(N)]
            for (x, y) in o:
                adj[x].add(y)
            if any(len(a) != deg for a in adj) or any(x not in adj[y] for x in range(N) for y in adj[x]):
                continue
            # local classes: components of the neighbourhood of every vertex
            local: List[List[FrozenSet[int]]] = []
            cls_at: List[Dict[int, int]] = []
            ok = True
            for x in range(N):
                comp_of: Dict[int, int] = {}
                comps: List[List[int]] = []
                for y in sorted(adj[x]):
                    if y in comp_of:
                        continue
                    stack = [y]
                    comp_of[y] = len(comps)
                    cur = [y]
                    while stack:
                        z = stack.pop()
                        for w in adj[z]:
                            if w in adj[x] and w not in comp_of:
                                comp_of[w] = len(comps)
                                cur.append(w)
                                stack.append(w)
                    comps.append(cur)
                if len(comps) != s or any(len(cp) != deg_coord for cp in comps):
                    ok = False
                    break
                local.append([frozenset(cp) for cp in comps])
                cls_at.append(comp_of)
            if not ok:
                continue
            # layers: union-find on (vertex, local class)
            parent = list(range(N * s))

            def find(a: int) -> int:
                while parent[a] != a:
                    parent[a] = parent[parent[a]]
                    a = parent[a]
                return a

            for x in range(N):
                for ci, cp in enumerate(local[x]):
                    for y in cp:
                        cj = cls_at[y][x]
                        ra, rb = find(x * s + ci), find(y * s + cj)
                        if ra != rb:
                            parent[ra] = rb
            groups: Dict[int, set] = {}
            for x in range(N):
                for ci in range(s):
                    groups.setdefault(find(x * s + ci), set()).add(x)
            layers = sorted((frozenset(g) for g in groups.values()), key=sorted)
            if len(layers) != s * c ** (s - 1) or any(len(L) != c for L in layers) or len(set(layers)) != len(layers):
                continue
            layers_of: Dict[int, List[int]] = {}
            for li, L in enumerate(layers):
                for v in L:
                    layers_of.setdefault(v, []).append(li)
            if any(len(layers_of.get(v, ())) != s for v in range(N)):
                continue
            # parallel classes (coordinates)
            parent2 = list(range(len(layers)))

            def find2(a: int) -> int:
                while parent2[a] != a:
                    parent2[a] = parent2[parent2[a]]
                    a = parent2[a]
                return a

            def parallel(L: FrozenSet[int], L2: FrozenSet[int]) -> bool:
                if L & L2:
                    return False
                return all(len(adj[v] & L2) == 1 for v in L) and all(len(adj[v] & L) == 1 for v in L2)

            tested = set()
            for li, L in enumerate(layers):
                for v in L:
                    for w in adj[v]:
                        if w in L:
                            continue
                        for lj in layers_of[w]:
                            key = (min(li, lj), max(li, lj))
                            if key in tested:
                                continue
                            tested.add(key)
                            if parallel(L, layers[lj]):
                                ra, rb = find2(li), find2(lj)
                                if ra != rb:
                                    parent2[ra] = rb
            classes: Dict[int, List[int]] = {}
            for li in range(len(layers)):
                classes.setdefault(find2(li), []).append(li)
            cls = sorted(classes.values(), key=lambda cl: sorted(layers[cl[0]]))
            if len(cls) != s or any(len(cl) != c ** (s - 1) for cl in cls):
                continue
            good = True
            for cl in cls:
                cover = set()
                for li in cl:
                    cover |= layers[li]
                if len(cover) != N:
                    good = False
            if not good:
                continue
            class_index = {}
            for ci, cl in enumerate(cls):
                for li in cl:
                    class_index[li] = ci
            layer_index = {L: li for li, L in enumerate(layers)}
            class_images = []
            for g in Gbar.gens:
                img = []
                for ci, cl in enumerate(cls):
                    L = layers[cl[0]]
                    lj = layer_index.get(frozenset(g[v] for v in L))
                    if lj is None:
                        good = False
                        break
                    img.append(class_index[lj])
                if not good:
                    break
                class_images.append(tuple(img))
            if not good:
                continue
            Gw = GroupWithAction(Gbar, s, class_images)
            Nk = Gw.kernel()
            # fibers of coordinate 1: components of the union of the layers of classes 2..s
            parent3 = list(range(N))

            def find3(a: int) -> int:
                while parent3[a] != a:
                    parent3[a] = parent3[parent3[a]]
                    a = parent3[a]
                return a

            for ci in range(1, s):
                for li in cls[ci]:
                    L = sorted(layers[li])
                    for v in L[1:]:
                        ra, rb = find3(L[0]), find3(v)
                        if ra != rb:
                            parent3[ra] = rb
            fib: Dict[int, List[int]] = {}
            for v in range(N):
                fib.setdefault(find3(v), []).append(v)
            fibers = sorted(fib.values())
            if len(fibers) != c or any(len(f) != c ** (s - 1) for f in fibers):
                continue
            # N must preserve the fibers and act on them as the Johnson group S_k^{(t)} / A_k^{(t)}
            fib_index = {frozenset(f): i for i, f in enumerate(fibers)}
            if any(frozenset(g[v] for v in f) not in fib_index for g in Nk.gens for f in fibers):
                continue
            Nact, _ = Nk.induced_action(fibers)
            if t == 1:
                if Nact.order() * 2 < factorial(c):
                    continue
            else:
                jh = recognize_johnson(Nact)
                if jh is None or (jh.m, jh.t) != (k, t):
                    continue
            layer_class = [class_index[li] for li in range(len(layers))]
            return CameronStructure(k, t, s, class_images, list(Nk.gens), fibers, layers, layer_class)
    return None


def johnson_phi(img: Perm, jh: "JohnsonStructure") -> Perm:
    """The permutation of Gamma induced by a permutation ``img`` of the points of the
    recognised group (points = t-subsets of Gamma via ``jh.T_of_point``).

    gamma^phi is the unique common element of T1^img and T2^img for two t-subsets
    T1, T2 with T1 cap T2 = {gamma} (t = 1: T1 = {gamma}).  The result is checked to
    induce ``img`` on all points: every element of the recognised group does (the
    permutations of the points induced by Sym(Gamma) form a group containing the
    generators), so a failure means ``img`` is not in that group."""
    m, t = jh.m, jh.t
    T_of = jh.T_of_point
    pt = jh.point_of_T
    phi = [0] * m
    if t == 1:
        for gamma in range(m):
            (phi[gamma],) = tuple(T_of[img[pt[frozenset([gamma])]]])
    else:
        if m < 2 * t - 1:
            raise ValueError("Johnson structure with m < 2t - 1")
        for gamma in range(m):
            others = [v for v in range(m) if v != gamma]
            T1 = frozenset([gamma] + others[:t - 1])
            T2 = frozenset([gamma] + others[t - 1:2 * (t - 1)])
            S = T_of[img[pt[T1]]] & T_of[img[pt[T2]]]
            if len(S) != 1:
                raise ValueError("permutation not induced by Sym(Gamma)")
            (phi[gamma],) = tuple(S)
    if len(set(phi)) != m:
        raise ValueError("permutation not induced by Sym(Gamma)")
    for p, T in enumerate(T_of):
        if T_of[img[p]] != frozenset(phi[g] for g in T):
            raise ValueError("permutation not induced by Sym(Gamma)")
    return tuple(phi)


def orbitals(G: PermGroup) -> List[List[Tuple[int, int]]]:
    """Orbits of G on ordered pairs of distinct points (Babai Sec. 13.1 "orbitals")."""
    n = G.n
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    return G.orbits_on(pairs, lambda p, g: (g[p[0]], g[p[1]]))


def recognize_johnson(Gbar: PermGroup) -> Optional[JohnsonStructure]:
    """Identify a primitive group as a giant (t=1) or a Johnson group with t >= 2.

    Returns None if the group is neither (e.g. a Cameron group with s >= 2 in
    product action, or one of the small exceptions to the Cameron-Maroti bound).
    """
    N = Gbar.n
    if N <= 1:
        return None
    if Gbar.order() * 2 >= factorial(N):
        return JohnsonStructure(N, 1, list(Gbar.gens), [frozenset([i]) for i in range(N)])
    orbs = orbitals(Gbar)
    candidates = []
    for t in range(2, N):
        for k in range(2 * t + 1, N + 1):
            c = comb(k, t)
            if c == N:
                candidates.append((k, t))
            if c > N:
                break
    for k, t in candidates:
        if len(orbs) != t:
            continue
        result = _identify(Gbar, orbs, k, t)
        if result is not None:
            return result
    return None


def _identify(Gbar: PermGroup, orbs: List[List[Tuple[int, int]]], k: int, t: int) -> Optional[JohnsonStructure]:
    """Try each orbital as the Johnson-graph relation |T1 \\ T2| = 1 and rebuild Gamma.

    For small parameters the [BLS]/HBD construction with "smallest/largest
    orbital" picks up spurious sets (HBD's condition m > (k+1)^2 - 2 fails), so
    we use the following elementary variant, valid for all k >= 2t+1:
    graph distance in the Johnson graph equals |T1 \\ T2|; for an edge (x,y) with
    x \\ y = {i}, y \\ x = {j} the set A(x,y) = {T : d(T,x) < d(T,y)} equals
    {T : i in T, j notin T}.  Two edges (x,y), (x,y') have the same difference
    point i iff the triangle x,y,y' has k-t-2 common neighbours (a "star"
    triangle, common (t-1)-set), as opposed to t-2 for triangles inside a
    (t+1)-set; k-t-2 > t-2 since k > 2t.  Then P_i = {x} cup union of A(x,y')
    over the edges with difference point i.  Everything is verified afterwards
    (the sets form a k-set Lambda, each point lies in exactly t members, the
    group permutes Lambda and acts on it as a giant).
    """
    N = Gbar.n
    expected_star = k - t - 2
    expected_u = t - 2
    for o in orbs:
        adj: List[set] = [set() for _ in range(N)]
        for (x, y) in o:
            adj[x].add(y)
        deg = len(adj[0])
        if any(len(a) != deg for a in adj) or deg != t * (k - t):
            continue
        # all-pairs BFS distances
        dist = []
        ok = True
        for s in range(N):
            d = [-1] * N
            d[s] = 0
            q = [s]
            for p in q:
                dp = d[p] + 1
                for v in adj[p]:
                    if d[v] < 0:
                        d[v] = dp
                        q.append(v)
            if len(q) != N or max(d) > t:
                ok = False
                break
            dist.append(d)
        if not ok:
            continue
        Lambda: Dict[FrozenSet[int], int] = {}
        for x in range(N):
            if len(Lambda) >= k:
                break
            nbrs = sorted(adj[x])
            # classify neighbours by difference point
            classes: List[List[int]] = []
            for y in nbrs:
                placed = False
                for cl in classes:
                    y0 = cl[0]
                    if y0 in adj[y]:
                        common = len(adj[x] & adj[y] & adj[y0])
                        if common == expected_star:
                            cl.append(y)
                            placed = True
                            break
                        if common != expected_u:
                            ok = False
                            break
                if not ok:
                    break
                if not placed:
                    classes.append([y])
            if not ok or len(classes) != t or any(len(cl) != k - t for cl in classes):
                ok = False
                break
            dx = dist[x]
            for cl in classes:
                P = {x}
                for y in cl:
                    dy = dist[y]
                    P.update(T for T in range(N) if dx[T] < dy[T])
                fs = frozenset(P)
                if fs not in Lambda:
                    Lambda[fs] = len(Lambda)
        if not ok or len(Lambda) != k:
            continue
        members = list(Lambda.keys())
        T_of_point: List[FrozenSet[int]] = []
        for w in range(N):
            T = frozenset(i for i, C in enumerate(members) if w in C)
            if len(T) != t:
                ok = False
                break
            T_of_point.append(T)
        if not ok or len(set(T_of_point)) != N:
            continue
        phi_gens = []
        for g in Gbar.gens:
            img = []
            for C in members:
                j = Lambda.get(frozenset(g[r] for r in C))
                if j is None:
                    ok = False
                    break
                img.append(j)
            if not ok:
                break
            phi_gens.append(tuple(img))
        if not ok:
            continue
        image = PermGroup(k, phi_gens)
        if image.order() * 2 < factorial(k):
            continue
        return JohnsonStructure(k, t, phi_gens, T_of_point)
    return None
