"""Cosets, windows (restriction + lifting) and groups equipped with a
homomorphism phi: G -> Sym(Gamma).

* ``Coset``: a right coset H sigma (Babai Def. 3.1.2 output format: generators of
  Aut_G(x) and a coset representative).
* ``WindowLifter``: for a G-invariant window Delta, the restriction G^Delta
  together with the ability to lift elements of G^Delta back to G and the
  kernel G_(Delta) (Babai Obs. 3.1.10 "reducing to the window").
* ``GroupWithAction``: G <= S(Omega) with phi given on generators.  Kernels,
  images phi(g), lifts phi^{-1}(tau) and preimages phi^{-1}(H) are computed
  through the combined action on Omega + Gamma (HBD Exercise 2.1.1(c)).
"""

from __future__ import annotations

from math import factorial
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple

from .group import PermGroup, even_subgroup_gens
from .perm import Perm, identity, inv, is_identity, mul, parity


class Coset:
    """Right coset ``group * rep``."""

    __slots__ = ("group", "rep")

    def __init__(self, group: PermGroup, rep: Perm):
        self.group = group
        self.rep = tuple(rep)

    @property
    def n(self) -> int:
        return self.group.n

    def order(self) -> int:
        return self.group.order()

    def contains(self, g: Perm) -> bool:
        return self.group.contains(mul(tuple(g), inv(self.rep)))

    def elements(self) -> Iterable[Perm]:
        for h in self.group.elements():
            yield mul(h, self.rep)

    def shift_right(self, sigma: Perm) -> "Coset":
        """(H rep) sigma = H (rep sigma)."""
        return Coset(self.group, mul(self.rep, sigma))

    def __repr__(self) -> str:
        return f"Coset(|H|={self.group.order()}, rep={self.rep})"


def window_lifter(G: PermGroup, window: Sequence[int]) -> "WindowLifter":
    """Cached WindowLifter for (G, window)."""
    key = frozenset(window)
    L = G.lifter_cache.get(key)
    if L is None:
        L = WindowLifter(G, window)
        G.lifter_cache[key] = L
    return L


class WindowLifter:
    """Restriction of G to an invariant window and lifting back (Babai Obs. 3.1.10)."""

    def __init__(self, G: PermGroup, window: Sequence[int]):
        self.G = G
        self.pts = sorted(set(window))
        self.index = {p: i for i, p in enumerate(self.pts)}
        self._H: Optional[PermGroup] = None
        self._k: Optional[int] = None
        imgs = []
        seen = set()
        for g in G.gens:
            r = tuple(self.index[g[p]] for p in self.pts)
            if r not in seen and not is_identity(r):
                seen.add(r)
                imgs.append(r)
        self.restricted = PermGroup(len(self.pts), imgs)

    def _chain(self) -> Tuple[PermGroup, int]:
        if self._H is None:
            H = self.G.prefix_group(self.pts)
            levels = H.levels
            k = 0
            pset = set(self.pts)
            while k < len(levels) and levels[k].b in pset:
                k += 1
            self._H, self._k = H, k
        return self._H, self._k  # type: ignore

    def kernel(self) -> PermGroup:
        """G_(Delta): pointwise stabilizer of the window."""
        H, k = self._chain()
        return H.level_group(k)

    def lift(self, pi: Perm) -> Optional[Perm]:
        """An element of G whose restriction to the window is ``pi`` (indexed by self.pts)."""
        H, k = self._chain()
        levels = H.levels
        n = self.G.n
        cur = [self.pts[pi[i]] for i in range(len(self.pts))]
        g = identity(n)
        for i in range(k):
            lev = levels[i]
            beta = cur[self.index[lev.b]]
            u = lev.trans.get(beta)
            if u is None:
                return None
            ui = lev.trans_inv[beta]
            cur = [ui[c] for c in cur]
            g = mul(u, g)
        for j, p in enumerate(self.pts):
            if cur[j] != p:
                return None
        return g

    def lift_group(self, H: PermGroup, known_order: Optional[int] = None) -> PermGroup:
        """<lifts of generators of H, kernel>, H <= G^Delta (cached per H object)."""
        cached = getattr(H, "_lifted_by", None)
        if cached is not None and cached[0] is self:
            return cached[1]
        gens = []
        for h in H.gens:
            l = self.lift(h)
            if l is None:
                raise ValueError("element not in restriction")
            gens.append(l)
        K = self.kernel()
        gens.extend(K.gens)
        if known_order is None and H.known_order_or_none() is not None:
            known_order = H.order() * K.order()
        L = PermGroup(self.G.n, gens, known_order=known_order)
        H._lifted_by = (self, L)  # type: ignore[attr-defined]
        return L

    def lift_coset(self, C: Optional[Coset]) -> Optional[Coset]:
        if C is None:
            return None
        rep = self.lift(C.rep)
        if rep is None:
            raise ValueError("coset representative not in restriction")
        return Coset(self.lift_group(C.group), rep)

    def restrict_string(self, x: Sequence) -> tuple:
        return tuple(x[p] for p in self.pts)


class GroupWithAction:
    """G <= S(Omega) with a homomorphism phi: G -> S(Gamma) given on generators."""

    def __init__(self, G: PermGroup, m: int, phi_gens: Sequence[Perm],
                 phi_fn: Optional[Callable[[Perm], Perm]] = None):
        if len(phi_gens) != len(G.gens):
            raise ValueError("phi must be given on the generators of G")
        self.G = G
        self.n = G.n
        self.m = m
        self.phi_gens = [tuple(p) for p in phi_gens]
        # optional direct evaluation of phi (e.g. read off the Johnson action on
        # the standard blocks); must agree with phi_gens on the generators
        self.phi_fn = phi_fn
        if phi_fn is not None:
            for g, p in zip(G.gens, self.phi_gens):
                if phi_fn(g) != p:
                    raise ValueError("phi_fn disagrees with phi on a generator")
        n = self.n
        self.combined_gens = [tuple(g) + tuple(n + v for v in p) for g, p in zip(G.gens, self.phi_gens)]
        self._comb_omega: Optional[PermGroup] = None
        self._comb_gamma: Optional[PermGroup] = None
        self._kernel: Optional[PermGroup] = None
        self._image: Optional[PermGroup] = None
        self._image_is_giant: Optional[bool] = None
        self.cache: Dict = {}

    # ------------------------------------------------------------ chains
    def comb_omega(self) -> PermGroup:
        if self._comb_omega is None:
            self._comb_omega = PermGroup(self.n + self.m, self.combined_gens,
                                         forced_prefix=range(self.n), known_order=self.G.known_order_or_none())
        return self._comb_omega

    def comb_gamma(self) -> PermGroup:
        if self._comb_gamma is None:
            self._comb_gamma = PermGroup(self.n + self.m, self.combined_gens,
                                         forced_prefix=range(self.n, self.n + self.m),
                                         known_order=self.G.known_order_or_none())
        return self._comb_gamma

    def _gamma_levels(self) -> int:
        H = self.comb_gamma()
        levels = H.levels
        k = 0
        while k < len(levels) and levels[k].b >= self.n:
            k += 1
        return k

    def phi(self, g: Perm) -> Perm:
        """phi(g) for an arbitrary element g of G (sift through the Omega-first chain)."""
        if self.phi_fn is not None:
            return self.phi_fn(g)
        H = self.comb_omega()
        levels = H.levels
        n, m = self.n, self.m
        cur = list(g)
        acc = identity(n + m)
        for lev in levels:
            if lev.b >= n:
                break
            beta = cur[lev.b]
            u = lev.trans.get(beta)
            if u is None:
                raise ValueError("element not in G")
            ui = lev.trans_inv[beta]
            cur = [ui[c] for c in cur]
            acc = mul(u, acc)
        for i in range(n):
            if cur[i] != i:
                raise ValueError("element not in G")
        return tuple(acc[n + j] - n for j in range(m))

    def kernel(self) -> PermGroup:
        if self._kernel is None:
            H = self.comb_gamma()
            k = self._gamma_levels()
            K = H.level_group(k)
            n = self.n
            self._kernel = PermGroup(n, [g[:n] for g in K.gens], known_order=K.order())
        return self._kernel

    def image(self) -> PermGroup:
        if self._image is None:
            self._image = PermGroup(self.m, self.phi_gens)
        return self._image

    def image_order(self) -> int:
        return self.image().order()

    def image_is_giant(self) -> bool:
        if self._image_is_giant is None:
            self._image_is_giant = self.image_order() * 2 >= factorial(self.m)
        return self._image_is_giant

    def image_is_sym(self) -> bool:
        return self.image_order() == factorial(self.m)

    def lift(self, tau: Perm) -> Optional[Perm]:
        """An element g of G with phi(g) = tau, or None if tau is not in G^phi."""
        H = self.comb_gamma()
        k = self._gamma_levels()
        levels = H.levels
        n, m = self.n, self.m
        cur = [n + tau[j] for j in range(m)]
        g = identity(n + m)
        for i in range(k):
            lev = levels[i]
            beta = cur[lev.b - n]
            u = lev.trans.get(beta)
            if u is None:
                return None
            ui = lev.trans_inv[beta]
            cur = [ui[c] for c in cur]
            g = mul(u, g)
        for j in range(m):
            if cur[j] != n + j:
                return None
        return g[:n]

    def intersect_image(self, gens: Sequence[Perm]) -> List[Perm]:
        """Generators of <gens> cap G^phi when G^phi is a giant (Sym or Alt)."""
        if not self.image_is_giant():
            raise ValueError("intersect_image requires a giant image")
        if self.image_is_sym():
            return [g for g in gens if not is_identity(g)]
        return even_subgroup_gens(list(gens), self.m)

    def preimage(self, gens: Sequence[Perm], image_order: Optional[int] = None) -> PermGroup:
        """phi^{-1}(<gens>) for <gens> <= G^phi."""
        lifted = []
        for h in gens:
            l = self.lift(h)
            if l is None:
                raise ValueError("generator not in the image of phi")
            lifted.append(l)
        K = self.kernel()
        known = None
        if image_order is not None:
            known = image_order * K.order()
        return PermGroup(self.n, lifted + K.gens, known_order=known)

    def subgroup(self, gens: Sequence[Perm], known_order: Optional[int] = None) -> "GroupWithAction":
        gens = [tuple(g) for g in gens if not is_identity(g)]
        uniq = list(dict.fromkeys(gens))
        H = PermGroup(self.n, uniq, known_order=known_order)
        return GroupWithAction(H, self.m, [self.phi(g) for g in H.gens], phi_fn=self.phi_fn)

    def restricted_image_gens(self, points: Sequence[int]) -> Tuple[List[Perm], Dict[int, int]]:
        """Images of the generators restricted to a phi-invariant subset of Gamma."""
        pts = list(points)
        index = {p: i for i, p in enumerate(pts)}
        return [tuple(index[p[q]] for q in pts) for p in self.phi_gens], index

    def odd_lift_fixing(self, moved: Sequence[int]) -> Optional[Perm]:
        """A lift of an odd permutation of Gamma supported on ``moved`` (if available)."""
        if len(moved) < 2:
            return None
        tau = list(range(self.m))
        a, b = moved[0], moved[1]
        tau[a], tau[b] = b, a
        return self.lift(tuple(tau))


def restrict_gens(gens: Sequence[Perm], pts: Sequence[int]) -> List[Perm]:
    index = {p: i for i, p in enumerate(pts)}
    return [tuple(index[g[p]] for p in pts) for g in gens]


def perm_parity_on(p: Perm) -> int:
    return parity(p)
