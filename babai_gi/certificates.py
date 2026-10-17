"""Local certificates (Babai Sec. 10.1, Thm. 10.1.3, Procedure LocalCertificates;
HBD Sec. 6.1) and their comparison (Babai Prop. 10.1.11; HBD Sec. 6.1.2, eq. (10)-(12)).

Setting: G <= S(Omega) transitive with a giant representation phi: G -> S(Gamma)
coming from the Johnson action on the standard blocks B_T, T in binom(Gamma, t)
(Babai Thm. 8.5.1); a test set A in binom(Gamma, k).

Procedure LocalCertificates (Babai 10.1, lines 01-11):
    W := empty, H(W) := G_A = phi^{-1}(S(Gamma)_A)
    while H(W)^A >= Alt(A) and aff(H(W), psi_A) is not contained in W:
        W <- aff(H(W), psi_A);  recompute H(W) = Aut^W_{H(W_old)}(x)
    full      -> K(A) = H(W)_(Omega \\ W)  (K(A)^A >= Alt(A) by the Unaffected
                 Stabilizer Theorem 8.3.5, used as a black box and verified)
    not full  -> M(A) = H(W)^A.
Recomputing H(W) (lines 04a-04h): N = kernel of H(W_old) -> S(A); for every
sigma_bar in H(W_old)^A (<= k! elements) lift sigma and compute
Aut^{W_new}_{N sigma}(x) = ISO^{W_new}_N(x, x^{sigma^{-1}}) sigma by strong Luks
reduction (recursive String Isomorphism on the window W_new, where the orbits of
N have length <= n/k by the Affected Orbit Lemma, Cor. 8.3.7).

Below the thresholds of Thm. 8.3.5 (k > max(8, 2 + log2 n)) the verification
K(A)^A >= Alt(A) may fail; we then continue with the window W = Omega, which
makes the fullness decision exact (at a higher, non-guaranteed cost).
"""

from __future__ import annotations

from itertools import combinations, permutations
from math import factorial
from typing import Dict, FrozenSet, List, Optional, Sequence, Tuple

from .action import Coset, GroupWithAction
from .group import PermGroup, generated_subcoset
from .perm import Perm, act_string, identity, inv, mul, parity, sym_gens


class JohnsonData:
    """The Johnson case (Babai Def. 3.4.1): G with giant phi: G -> S(Gamma) and
    the system of standard blocks B_T indexed by t-subsets T of Gamma."""

    def __init__(self, Gw: GroupWithAction, t: int, blocks: List[List[int]], T_of_block: List[FrozenSet[int]],
                 tower=None):
        self.Gw = Gw
        # the tower of the Johnson-case call (tower.py); its top partition is ``blocks``
        # (or the singletons in the primitive case); recursive calls inside the Johnson
        # case (local certificates, top action, the reduced group) receive it, restricted
        if tower is None:
            from .tower import Tower
            tower = Tower.trivial(Gw.n)
        self.tower = tower
        self.m = Gw.m
        self.t = t
        self.blocks = blocks
        self.T_of_block = T_of_block
        self.block_of_T: Dict[FrozenSet[int], int] = {T: i for i, T in enumerate(T_of_block)}
        self.block_of_point: Dict[int, int] = {}
        for i, blk in enumerate(blocks):
            for p in blk:
                self.block_of_point[p] = i
        if Gw.phi_fn is None:
            fn = self._make_fast_phi()
            if fn is not None:
                for g, p in zip(Gw.G.gens, Gw.phi_gens):
                    if fn(g) != p:
                        fn = None
                        break
            Gw.phi_fn = fn

    def _make_fast_phi(self):
        """phi(g) read off the action on the standard blocks: gamma^phi(g) is the
        unique common element of T1^g and T2^g for two t-sets T1, T2 with
        T1 cap T2 = {gamma} (this is how the Johnson action determines the
        permutation of Gamma; it avoids sifting through a stabilizer chain)."""
        m, t = self.m, self.t
        blocks, T_of_block, block_of_point = self.blocks, self.T_of_block, self.block_of_point
        if t == 1:
            reps = []
            for gamma in range(m):
                b = self.block_of_T.get(frozenset([gamma]))
                if b is None:
                    return None
                reps.append(blocks[b][0])
            elem = [next(iter(T)) for T in T_of_block]

            def phi_fn(g: Perm) -> Perm:
                return tuple(elem[block_of_point[g[p]]] for p in reps)

            return phi_fn
        if m < 2 * t - 1:
            return None
        pairs = []
        for gamma in range(m):
            others = [v for v in range(m) if v != gamma]
            T1 = frozenset([gamma] + others[:t - 1])
            T2 = frozenset([gamma] + others[t - 1:2 * (t - 1)])
            b1, b2 = self.block_of_T.get(T1), self.block_of_T.get(T2)
            if b1 is None or b2 is None:
                return None
            pairs.append((blocks[b1][0], blocks[b2][0]))

        def phi_fn2(g: Perm) -> Perm:
            out = []
            for p1, p2 in pairs:
                S = T_of_block[block_of_point[g[p1]]] & T_of_block[block_of_point[g[p2]]]
                if len(S) != 1:
                    raise ValueError("element does not act as a Johnson group on the standard blocks")
                out.append(next(iter(S)))
            return tuple(out)

        return phi_fn2

    def omega_of(self, A: FrozenSet[int]) -> FrozenSet[int]:
        """Omega(A) = union of the blocks B_T with T subset of A (Babai Sec. 10.1)."""
        out = set()
        for T, i in self.block_of_T.items():
            if T <= A:
                out.update(self.blocks[i])
        return frozenset(out)

    def is_primitive(self) -> bool:
        return len(self.blocks) == self.Gw.n


class Iteration:
    __slots__ = ("W_old", "W_new", "N", "lifts", "H_old_A")

    def __init__(self, W_old, W_new, N, lifts, H_old_A):
        self.W_old = W_old
        self.W_new = W_new
        self.N = N                  # PermGroup on Omega: kernel of H(W_old) -> S(A)
        self.lifts = lifts          # list of (sigma_bar on positions of A, sigma in H(W_old))
        self.H_old_A = H_old_A      # PermGroup on range(k)


class Certificate:
    def __init__(self, A: FrozenSet[int], full: bool, W: FrozenSet[int], H: GroupWithAction,
                 HA: PermGroup, iterations: List[Iteration], K: Optional[PermGroup]):
        self.A = A
        self.A_sorted = sorted(A)
        self.full = full
        self.W = W
        self.H = H              # H(W) as GroupWithAction (final)
        self.HA = HA            # H(W)^A on positions range(k)  (= M(A) if not full)
        self.iterations = iterations
        self.K = K              # K(A) <= Aut_G(x) if full
        self.invariant = (full, tuple(len(it.W_new) for it in iterations), tuple(it.H_old_A.order() for it in iterations),
                          HA.order(), len(W))


def restrict_to(p: Perm, pts: Sequence[int]) -> Perm:
    index = {q: i for i, q in enumerate(pts)}
    return tuple(index[p[q]] for q in pts)


def is_giant_on(k: int, gens: Sequence[Perm]) -> bool:
    if k <= 2:
        return True
    return PermGroup(k, gens).order() * 2 >= factorial(k)


class LocalCertificates:
    """Local certificates of one string x (cached per test set)."""

    def __init__(self, solver, jd: JohnsonData, x: Sequence, k: int):
        self.solver = solver
        self.jd = jd
        self.Gw = jd.Gw
        self.x = tuple(x)
        self.k = k
        self.n = self.Gw.n
        self.m = self.Gw.m
        self.certs: Dict[FrozenSet[int], Certificate] = {}

    # ---------------------------------------------------------- helpers
    def setwise_stabilizer(self, A: FrozenSet[int]) -> GroupWithAction:
        """G_A = phi^{-1}(S(Gamma)_A cap G^phi) (Babai Notation 10.1.1)."""
        Gw = self.Gw
        m = self.m
        gens = sym_gens(sorted(A), m) + sym_gens([v for v in range(m) if v not in A], m)
        gens = Gw.intersect_image(gens)
        order = factorial(len(A)) * factorial(m - len(A))
        if not Gw.image_is_sym():
            order //= 2
        H = Gw.preimage(gens, image_order=order)
        return Gw.subgroup(H.gens, known_order=H.order())

    def image_on_A(self, H: GroupWithAction, A_sorted: List[int]) -> PermGroup:
        return PermGroup(len(A_sorted), [restrict_to(p, A_sorted) for p in H.phi_gens])

    def affected(self, H: GroupWithAction, A_sorted: List[int]) -> FrozenSet[int]:
        """aff(H, psi_A) = {u : H_u^A does not contain Alt(A)} (Babai Def. 10.1.4).

        By Prop. 8.3.6, |H^psi : H_u^psi| = |u^H| / |u^N| where N = ker psi_A; the
        stabilizer image contains Alt(A) iff this index is <= 2 (index 2 forces
        H^psi = Sym(A), H_u^psi = Alt(A) since Alt(A) has no subgroup of index 2).
        So u is affected iff |u^H| > 2 |u^N|.  This avoids point stabilizers.
        """
        N, _ = self.kernel_and_lifts(H, A_sorted)
        out = set()
        norb = {}
        for orb in N.orbits():
            for u in orb:
                norb[u] = len(orb)
        for orb in H.G.orbits():
            if len(orb) > 2 * norb[orb[0]]:
                out.update(orb)
        return frozenset(out)

    def kernel_and_lifts(self, H: GroupWithAction, A_sorted: List[int]) -> Tuple[PermGroup, List[Tuple[Perm, Perm]]]:
        """N = kernel of H -> S(A) and lifts of all elements of H^A (combined action, A first)."""
        key = ("kl", tuple(A_sorted))
        if key in H.cache:
            return H.cache[key]
        n, m = self.n, self.m
        comb = PermGroup(n + m, H.combined_gens, forced_prefix=[n + a for a in A_sorted],
                         known_order=H.G.known_order_or_none())
        levels = comb.levels
        kA = 0
        Aset = set(n + a for a in A_sorted)
        while kA < len(levels) and levels[kA].b in Aset:
            kA += 1
        K = comb.level_group(kA)
        N = PermGroup(n, [g[:n] for g in K.gens], known_order=K.order())
        lifts = []
        for r in comb.coset_reps_prefix(kA):
            sigma = r[:n]
            sbar = tuple(A_sorted.index(r[n + a] - n) for a in A_sorted)
            lifts.append((sbar, sigma))
        H.cache[key] = (N, lifts)
        return N, lifts

    # ------------------------------------------------------- conjugation
    def conjugate(self, cert: Certificate, g: Perm, A2: FrozenSet[int]) -> Certificate:
        """The certificate of A^g for an automorphism g of x (canonicity: cert(x, A^g) = cert(x, A)^g)."""
        Gw = self.Gw
        gi = inv(g)
        A2_sorted = sorted(A2)

        def cj(p: Perm) -> Perm:
            return mul(mul(gi, p), g)

        def cj_group(P: PermGroup) -> PermGroup:
            return PermGroup(P.n, [cj(p) for p in P.gens], known_order=P.known_order_or_none())

        W2 = frozenset(g[u] for u in cert.W)
        H2 = Gw.subgroup([cj(p) for p in cert.H.G.gens], known_order=cert.H.G.known_order_or_none())
        HA2 = self.image_on_A(H2, A2_sorted)
        # positions of A map to positions of A2 through phi(g): the image on A2 of
        # g^{-1} sigma g is rho^{-1} sbar rho
        gbar = Gw.phi(g)
        pos2 = {a: i for i, a in enumerate(A2_sorted)}
        rho = [pos2[gbar[a]] for a in cert.A_sorted]
        its = []
        for it in cert.iterations:
            N2 = cj_group(it.N)
            lifts2 = []
            for sbar, sigma in it.lifts:
                s2 = cj(sigma)
                sb2 = [0] * len(rho)
                for i, si in enumerate(sbar):
                    sb2[rho[i]] = rho[si]
                lifts2.append((tuple(sb2), s2))
            its.append(Iteration(frozenset(g[u] for u in it.W_old), frozenset(g[u] for u in it.W_new), N2, lifts2,
                                 PermGroup(len(A2_sorted), [sb for sb, s in lifts2])))
        K2 = cj_group(cert.K) if cert.K is not None else None
        c2 = Certificate(A2, cert.full, W2, H2, HA2, its, K2)
        self.certs[A2] = c2
        self.solver.stats["lc_conjugated"] += 1
        return c2

    def recompute(self, H: GroupWithAction, A_sorted: List[int], W_new: FrozenSet[int], x: Sequence) -> Tuple[GroupWithAction, Iteration, bool]:
        """H(W_new) = Aut^{W_new}_{H}(x) by strong Luks reduction through N (Babai lines 04a-04h)."""
        N, lifts = self.kernel_and_lifts(H, A_sorted)
        HA = PermGroup(len(A_sorted), [sb for sb, s in lifts])
        pieces = []
        window = sorted(W_new)
        for sbar, sigma in lifts:
            x2 = act_string(x, inv(sigma))
            C = self.solver.iso_window(N, x, x2, window, self.jd.tower)
            if C is not None:
                pieces.append((C.group, mul(C.rep, sigma)))
        res = generated_subcoset(self.n, pieces)
        if res is None:
            raise RuntimeError("Aut^W(x) cannot be empty")
        Hgroup, rep = res
        H_new = self.Gw.subgroup(list(Hgroup.gens) + [rep])
        return H_new, Iteration(None, W_new, N, lifts, HA), True

    # ------------------------------------------------------- the procedure
    def certificate(self, A: FrozenSet[int]) -> Certificate:
        A = frozenset(A)
        if A in self.certs:
            return self.certs[A]
        A_sorted = sorted(A)
        k = len(A_sorted)
        x = self.x
        H = self.setwise_stabilizer(A)
        W: FrozenSet[int] = frozenset()
        iterations: List[Iteration] = []
        full = None
        while True:
            HA = self.image_on_A(H, A_sorted)
            if not is_giant_on(k, HA.gens):
                full = False
                break
            aff = self.affected(H, A_sorted)
            if aff <= W:
                full = True
                break
            W_new = W | aff
            H, it, _ = self.recompute(H, A_sorted, W_new, x)
            it.W_old = W
            iterations.append(it)
            W = W_new
            self.solver.stats["lc_iterations"] += 1
        K = None
        if full:
            K = H.G.pointwise_stabilizer([u for u in range(self.n) if u not in W])
            Kimgs = [restrict_to(self.Gw.phi(g), A_sorted) for g in K.gens]
            if not is_giant_on(k, Kimgs):
                # below the threshold of Thm. 8.3.5: make the decision exact with W = Omega
                # (unreachable when k > max(8, 2 + log2 n), Babai Thm. 8.3.5)
                from .errors import fallback
                fallback(self.solver.params.allow_fallbacks, "certificate of fullness not full (Babai Thm. 8.3.5)")
                self.solver.stats["lc_fallback_full_window"] += 1
                W_new = frozenset(range(self.n))
                if W_new != W:
                    H, it, _ = self.recompute(H, A_sorted, W_new, x)
                    it.W_old = W
                    iterations.append(it)
                    W = W_new
                HA = self.image_on_A(H, A_sorted)
                full = is_giant_on(k, HA.gens)
                K = H.G if full else None
        HA = self.image_on_A(H, A_sorted)
        cert = Certificate(A, bool(full), W, H, HA, iterations, K)
        self.certs[A] = cert
        self.solver.stats["lc_full" if full else "lc_notfull"] += 1
        return cert

    def colored_string(self, A: FrozenSet[int]) -> tuple:
        """x_A: mark the positions in Omega(A) (Babai Notation 10.1.10)."""
        OA = self.jd.omega_of(A)
        return tuple((self.x[u], 1 if u in OA else 0) for u in range(self.n))

    # ------------------------------------------------------- comparison
    def compare(self, cert: Certificate, other: "LocalCertificates", cert2: Certificate) -> Optional[Coset]:
        """ISO_G(x_A^{W(A)}, x'_{A'}^{W(A')}) (Babai Prop. 10.1.11) by replaying the
        trajectory of (x, A) against (x', A').  Returns the coset H(W(A)) pi or None."""
        if cert.invariant != cert2.invariant:
            return None
        Gw = self.Gw
        A1, A2 = cert.A_sorted, cert2.A_sorted
        m = self.m
        # tau in G mapping A to A' in the Gamma-action (parity fixed if needed)
        tau_bar = list(range(m))
        rest1 = [v for v in range(m) if v not in cert.A]
        rest2 = [v for v in range(m) if v not in cert2.A]
        for a, b in zip(A1, A2):
            tau_bar[a] = b
        for a, b in zip(rest1, rest2):
            tau_bar[a] = b
        tau_bar = tuple(tau_bar)
        if not Gw.image_is_sym() and parity(tau_bar) == 1:
            if len(rest2) >= 2:
                t = list(tau_bar)
                i, j = rest1[0], rest1[1]
                t[i], t[j] = t[j], t[i]
                tau_bar = tuple(t)
            elif len(A2) >= 2:
                t = list(tau_bar)
                i, j = A1[0], A1[1]
                t[i], t[j] = t[j], t[i]
                tau_bar = tuple(t)
            else:
                return None
        tau = Gw.lift(tau_bar)
        if tau is None:
            return None
        xA = self.colored_string(cert.A)
        yA = other.colored_string(cert2.A)
        pi0 = tau
        for it, it2 in zip(cert.iterations, cert2.iterations):
            W_new, W2_new = it.W_new, it2.W_new
            window = sorted(W_new)
            pieces = []
            for sbar, sigma in it.lifts:
                pi = mul(sigma, pi0)
                if frozenset(pi[u] for u in W_new) != W2_new:
                    continue
                y2 = act_string(yA, inv(pi))
                R = self.solver.iso_window(it.N, xA, y2, window, self.jd.tower)
                if R is not None:
                    pieces.append((R.group, mul(R.rep, pi)))
            res = generated_subcoset(self.n, pieces)
            if res is None:
                return None
            Hgroup, pi0 = res
        # final check on the full window W(A) (the last iteration already covers W(A))
        if frozenset(pi0[u] for u in cert.W) != cert2.W:
            return None
        return Coset(cert.H.G, pi0)

    def ordered_label(self, cert: Certificate, T: Sequence[int]) -> Tuple[int, ...]:
        """Canonical label of the ordering T of A under H(A)^A (cosets of the image group)."""
        pos = {a: i for i, a in enumerate(cert.A_sorted)}
        p = tuple(pos[t] for t in T)
        best = None
        for h in cert.HA.elements():
            q = tuple(h[i] for i in p)  # (T)^h in positions
            if best is None or q < best:
                best = q
        return best  # type: ignore[return-value]
