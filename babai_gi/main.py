"""The main procedure: Luks's framework + Babai's Johnson-case machinery.

Babai Sec. 3.3 (Procedure Reduce-to-Johnson), Sec. 12 (Master Algorithm),
Sec. 9 (verification of top action), Sec. 10.2 (AggregateCertificates),
Sec. 11.1 (Procedure Align); HBD Sec. 3 (flowchart), 4.2, 5.3, 6.2.

``Solver.iso(G, x, y)`` returns ISO_G(x, y) as a ``Coset`` (generators of
Aut_G(x) and a representative, Babai Def. 3.1.2) or None.

Recursion structure (Babai Sec. 3.4 / HBD Appendix A):
  * intransitive G: Chain Rule over orbits (Prop. 3.1.7);
  * transitive G, small primitive quotient on a minimal block system
    (|Gbar| < m^{1+log2 m}, Cameron-Maroti): strong Luks reduction (Thm. 3.1.8);
  * large primitive quotient: identified as a Johnson group (Thm. 3.2.1 / HBD 2.8),
    giving a giant representation phi: G -> S(Gamma); if |Gamma| is below the
    polylogarithmic threshold ell(n) we enumerate S(Gamma) (Babai 1.1.2);
  * otherwise the Johnson case: primitive -> trivial case / pullback / Extended
    Design Lemma; imprimitive -> local certificates and their aggregation;
    the canonical structure found on Gamma is aligned (Sec. 11.1) and the group
    reduced to phi^{-1}(Aut(structure)); the recursion then restarts.
Every non-canonical choice is enumerated on the y-side (Prop. 4.0.4), which is
the multiplicative cost of the paper's analysis.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial, log2, ceil
from typing import Any, Callable, Dict, FrozenSet, Hashable, List, Optional, Sequence, Tuple

from .action import Coset, GroupWithAction, WindowLifter, window_lifter
from .canon import canon, normalize_letters
from .cc import ClassicalCC
from .certificates import JohnsonData, LocalCertificates, restrict_to, is_giant_on
from .design import extended_design_lemma
from .group import PermGroup, generated_subcoset, even_subgroup_gens
from .errors import TheoremViolation, fallback
from .johnson import JohnsonStructure, johnson_phi, recognize_johnson, recognize_cameron, orbitals
from .perm import (Perm, act_string, alt_gens, from_cycles, identity, inv, is_identity,
                   is_string_automorphism, maps_string, mul, parity, sym_gens)
from .soj import SOJParams, individualize_until, select_min, split_by_blocks, upcc_split_or_johnson
from .structure import (Chooser, Fixed, RecordingChooser, Structure, align, apply_obj, enumerate_runs)
from .tower import Tower
from .wl import KStructure, refine_structures


class Params:
    """Thresholds of the algorithm.  The keyword defaults are the papers' values
    (``Params.paper()``); ``Params.small_scale()`` lowers them so that the
    Johnson-case machinery executes on inputs a pure-Python implementation can
    process.  Correctness never depends on the values (every certificate is
    verified and every fallback is exact); the quasipolynomial bound of Babai
    Sec. 3.4 / HBD App. A is a statement about the paper's values.

    brute_force_order
        C_0 of Procedure Reduce-to-Johnson line 2 (Babai Sec. 3.3): |G| <= C_0 is
        solved by exhaustive search.  The papers leave the absolute constant
        unspecified; 5040 = 7!.
    quotient_enum_limit
        Cap on the order of the primitive quotient Gbar that is enumerated by the
        strong Luks reduction.  None (paper): Reduce-to-Johnson line 5 alone decides,
        i.e. Gbar is enumerated iff |Gbar| < m^{1+log2 m} (Thm. 3.2.3 Cameron-Maroti;
        HBD Thm. 3.1(a)), with no cap.
    cameron_maroti_degree
        Thm. 3.2.3 is stated for m >= 25 (Maroti: the only primitive groups of
        order >= m^{1+log2 m} that are not Cameron groups are M_12 and M_24).  A
        primitive quotient of degree m < 25 that is neither a Johnson group nor a
        product action is enumerated: its order is bounded by the absolute constant 24!.
    min_gamma
        ell(n): a Johnson quotient on Gamma with |Gamma| = m < ell(n) is enumerated
        ("brute force enumeration over Sym(Gamma) at a multiplicative cost of
        ell(n)!", Babai Sec. 1.2, Sec. 3.4 recurrence (v), HBD Sec. 3.1 "m <= C log n").
        None (paper): ell(n) = 10 * k_paper(n), the smallest m for which a test-set
        size k with max{8, 2 + log2 n} < k <= m/10 exists (Thm. 10.1.3 / Thm. 10.2.1;
        the hypothesis of the Unaffected Stabilizer Theorem 8.3.5 and of HBD Sec. 6.2
        "k ~ C log|Omega|, k < |Gamma|/10").
    local_k, k_rule
        Size k of the test sets of Local Certificates.  ``local_k`` fixes it;
        otherwise ``k_rule == "paper"`` gives k_paper(n) = floor(max{8, 2 + log2 n}) + 1,
        the smallest integer admitted by Thm. 10.1.3 (and k <= m/10 holds by the
        choice of ell(n)); ``k_rule == "small_scale"`` gives min(max(3, ceil(log2 n)), m - 2, 4).
    alpha
        The alpha of the Extended Design Lemma (Babai Thm. 7.3.3, built here from HBD
        Prop. 5.1 and Thm. 5.3) and of Split-or-Johnson in case 2b.  HBD's statements
        need 1/2 <= alpha < 1 (Design Lemma) and 2/3 <= alpha < 1 (Split-or-Johnson;
        the Extended Design Lemma calls it with alpha m/|C| >= alpha).  Babai states
        Thm. 7.3.3 for 3/4 <= alpha.  The default 2/3 is the smallest value the
        lemmas admit; every alpha-partition shrinks the windows of the recursion
        to at most alpha n points, so it gives the smallest constant b of the time
        bound (PROOF.md).
    soj
        ``SOJParams`` of Split-or-Johnson (see there; the defaults are HBD's constants).
    orbit_prune
        Skip y-branches lying in the orbit of an already processed branch under the
        automorphisms found so far (they only give translates; Babai Prop. 4.0.4).
    """

    def __init__(self, brute_force_order: int = 5040, quotient_enum_limit: Optional[int] = None,
                 min_gamma: Optional[int] = None, local_k: Optional[int] = None, k_rule: str = "paper",
                 alpha=Fraction(2, 3), soj: Optional[SOJParams] = None, orbit_prune: bool = True,
                 cameron_maroti_degree: int = 25, allow_fallbacks: bool = False):
        if k_rule not in ("paper", "small_scale"):
            raise ValueError("k_rule must be 'paper' or 'small_scale'")
        self.brute_force_order = brute_force_order
        self.quotient_enum_limit = quotient_enum_limit
        self.min_gamma = min_gamma
        self.local_k = local_k
        self.k_rule = k_rule
        self.alpha = Fraction(alpha)
        self.soj = soj if soj is not None else SOJParams(allow_fallbacks=allow_fallbacks)
        self.orbit_prune = orbit_prune
        self.cameron_maroti_degree = cameron_maroti_degree
        # exact but expensive fallbacks for situations the papers' theorems exclude
        # (only below the papers' thresholds); under the paper preset they raise
        # TheoremViolation instead (errors.py)
        self.allow_fallbacks = allow_fallbacks
        self.preset = "custom"

    # ------------------------------------------------------------ presets
    @classmethod
    def paper(cls, **overrides) -> "Params":
        """The papers' thresholds (the default of ``Solver``, ``graph_isomorphism``
        and the command line): |Gbar| < m^{1+log2 m} decides enumeration versus
        Johnson identification (Babai Thm. 3.2.3, Reduce-to-Johnson line 5);
        Sym(Gamma) is enumerated for |Gamma| < ell(n) = 10 k_paper(n); the test
        sets of Local Certificates have size k_paper(n) > max{8, 2 + log2 n}
        (Thm. 8.3.5, Thm. 10.1.3); Split-or-Johnson uses the arity d = 2s of
        ``SOJParams.arity`` without caps and without HBD's small-|V2| shortcut
        (``SOJParams``).  At the sizes a
        Python implementation can process these thresholds degenerate to
        enumeration (v! < binom(v,2)^{1+log2 binom(v,2)} for graphs with v < 22
        vertices, and ell(binom(v,2)) > v for v < 160, so Sym(V) is enumerated
        either by line 5 or by the |Gamma| < ell(n) rule), which is what the
        papers prescribe there: the cost is bounded by an absolute constant or by
        ell(n)!.  Feasible in Python up to 8-9 vertices."""
        P = cls(**overrides)
        P.preset = "paper"
        return P

    @classmethod
    def small_scale(cls, **overrides) -> "Params":
        """Small constants: brute force below 5040, quotient enumeration capped at
        20000 (above it the Johnson / product-action identification is tried even
        below the Cameron-Maroti bound, which is correct since the identification
        is verified), Johnson case for |Gamma| >= 8, test sets of size
        min(max(3, ceil(log2 n)), m - 2, 4), ``SOJParams.small_scale()``.  These
        values make every branch of the algorithm execute on inputs that Python
        can process; the papers' theorems (Thm. 8.3.5 in particular) do not apply
        at these sizes, so the fullness of a certificate is verified and, if the
        verification fails, decided exactly on the full window (certificates.py)."""
        kw = dict(brute_force_order=5040, quotient_enum_limit=20000, min_gamma=8, k_rule="small_scale",
                  soj=SOJParams.small_scale(), allow_fallbacks=True)
        kw.update(overrides)
        P = cls(**kw)
        P.preset = "small_scale"
        return P

    def __repr__(self) -> str:
        return (f"Params({self.preset}: C0={self.brute_force_order}, quotient_enum_limit={self.quotient_enum_limit}, "
                f"min_gamma={self.min_gamma}, local_k={self.local_k}, k_rule={self.k_rule}, "
                f"allow_fallbacks={self.allow_fallbacks})")

    # ------------------------------------------------------------- rules
    @staticmethod
    def luks_threshold(m: int) -> int:
        """m^{1 + floor(log2 m)}, an integer at most the Cameron-Maroti bound m^{1+log2 m}
        (Babai Thm. 3.2.3, Reduce-to-Johnson line 5).  A primitive quotient of smaller
        order is enumerated (strong Luks reduction)."""
        return m ** m.bit_length() if m >= 2 else 1

    @staticmethod
    def enumeration_cap(m: int) -> int:
        """m^{2 + floor(log2 m)} > m^{1+log2 m}: an unrecognised primitive quotient of
        smaller order may be enumerated (its order is then below this cap); one of at
        least this order is a Cameron group by Thm. 3.2.3 when m >= 25, hence
        recognised (johnson.py), so an unrecognised one is a TheoremViolation."""
        return m ** (m.bit_length() + 1) if m >= 2 else 1

    def small_quotient(self, order: int, m: int) -> bool:
        """Whether a primitive quotient of degree m and this order is enumerated without
        trying to recognise it."""
        if order < self.luks_threshold(m):
            return self.quotient_enum_limit is None or order <= self.quotient_enum_limit
        return False

    @staticmethod
    def k_paper(n: int) -> int:
        """Smallest integer k with k > max{8, 2 + log2 n} (Babai Thm. 8.3.5 / Thm. 10.1.3):
        max(9, 3 + floor(log2 n)), computed exactly (floor(log2 n) = bit_length - 1)."""
        return max(9, max(n, 1).bit_length() + 2)

    def gamma_threshold(self, n: int) -> int:
        """ell(n): Johnson quotients with |Gamma| < ell(n) are enumerated."""
        if self.min_gamma is not None:
            return self.min_gamma
        return 10 * self.k_paper(n)

    def k_for(self, n: int, m: int) -> int:
        """Test-set size for Local Certificates on |Omega| = n, |Gamma| = m."""
        if self.local_k is not None:
            return max(1, min(self.local_k, m - 2))
        if self.k_rule == "paper":
            # k_paper(n) <= m/10 whenever m >= ell(n); the cap only matters if min_gamma was lowered by hand
            return max(1, min(self.k_paper(n), m - 2))
        k = max(3, int(ceil(log2(max(n, 2)))))
        return max(1, min(k, m - 2, 4))


class Solver:
    def __init__(self, params: Optional[Params] = None):
        # the papers' thresholds are the default; Params.small_scale() for Python-sized inputs
        self.params = params if params is not None else Params.paper()
        self.stats: Counter = Counter()
        self.depth = 0

    # ================================================================ core
    def iso(self, G: PermGroup, x: Sequence, y: Sequence, tower: Optional[Tower] = None) -> Optional[Coset]:
        """ISO_G(x, y) (Babai Def. 3.1.2); Reduce-to-Johnson (Sec. 3.3) + Master Algorithm (Sec. 12).

        ``tower`` is a tower of G-invariant partitions of the domain (``tower.py``);
        the recursion only coarsens above its top level.  It does not influence the
        result, only the path of the recursion (HBD App. A.1)."""
        x, y = tuple(x), tuple(y)
        n = G.n
        if tower is None:
            tower = Tower.trivial(n)
        if tower.n != n:
            raise ValueError("tower on a different domain")
        self.stats["calls"] += 1
        self.depth += 1
        try:
            if len(x) != n or len(y) != n:
                raise ValueError("strings must be indexed by the domain of G")
            # step 1: G <= Aut(x)
            if all(is_string_automorphism(x, g) for g in G.gens):
                return Coset(G, identity(n)) if x == y else None
            if Counter(x) != Counter(y):
                return None
            if x != y:
                # ISO_G(x,y) = Aut_G(x) rho for any isomorphism rho
                rho = self._one_iso(G, x, y, tower)
                if rho is None:
                    return None
                A = self.iso(G, x, x, tower)
                return Coset(A.group, rho)
            A = G.aut_cache.get(x)
            if A is None:
                A = self._solve(G, x, y, tower)
                G.aut_cache[x] = A
            else:
                self.stats["aut_cache_hits"] += 1
            return A
        finally:
            self.depth -= 1

    def _one_iso(self, G: PermGroup, x: tuple, y: tuple, tower: Tower) -> Optional[Perm]:
        """One element of ISO_G(x, y), or None.  (``_solve`` with x != y returns a
        non-empty sub-coset of ISO_G(x, y) when it is non-empty; only its
        representative is used.)"""
        C = self._solve(G, x, y, tower)
        return None if C is None else C.rep

    def _solve(self, G: PermGroup, x: tuple, y: tuple, tower: Tower) -> Optional[Coset]:
        n = G.n
        P = self.params
        if G.order() <= P.brute_force_order:
            return self.brute_force(G, x, y)
        orbits = G.orbits()
        if len(orbits) > 1:
            return self.chain_rule(G, x, y, orbits, tower)
        if n >= 3 and G.order() * 2 >= factorial(n):
            # G = Sym(Omega) or Alt(Omega): the Johnson case with t = 1 and Omega = Gamma
            # (Master Algorithm line 4); exact for every n, so no threshold applies.  A
            # giant is primitive, so its only invariant partition is into singletons.
            assert tower.is_trivial()
            self.stats["johnson_case"] += 1
            self.stats["johnson_t1"] += 1
            return self.trivial_case(GroupWithAction(G, n, list(G.gens), phi_fn=lambda g: g), x, y,
                                     is_sym=(G.order() == factorial(n)))
        hint = getattr(G, "johnson_hint", None)
        if (hint is not None and tower.is_trivial() and hint.m >= P.gamma_threshold(n)
                and not P.small_quotient(G.order(), n)):
            # the caller (the GI -> SI reduction) supplied the Johnson structure of a
            # primitive G; it is used under exactly the conditions of Reduce-to-Johnson
            # lines 5-7 (|G| >= m^{1+floor(log2 m)} on the m = n singleton blocks, |Gamma| >= ell(n))
            jd = G.agg_cache.get("hint_jd")
            if jd is None:
                Gw = GroupWithAction(G, hint.m, hint.phi_gens)
                jd = JohnsonData(Gw, hint.t, [[i] for i in range(n)], hint.T_of_point, tower)
                G.agg_cache["hint_jd"] = jd
            self.stats["johnson_case"] += 1
            self.stats[f"johnson_t{hint.t}"] += 1
            return self.johnson_case(jd, x, y)
        # the top partition of the tower; G is transitive on its blocks
        top = tower.top_blocks()
        if len(top) == n:
            coarse = G.minimal_block_system()
        else:
            Gp, _ = G.induced_action(top)
            sup = Gp.minimal_block_system()          # maximal blocks of the action on the top blocks
            coarse = [sorted(p for bi in grp for p in top[bi]) for grp in sup] if len(sup) < len(top) else top
            coarse.sort()
        if len(coarse) < len(top):
            # the action on the top blocks is imprimitive: append its maximal block system
            tower = tower.extend(coarse)
        blocks = coarse
        m = len(blocks)
        Gbar, imgs = G.induced_action(blocks)
        qorder = Gbar.order()
        if P.small_quotient(qorder, m):
            # Reduce-to-Johnson line 5: |Gbar| < m^{1+floor(log2 m)} (or below the small-scale cap)
            self.stats["luks_small_quotient"] += 1
            return self.strong_luks(G, blocks, imgs, x, y, tower)
        # line 6: Gbar is a Cameron group (Thm. 3.2.3, m >= 25): a Johnson group (s = 1) or a
        # product action S_k^{(t)} wr S_s, s >= 2, reduced to a Johnson group at cost <= s!
        jh = recognize_johnson(Gbar)
        if jh is None:
            cs = recognize_cameron(Gbar)
            if cs is not None:
                self.stats["cameron_product_action"] += 1
                self.stats[f"cameron_t{cs.t}_s{cs.s}"] += 1
                return self.cameron_reduction(G, Gbar, imgs, cs, x, y, tower)
            # Not recognised.  If |Gbar| < m^{2+floor(log2 m)} it is enumerated (the cost of
            # that is of the order of the Luks bound).  Otherwise m < 25 (Thm. 3.2.3: for
            # m >= 25 a primitive group of order >= m^{1+log2 m} is a Cameron group, and
            # johnson.py recognises every Cameron group), and |Gbar| <= 24! is an absolute
            # constant (M_12, M_24 are the only primitive groups of degree < 25 above the bound).
            self.stats["fallback_enumeration"] += 1
            if m >= P.cameron_maroti_degree and qorder >= P.enumeration_cap(m):
                self.stats["fallback_enumeration_unexpected"] += 1
                fallback(P.allow_fallbacks, "primitive quotient of degree >= 25 above the "
                         "Cameron-Maroti bound not recognised (Babai Thm. 3.2.3)")
            return self.strong_luks(G, blocks, imgs, x, y, tower)
        if jh.m < P.gamma_threshold(n):
            # |Gamma| below ell(n): enumerate Sym(Gamma) (Babai Sec. 1.2 / 3.4; the quotient
            # Gbar = S^{(t)}(Gamma) has order |Gamma|! <= ell(n)!, quasipolynomial)
            self.stats["luks_small_gamma"] += 1
            return self.strong_luks(G, blocks, imgs, x, y, tower)
        # phi on every generator of G, read off its block image (johnson.johnson_phi)
        phi_gens = [johnson_phi(img, jh) for img in imgs]
        Gw = GroupWithAction(G, jh.m, phi_gens)
        jd = JohnsonData(Gw, jh.t, [list(b) for b in blocks], jh.T_of_point, tower)
        self.stats["johnson_case"] += 1
        self.stats[f"johnson_t{jh.t}"] += 1
        return self.johnson_case(jd, x, y)

    # ======================================================= Luks machinery
    def brute_force(self, G: PermGroup, x: tuple, y: tuple) -> Optional[Coset]:
        """Exhaustive search in a group of bounded order (Reduce-to-Johnson line 2,
        |G| < C_0).  The elements are enumerated along the stabilizer chain
        (g = h u_0 with u_0 in the transversal of the first base point, h in the
        stabilizer, recursively); a partial product already determines the images
        of the points fixed by the remaining stabilizer, which are checked against
        the target string as soon as they are determined (pruning).  This is still
        an exhaustive search of the whole group, only organised to skip subtrees
        that cannot contain an isomorphism."""
        self.stats["brute_force"] += 1
        A = G.aut_cache.get(x)
        if A is None:
            auts = list(_chain_search(G, x, x))
            A = Coset(PermGroup(G.n, auts, known_order=len(auts)), identity(G.n))
            G.aut_cache[x] = A
        if x == y:
            return A
        for g in _chain_search(G, x, y):
            return Coset(A.group, g)
        return None

    def iso_window(self, H: PermGroup, x: Sequence, y: Sequence, window: Sequence[int],
                   tower: Optional[Tower] = None) -> Optional[Coset]:
        """ISO^Delta_H(x, y) for an H-invariant window Delta (Babai Obs. 3.1.10);
        ``tower`` (H-invariant, on the whole domain) is restricted to the window."""
        window = sorted(window)
        if not window:
            return Coset(H, identity(H.n))
        lifter = window_lifter(H, window)
        xr, yr = lifter.restrict_string(x), lifter.restrict_string(y)
        Hr = lifter.restricted
        if Hr.is_trivial():
            if xr != yr:
                return None
            return Coset(H, identity(H.n))
        sub_tower = (tower if tower is not None else Tower.trivial(H.n)).restrict(lifter.pts)
        C = self.iso(Hr, xr, yr, sub_tower)
        if C is None:
            return None
        return lifter.lift_coset(C)

    def chain_rule(self, G: PermGroup, x: tuple, y: tuple, orbits: Sequence[Sequence[int]],
                   tower: Tower) -> Optional[Coset]:
        """Luks's Chain Rule over the orbits (Babai Prop. 3.1.7).

        The groups Aut^{Delta_1 cup ... cup Delta_i}_G(x) and the window
        lifters depend on x only; they are cached on G so that repeated calls
        with different y (Luks reductions) only pay for finding representatives.
        Each orbit is processed with the tower restricted to it.
        """
        self.stats["chain_rule"] += 1
        n = G.n
        order = sorted(orbits, key=lambda o: (-len(o), min(o)))
        stages = G.stage_cache.get(x)
        if stages is None:
            stages = []
            G.stage_cache[x] = stages
        cur = G
        cur_y = y
        acc = identity(n)
        for i, orb in enumerate(order):
            if i < len(stages):
                lifter, nxt = stages[i]
            else:
                lifter = window_lifter(cur, orb)
                nxt = None
            xr, yr = lifter.restrict_string(x), lifter.restrict_string(cur_y)
            Hr = lifter.restricted
            if Hr.is_trivial():
                if xr != yr:
                    return None
                rep = identity(n)
                group = cur
            else:
                C = self.iso(Hr, xr, yr, tower.restrict(lifter.pts))
                if C is None:
                    return None
                rep = lifter.lift(C.rep)
                group = nxt if nxt is not None else lifter.lift_group(C.group)
            if i >= len(stages):
                stages.append((lifter, group))
            cur = group
            cur_y = act_string(cur_y, inv(rep))
            acc = mul(rep, acc)
        return Coset(cur, acc)

    def strong_luks(self, G: PermGroup, blocks: Sequence[Sequence[int]], imgs: Sequence[Perm], x: tuple, y: tuple,
                    tower: Tower) -> Optional[Coset]:
        """Strong Luks reduction (Babai Thm. 3.1.8): weak reduction to the kernel N
        of the action on the blocks (enumerating the primitive quotient), then the
        Chain Rule over the orbits of N inside the recursive calls."""
        self.stats["strong_luks"] += 1
        n = G.n
        m = len(blocks)
        Gw = GroupWithAction(G, m, imgs)
        N = Gw.kernel()
        comb = Gw.comb_gamma()
        k = Gw._gamma_levels()
        pieces = []
        for r in comb.coset_reps_prefix(k):
            sigma = r[:n]
            y2 = act_string(y, inv(sigma))
            C = self.iso(N, x, y2, tower)
            if C is not None:
                pieces.append((C.group, mul(C.rep, sigma)))
                if x != y:
                    break
        res = generated_subcoset(n, pieces)
        if res is None:
            return None
        return Coset(res[0], res[1])

    def cameron_reduction(self, G: PermGroup, Gbar: PermGroup, imgs: Sequence[Perm], hs, x: tuple, y: tuple,
                          tower: Tower) -> Optional[Coset]:
        """Babai Thm. 3.2.1 / Procedure Reduce-to-Johnson line 6: the primitive
        quotient is a Cameron group with s >= 2 (product action of S_k^{(t)} wr S_s,
        ``hs`` a ``johnson.CameronStructure``); weak Luks reduction over the cosets
        of the kernel N of the action on the s coordinates (multiplicative cost
        <= s! < m, Prop. 3.2.5) to the preimage of N.  Its action on the top blocks of
        the tower is the product action of (A_k^{(t)})^s <= Nbar <= (S_k^{(t)})^s,
        imprimitive with the fibres of a coordinate as blocks, so the recursive call
        appends such a fibre system to the tower and finds the Johnson quotient on it."""
        self.stats["cameron_reduction"] += 1
        n = G.n
        Gw0 = GroupWithAction(G, Gbar.n, imgs)
        Nbar = PermGroup(Gbar.n, hs.N_gens)
        NG = Gw0.preimage(hs.N_gens, image_order=Nbar.order())
        Qw = GroupWithAction(Gbar, hs.s, hs.class_images)
        comb = Qw.comb_gamma()
        k = Qw._gamma_levels()
        pieces = []
        for r in comb.coset_reps_prefix(k):
            sbar = r[:Gbar.n]
            sigma = Gw0.lift(sbar)
            if sigma is None:
                raise RuntimeError("coset representative not liftable")
            y2 = act_string(y, inv(sigma))
            C = self.iso(NG, x, y2, tower)
            if C is not None:
                pieces.append((C.group, mul(C.rep, sigma)))
                if x != y:
                    break
        res = generated_subcoset(n, pieces)
        if res is None:
            return None
        return Coset(res[0], res[1])

    # ============================================================ Johnson
    def johnson_case(self, jd: JohnsonData, x: tuple, y: tuple) -> Optional[Coset]:
        if jd.is_primitive():
            if jd.t == 1:
                return self.trivial_case(jd.Gw, x, y)
            return self.primitive_johnson(jd, x, y)
        return self.imprimitive_johnson(jd, x, y)

    def trivial_case(self, Gw: GroupWithAction, x: tuple, y: tuple, is_sym: Optional[bool] = None) -> Optional[Coset]:
        """G >= Alt(Omega) acting on Omega = Gamma (Babai Sec. 12 line 4; HBD 4.2)."""
        self.stats["trivial_case"] += 1
        n = Gw.n
        if is_sym is None:
            is_sym = Gw.image_is_sym()
        cx: Dict = {}
        cy: Dict = {}
        for u in range(n):
            cx.setdefault(x[u], []).append(u)
            cy.setdefault(y[u], []).append(u)
        if set(cx) != set(cy) or any(len(cx[l]) != len(cy[l]) for l in cx):
            return None
        sigma = [0] * n
        for l in cx:
            for a, b in zip(cx[l], cy[l]):
                sigma[a] = b
        sigma = tuple(sigma)
        gens = []
        for l in cx:
            gens.extend(sym_gens(cx[l], n))
        order = 1
        for l in cx:
            order *= factorial(len(cx[l]))
        if is_sym:
            return Coset(PermGroup(n, gens, known_order=order), sigma)
        # G = Alt(Omega)
        egens = even_subgroup_gens(gens, n)
        has_odd = any(len(v) >= 2 for v in cx.values())
        if parity(sigma) == 1:
            if not has_odd:
                return None
            l = next(l for l in cx if len(cx[l]) >= 2)
            a, b = cy[l][0], cy[l][1]
            tr = from_cycles(n, [[a, b]])
            sigma = mul(sigma, tr)
        return Coset(PermGroup(n, egens, known_order=order // 2 if has_odd else order), sigma)

    # ---------------------------------------------------- hypergraph tools
    def hypergraph_structure(self, jd: JohnsonData, s: tuple, chooser: Chooser) -> KStructure:
        """x viewed as an edge-colored t-uniform hypergraph on Gamma, refined by t-WL."""
        m, t = jd.m, jd.t
        from itertools import product
        raw = []
        letter_index = {a: i for i, a in enumerate(sorted(set(s), key=canon))}
        for tup in product(range(m), repeat=t):
            if len(set(tup)) < t:
                raw.append(-1)
            else:
                raw.append(letter_index[s[jd.block_of_T[frozenset(tup)]]])
        distinct = sorted(set(raw))
        cmap = {c: i for i, c in enumerate(distinct)}
        X0 = KStructure(m, t, [cmap[r] for r in raw], len(distinct))
        chooser.check(("hyp", tuple(raw.count(c) for c in distinct)))
        return refine_structures([X0], chooser.check)[0]

    def hypergraph_twin_classes(self, jd: JohnsonData, s: tuple) -> List[List[int]]:
        """Twin classes of Gamma for the hypergraph (Babai Sec. 2.6.3, Prop. 2.6.4)."""
        m = jd.m
        parent = list(range(m))

        def find(a):
            while parent[a] != a:
                parent[a] = parent[parent[a]]
                a = parent[a]
            return a

        for a in range(m):
            for b in range(a + 1, m):
                if find(a) == find(b):
                    continue
                ok = True
                for T, i in jd.block_of_T.items():
                    if (a in T) != (b in T):
                        T2 = frozenset((b if v == a else (a if v == b else v)) for v in T)
                        if s[i] != s[jd.block_of_T[T2]]:
                            ok = False
                            break
                if ok:
                    parent[find(b)] = find(a)
        groups: Dict[int, List[int]] = {}
        for a in range(m):
            groups.setdefault(find(a), []).append(a)
        return list(groups.values())

    def primitive_johnson(self, jd: JohnsonData, x: tuple, y: tuple) -> Optional[Coset]:
        """Babai Sec. 12 lines 5-7: t >= 2, G primitive on Omega = binom(Gamma, t)."""
        self.stats["primitive_johnson"] += 1
        Gw = jd.Gw
        m = jd.m
        P = self.params

        def largest_twin(s: tuple) -> List[int]:
            return max(self.hypergraph_twin_classes(jd, s), key=lambda c: (len(c), [-v for v in c]))

        Cx = largest_twin(x)
        if 2 * len(Cx) > m:
            self.stats["pullback_twins"] += 1

            def proc(s: tuple, chooser: Chooser) -> Structure:
                C = largest_twin(s)
                chooser.check(("pullback", len(C)))
                return Structure(m, [("twins", frozenset(C)), ("rest", frozenset(set(range(m)) - set(C)))])

            return self.branch(Gw, x, y, proc, [], tower=jd.tower)

        def proc2(s: tuple, chooser: Chooser) -> Structure:
            X = self.hypergraph_structure(jd, s, chooser)
            base = Structure(m, [("all", frozenset(range(m)))])
            return extended_design_lemma(X, base, P.alpha, chooser, P.soj)

        self.stats["edl_primitive"] += 1
        return self.branch(Gw, x, y, proc2, [], tower=jd.tower)

    # ------------------------------------------------------------ branch
    def branch(self, Gw: GroupWithAction, x: tuple, y: tuple, proc: Callable[[tuple, Chooser], Structure],
               known_auts: Sequence[Perm], recurse: Optional[Callable] = None,
               tower: Optional[Tower] = None) -> Optional[Coset]:
        """Reduction at multiplicative cost (Babai Prop. 4.0.4) followed by Align (Sec. 11.1).

        Computes the canonical structure F(x) with the first choices, enumerates
        all choice sequences for y, aligns, reduces G to phi^{-1}(Aut(F(x))) and
        recurses.  For x == y all branches are combined (automorphism group);
        branches whose choice sequence lies in the orbit of an already processed
        one under the known automorphisms are skipped (they give translates).
        """
        n, m = Gw.n, Gw.m
        want_all = (x == y)
        rc = RecordingChooser()
        Sx = proc(x, rc)
        self.stats["branch_calls"] += 1
        aut_gens_gamma = Gw.intersect_image(Sx.aut_gens())
        # |Aut(Sx) cap G^phi|, computed (not read off the structure), so that the order
        # handed to Schreier-Sims for G1 = phi^{-1}(Aut(Sx)) is correct by construction
        image_order = PermGroup(m, aut_gens_gamma).order()
        G1 = Gw.preimage(aut_gens_gamma, image_order=image_order)
        need_even = not Gw.image_is_sym()
        H_gens: List[Perm] = [g for g in known_auts if not is_identity(g)]
        pieces: List[Tuple[PermGroup, Perm]] = []
        if H_gens:
            pieces.append((PermGroup(n, H_gens), identity(n)))
        processed: List[Tuple] = []
        covered: set = set()
        # orbit pruning transports choice sequences by apply_obj; colours chosen to break
        # ties of equal keys (structure.Fixed) have no canonical names and are not
        # transported, so pruning is switched off for such traces
        prune = self.params.orbit_prune and not any(isinstance(c, Fixed) for c in rc.chosen)
        for Sy, chosen in enumerate_runs(lambda ch: proc(y, ch), rc.trace):
            self.stats["branches"] += 1
            key = tuple(chosen)
            if want_all and prune and key in covered:
                self.stats["branches_pruned"] += 1
                continue
            sigma_bar = align(Sx, Sy, need_even)
            if sigma_bar is None:
                self.stats["branches_unaligned"] += 1
                continue
            sigma = Gw.lift(sigma_bar)
            if sigma is None:
                # align returns an element of G^phi (even when G^phi = Alt(Gamma))
                raise RuntimeError("aligning permutation not in the image of phi")
            y1 = act_string(y, inv(sigma))
            if recurse is None:
                sub = self.iso(G1, x, y1, tower)
            else:
                sub = recurse(G1, x, y1)
            if sub is None:
                continue
            piece = (sub.group, mul(sub.rep, sigma))
            if not want_all:
                return Coset(piece[0], piece[1])
            pieces.append(piece)
            processed.append(key)
            H_gens.extend(sub.group.gens)
            H_gens.append(piece[1])
            if prune:
                covered = self._covered(processed, H_gens, Gw)
        if not want_all:
            return None  # no branch produced an isomorphism (the known automorphisms are not one)
        res = generated_subcoset(n, pieces)
        if res is None:
            return None
        return Coset(res[0], res[1])

    def _covered(self, processed: List[Tuple], H_gens: List[Perm], Gw: GroupWithAction, cap: int = 20000) -> set:
        imgs = [Gw.phi(g) for g in H_gens if not is_identity(g)]
        covered = set()
        for key in processed:
            orbit = {key}
            queue = [key]
            while queue and len(orbit) < cap:
                cur = queue.pop()
                for g in imgs:
                    nx = tuple(apply_obj(o, g) for o in cur)
                    if nx not in orbit:
                        orbit.add(nx)
                        queue.append(nx)
            covered |= orbit
        return covered

    # ======================================================== imprimitive
    def imprimitive_johnson(self, jd: JohnsonData, x: tuple, y: tuple) -> Optional[Coset]:
        """Babai Sec. 12 lines 8-12: AggregateCertificates (Thm. 10.2.1) then
        Extended Design Lemma / Align.  HBD Sec. 6.2 Cases 1, 2a, 2b, 3."""
        self.stats["imprimitive_johnson"] += 1
        Gw = jd.Gw
        n, m = Gw.n, Gw.m
        P = self.params
        k = P.k_for(n, m)
        ax = self.aggregate(jd, x, k)
        ay = self.aggregate(jd, y, k) if y != x else ax
        if ax["case"] != ay["case"] or ax["sizes"] != ay["sizes"]:
            return None
        case = ax["case"]
        self.stats[f"agg_case_{case}"] += 1
        if case == "1":
            def proc(s: tuple, chooser: Chooser) -> Structure:
                a = self.aggregate(jd, s, k)
                chooser.check(("agg1", a["sizes"]))
                cells = []
                fixed = set(range(m))
                for orb in a["orbits"]:
                    if len(orb) >= 2:
                        cells.append((("orb", len(orb)), frozenset(orb)))
                        fixed -= set(orb)
                if fixed:
                    cells.append(("fixed", frozenset(fixed)))
                return Structure(m, cells)
            return self.branch(Gw, x, y, proc, ax["F_gens"], tower=jd.tower)
        if case == "2a":
            return self.case_2a(jd, x, y, ax, ay, k)
        if case == "2b":
            def proc(s: tuple, chooser: Chooser) -> Structure:
                a = self.aggregate(jd, s, k)
                return self.case_2b_structure(jd, a, chooser)
            return self.branch(Gw, x, y, proc, ax["F_gens"], tower=jd.tower)
        # case 3
        return self.case_3(jd, x, y, ax, ay, k)

    def aggregate(self, jd: JohnsonData, s: tuple, k: int) -> Dict:
        """Compute all local certificates of s and the data of Thm. 10.2.1."""
        Gw = jd.Gw
        key = ("agg", s, k)
        # cached on the underlying PermGroup: ISO_G(x, y) first computes one
        # isomorphism and then Aut_G(x) in a second pass over the same G
        cache = Gw.G.agg_cache
        if key in cache:
            return cache[key]
        n, m = Gw.n, Gw.m
        lc = LocalCertificates(self, jd, s, k)
        full_sets = []
        F_gens: List[Perm] = []
        F_img: List[Perm] = []
        processed: Dict[FrozenSet[int], None] = {}
        for A in combinations(range(m), k):
            A = frozenset(A)
            # test sets in the orbit of a processed one under the known automorphisms
            # have conjugate certificates (the procedure is canonical)
            found = None
            if F_img:
                seen = {A: identity(n)}
                queue = [A]
                while queue and found is None:
                    cur = queue.pop()
                    for gg, gb in zip(F_gens, F_img):
                        nx_ = frozenset(gb[v] for v in cur)
                        if nx_ not in seen:
                            seen[nx_] = mul(seen[cur], gg)
                            if nx_ in processed:
                                found = (nx_, seen[nx_])
                                break
                            queue.append(nx_)
            if found is not None:
                A0, g = found      # A0 = A^{g} with g in F; cert(A) = cert(A0)^{g^{-1}}
                cert = lc.conjugate(lc.certificate(A0), inv(g), A)
            else:
                cert = lc.certificate(A)
            processed[A] = None
            if cert.full:
                full_sets.append(A)
                new = [g for g in cert.K.gens if not is_identity(g)]
                F_gens.extend(new)
                F_img.extend(Gw.phi(g) for g in new)
        F_gens = list(dict.fromkeys(F_gens))
        Fimg = PermGroup(m, [Gw.phi(g) for g in F_gens])
        orbits = Fimg.orbits()
        support = [v for v in range(m) if any(g[v] != v for g in Fimg.gens)]
        S = frozenset(support)
        big = [orb for orb in orbits if 2 * len(orb) > m]
        if big:
            Phi = sorted(big[0])
            FPhi_gens = [restrict_to(g, Phi) for g in Fimg.gens]
            giant = is_giant_on(len(Phi), FPhi_gens)
            case = "2a" if giant else "2b"
            sizes = (len(S), len(Phi))
        elif 2 * len(S) >= m:
            case = "1"
            Phi = None
            sizes = (len(S), tuple(sorted(len(o) for o in orbits)))
        else:
            case = "3"
            Phi = None
            sizes = (len(S),)
        data = {"lc": lc, "full": full_sets, "F_gens": F_gens, "Fimg": Fimg, "orbits": orbits, "S": S,
                "Phi": Phi, "case": case, "sizes": sizes}
        cache[key] = data
        self.stats[f"agg_computed"] += 1
        return data

    # ----------------------------------------------------------- case 2a
    def case_2a(self, jd: JohnsonData, x: tuple, y: tuple, ax: Dict, ay: Dict, k: int) -> Optional[Coset]:
        """F^Phi >= Alt(Phi): large symmetry; pullback via Cor. 9.0.9 / HBD 6.2 Case 2a."""
        self.stats["case_2a"] += 1
        Gw = jd.Gw
        m = Gw.m

        def proc(s: tuple, chooser: Chooser) -> Structure:
            a = self.aggregate(jd, s, k)
            Phi = a["Phi"]
            chooser.check(("2a", len(Phi)))
            return Structure(m, [("Phi", frozenset(Phi)), ("rest", frozenset(set(range(m)) - set(Phi)))])

        Phi = ax["Phi"]
        F_gens = ax["F_gens"]

        def recurse(G1: PermGroup, x1: tuple, y1: tuple) -> Optional[Coset]:
            return self.top_action(jd, G1, Phi, F_gens, x1, y1)

        return self.branch(Gw, x, y, proc, F_gens, recurse, tower=jd.tower)

    def top_action(self, jd: JohnsonData, G1: PermGroup, Phi: List[int], F_gens: Sequence[Perm], x: tuple, y: tuple) -> Optional[Coset]:
        """Babai Sec. 9 (TopAction1-4): ISO_{G1}(x, y) when Aut_{G1}(x) is known to
        map onto a giant on Phi (witnessed by F).  Window Omega(Phi) first (Cor. 9.0.6/9.0.8),
        then the Chain Rule on the remaining windows (Cor. 9.0.9)."""
        self.stats["top_action"] += 1
        Gw = jd.Gw
        n = Gw.n
        Phi = list(Phi)
        G1w = Gw.subgroup(G1.gens, known_order=G1.known_order_or_none())
        phiPhi = [restrict_to(p, Phi) for p in G1w.phi_gens]
        phi_on_phi = (lambda g: restrict_to(Gw.phi(g), Phi)) if Gw.phi_fn is not None else None
        Gp = GroupWithAction(G1, len(Phi), phiPhi, phi_fn=phi_on_phi)
        K = Gp.kernel()
        window = sorted(jd.omega_of(frozenset(Phi)))
        # F with its action on Phi (its generators are automorphisms of x in G1)
        Fgroup = PermGroup(n, [g for g in F_gens if not is_identity(g)])
        Fw = GroupWithAction(Fgroup, len(Phi), [restrict_to(Gw.phi(g), Phi) for g in Fgroup.gens],
                             phi_fn=phi_on_phi)
        pieces: List[Tuple[PermGroup, Perm]] = []
        for a in alt_gens(list(range(len(Phi))), len(Phi)):
            l = Fw.lift(a)
            if l is None:
                raise RuntimeError("F does not act as a giant on Phi")
            pieces.append((PermGroup(n, []), l))
        CK = self.iso_window(K, x, x, window, jd.tower)
        assert CK is not None
        pieces.append((CK.group, identity(n)))
        sym_on_phi = Gp.image_is_sym()
        F_is_sym = Fw.image_order() == factorial(len(Phi))
        sigma_odd = None
        if F_is_sym:
            # F itself contains automorphisms with odd image on Phi: add one of
            # them, so that <pieces> = Aut^{Omega(Phi)}_{G1}(x) also covers the
            # odd coset (F^Phi = Sym(Phi) and F <= Aut_G(x)).
            l = Fw.lift(from_cycles(len(Phi), [[0, 1]]))
            if l is None:
                raise RuntimeError("F^Phi = Sym(Phi) but no odd element lifts")
            pieces.append((PermGroup(n, []), l))
        elif sym_on_phi:
            sigma_odd = Gp.lift(from_cycles(len(Phi), [[0, 1]]))
            Codd = self.iso_window(K, x, act_string(x, inv(sigma_odd)), window, jd.tower)
            if Codd is not None:
                pieces.append((Codd.group, mul(Codd.rep, sigma_odd)))
        res = generated_subcoset(n, pieces)
        Aut_top = res[0]
        # one isomorphism on the window
        if x == y:
            rho = identity(n)
        else:
            C0 = self.iso_window(K, x, y, window, jd.tower)
            if C0 is not None:
                rho = C0.rep
            elif sym_on_phi:
                if sigma_odd is None:
                    sigma_odd = Gp.lift(from_cycles(len(Phi), [[0, 1]]))
                C1 = self.iso_window(K, x, act_string(y, inv(sigma_odd)), window, jd.tower)
                if C1 is None:
                    return None
                rho = mul(C1.rep, sigma_odd)
            else:
                return None
        # remaining windows with the reduced group
        rest = [u for u in range(n) if u not in set(window)]
        y2 = act_string(y, inv(rho))
        Crest = self.iso_window(Aut_top, x, y2, rest, jd.tower)
        if Crest is None:
            return None
        return Coset(Crest.group, mul(Crest.rep, rho))

    # ----------------------------------------------------------- case 2b
    def case_2b_structure(self, jd: JohnsonData, a: Dict, chooser: Chooser) -> Structure:
        """F^Phi transitive but not a giant (HBD 6.2 Case 2b; Babai 10.2 2b2):
        individualize points until the stabilizer is not doubly transitive, then
        use the orbital configuration (a Schurian coherent configuration):
        imprimitive -> components; uniprimitive -> Split-or-Johnson."""
        self.stats["case_2b"] += 1
        m = jd.m
        Phi = list(a["Phi"])
        chooser.check(("2b", len(Phi)))
        base = Structure(m, [("Phi", frozenset(Phi)), ("rest", frozenset(set(range(m)) - set(Phi)))])
        Fimg: PermGroup = a["Fimg"]
        H = PermGroup(len(Phi), [restrict_to(g, Phi) for g in Fimg.gens])
        pts = list(Phi)  # current point set (as Gamma vertices), H acts on positions of pts
        step = 0
        while True:
            np_ = len(pts)
            orbs = orbitals(H)
            two_trans = (len(orbs) == 1)
            giant = H.order() * 2 >= factorial(np_)
            chooser.check(("2b-step", step, np_, len(orbs), giant))
            if not two_trans or np_ <= 2:
                break
            if giant:
                break
            v = chooser.choose(sorted(pts))
            base = base.individualize(v, ("2b-ind", step))
            vi = pts.index(v)
            Hv = H.point_stabilizer(vi)
            new_pts = [p for p in pts if p != v]
            H = PermGroup(len(new_pts), [restrict_to(g, [pts.index(p) for p in new_pts]) for g in Hv.gens])
            pts = new_pts
            step += 1
        if len(orbs) <= 1:
            # unreachable under the paper's thresholds (CORRECTNESS.md, case 2b)
            fallback(self.params.allow_fallbacks, "case 2b: stabiliser still doubly transitive")
            return individualize_until(base, pts, self.params.alpha * len(pts), chooser, "2b-fb")
        color_of = {}
        for ci, orb in enumerate(orbs):
            for (u, v) in orb:
                color_of[(u, v)] = ci + 1
        cc = ClassicalCC(list(range(len(pts))), lambda u, v: 0 if u == v else color_of[(u, v)])
        cc.canonical_keys()
        disc = cc.disconnected_off_diagonal_colors()
        chooser.check(("2b-disc", len(disc)))
        if disc:
            col = select_min(disc, cc.key, chooser)
            comps = cc.components(col)
            blocks = [[pts[i] for i in cmp] for cmp in comps]
            return split_by_blocks(base, pts, blocks, "2b-comp")
        # uniprimitive: relabel vertices to Gamma and run UPCC Split-or-Johnson
        ccg = ClassicalCC(pts, lambda u, v: 0 if u == v else color_of[(pts.index(u), pts.index(v))])
        ccg.set_keys(cc._keys)
        return upcc_split_or_johnson(ccg, self.params.alpha, base, chooser, self.params.soj)

    # ------------------------------------------------------------ case 3
    def case_3(self, jd: JohnsonData, x: tuple, y: tuple, ax: Dict, ay: Dict, k: int) -> Optional[Coset]:
        """|S| < m/2: canonical k-ary relation on Gamma \\ S from the comparison of
        local certificates (Babai Thm. 10.2.1 item 2c / Prop. 6.2.3 "local guide";
        HBD 6.2 Case 3), then Extended Design Lemma."""
        self.stats["case_3"] += 1
        Gw = jd.Gw
        m = Gw.m
        P = self.params
        lcx: LocalCertificates = ax["lc"]
        lcy: LocalCertificates = ay["lc"]
        Sx, Sy = ax["S"], ay["S"]
        strings = [("x", x, lcx, Sx)]
        if y != x:
            strings.append(("y", y, lcy, Sy))
        # equivalence classes of (string, A) under Prop. 10.1.11, with representatives
        classes: List[Tuple[str, FrozenSet[int]]] = []
        class_of: Dict[Tuple[str, FrozenSet[int]], Tuple[int, Perm]] = {}
        buckets: Dict[Tuple, List[int]] = {}
        for name, s, lc, S in strings:
            rest = sorted(v for v in range(m) if v not in S)
            for A in combinations(rest, k):
                A = frozenset(A)
                cert = lc.certificate(A)
                found = None
                for ci in buckets.get(cert.invariant, []):
                    name0, A0 = classes[ci]
                    lc0 = lcx if name0 == "x" else lcy
                    cert0 = lc0.certificate(A0)
                    Q = lc0.compare(cert0, lc, cert)
                    self.stats["cert_compare"] += 1
                    if Q is not None:
                        found = (ci, Q.rep)
                        break
                if found is None:
                    ci = len(classes)
                    classes.append((name, A))
                    buckets.setdefault(cert.invariant, []).append(ci)
                    found = (ci, identity(Gw.n))
                class_of[(name, A)] = found
        self.stats["cert_classes"] = len(classes)
        # k-ary colorings
        colorings: Dict[str, Dict[Tuple[int, ...], Hashable]] = {}
        for name, s, lc, S in strings:
            col: Dict[Tuple[int, ...], Hashable] = {}
            rest = sorted(v for v in range(m) if v not in S)
            for A in combinations(rest, k):
                A = frozenset(A)
                ci, pi = class_of[(name, A)]
                name0, A0 = classes[ci]
                lc0 = lcx if name0 == "x" else lcy
                cert0 = lc0.certificate(A0)
                pibar_inv = inv(Gw.phi(pi))
                for T in permutations(sorted(A), k):
                    T0 = tuple(pibar_inv[v] for v in T)
                    col[T] = ("c", ci, lc0.ordered_label(cert0, T0))
            colorings[name] = col
        from itertools import product

        def proc(s: tuple, chooser: Chooser) -> Structure:
            name = "x" if s == x else "y"
            S = Sx if name == "x" else Sy
            col = colorings[name]
            raw = []
            for tup in product(range(m), repeat=k):
                raw.append(col.get(tup, ("other",)))
            keys = sorted(set(raw), key=canon)
            idx = {kk: i for i, kk in enumerate(keys)}
            X0 = KStructure(m, k, [idx[r] for r in raw], len(keys))
            chooser.check(("case3", len(S), tuple(raw.count(kk) for kk in keys)))
            X = refine_structures([X0], chooser.check)[0]
            base = Structure(m, [("S", frozenset(S)), ("rest", frozenset(set(range(m)) - S))])
            return extended_design_lemma(X, base, P.alpha, chooser, P.soj, vertices=sorted(set(range(m)) - S))

        return self.branch(Gw, x, y, proc, ax["F_gens"], tower=jd.tower)


def _chain_search(G: PermGroup, x: tuple, y: tuple):
    """All g in G with x^g = y, enumerated along the stabilizer chain with pruning.

    g = h u_0 (u_0 in the transversal of level 0, h in the point stabilizer),
    recursively; after u_0, ..., u_i are chosen the images of all points fixed
    by the remaining stabilizer G^{(i+1)} are determined and are checked at once.
    """
    levels = G.levels
    n = G.n
    k = len(levels)
    # fixed[i] = points fixed by G^{(i)} (the group of level i); fixed[k] = everything
    fixed: List[set] = []
    for i in range(k):
        f = set(range(n))
        for g in levels[i].gens:
            f = {p for p in f if g[p] == p}
        fixed.append(f)
    fixed.append(set(range(n)))
    for p in fixed[0]:
        if x[p] != y[p]:
            return
    new_fixed = [sorted(fixed[i + 1] - fixed[i]) for i in range(k)]

    def rec(i: int, P: Perm):
        if i == k:
            yield P
            return
        checks = new_fixed[i]
        for u in levels[i].trans.values():
            Pn = tuple(P[u[p]] for p in range(n))  # u then P
            ok = True
            for p in checks:
                if y[Pn[p]] != x[p]:
                    ok = False
                    break
            if ok:
                yield from rec(i + 1, Pn)

    yield from rec(0, identity(n))


def string_isomorphism(G: PermGroup, x: Sequence, y: Sequence, params: Optional[Params] = None,
                       solver: Optional[Solver] = None) -> Optional[Coset]:
    """ISO_G(x, y): the set of G-isomorphisms of the strings x, y (Babai Thm. 1.1.1).

    The letters may be arbitrary hashable values; they are first re-encoded as
    integers by one bijection applied to both strings (``canon.normalize_letters``),
    which does not change ISO_G(x, y)."""
    if solver is None:
        solver = Solver(params)
    x, y = normalize_letters(tuple(x), tuple(y))
    return solver.iso(G, x, y)
