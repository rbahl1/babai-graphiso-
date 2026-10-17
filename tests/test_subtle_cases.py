"""Tests of the points where the papers' procedures are easy to implement incorrectly.

* phi (the action of G on Gamma in the Johnson case) is computed from the block
  permutation of each generator (``johnson.johnson_phi``), so it is a homomorphism also
  when the quotient group keeps only some of its generators.
* the orbital configuration of case 2b carries colours whose canonical keys tie; UPCC
  Split-or-Johnson splits tied colours into their colour classes, as interchangeable
  blocks, so the runs cover all isomorphisms (Paley tournaments, cyclic schemes).
* bipartite Split-or-Johnson computes twin classes in the coloured graph, so no twin
  class meets two cells.
* letters are compared by value (1 and True, equal frozensets), not by ``repr``.
* the tower of block systems (``tower.py``), the fallback gates, the half split of
  Bipartite Split-or-Johnson under the paper parameters, and the exact integer root.
"""

import itertools
from fractions import Fraction
import random

import pytest

from babai_gi.canon import canon, normalize_letters
from babai_gi.cc import ClassicalCC
from babai_gi.errors import TheoremViolation, fallback
from babai_gi.group import PermGroup
from babai_gi.johnson import orbitals
from babai_gi.main import Params, Solver, string_isomorphism
from babai_gi.perm import act_string, from_cycles, maps_string, mul
from babai_gi.soj import SOJParams, bipartite_split_or_johnson, upcc_split_or_johnson
from babai_gi.structure import RecordingChooser, Structure, enumerate_runs
from babai_gi.tower import Tower


def _brute_aut_order(G, x):
    return sum(1 for g in G.elements() if maps_string(x, x, g))


# ------------------------------------------------------- phi is a homomorphism

def _pairs_group(variant):
    """S_8 x C_2 on 16 points (8 blocks {2i, 2i+1}) given by 8 generators, so that the
    quotient on the blocks drops some generator images."""
    n = 16

    def block_swap(i, j):
        p = list(range(n))
        p[2 * i], p[2 * j] = 2 * j, 2 * i
        p[2 * i + 1], p[2 * j + 1] = 2 * j + 1, 2 * i + 1
        return tuple(p)

    flip_all = tuple(v ^ 1 for v in range(n))
    if variant == 0:
        gens = [block_swap(i, i + 1) for i in range(7)] + [mul(block_swap(0, 2), flip_all)]
    else:
        gens = [block_swap(0, i) for i in range(1, 8)] + [mul(block_swap(3, 5), flip_all)]
    return PermGroup(n, gens)


@pytest.mark.parametrize("variant", [0, 1])
def test_phi_homomorphism_pairs_group(variant):
    G = _pairs_group(variant)
    assert G.order() == 2 * 40320
    rng = random.Random(variant)
    strings = [tuple([0] * 8 + [1] * 8), (0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1)]
    strings += [tuple(rng.randrange(2) for _ in range(16)) for _ in range(4)]
    elements = list(G.elements())
    for x in strings:
        A = Solver(Params.small_scale()).iso(G, x, x)
        assert A.order() == _brute_aut_order(G, x)
        for g in A.group.gens:
            assert maps_string(x, x, g)
        g = elements[rng.randrange(len(elements))]
        y = act_string(x, g)
        C = Solver(Params.small_scale()).iso(G, x, y)
        assert C is not None and maps_string(x, y, C.rep) and G.contains(C.rep)
        assert C.order() == A.order()


# ------------------------------------------- tied orbital keys (Paley tournament)

def _paley_cc(p, labels, shuffle_seed):
    """The orbital configuration of {v -> a v + b : a a nonzero square mod p} on the
    points labels[0..p-1], with the colour names in a random order (as in case 2b)."""
    g = next(a for a in range(2, p) if len({pow(a, k, p) for k in range(1, p)}) == p - 1)
    inv = {labels[v]: v for v in range(p)}
    shift = tuple(labels[(inv[i] + 1) % p] for i in range(p))
    mult = tuple(labels[(inv[i] * g * g) % p] for i in range(p))
    orbs = orbitals(PermGroup(p, [shift, mult]))
    random.Random(shuffle_seed).shuffle(orbs)
    color_of = {e: ci + 1 for ci, orb in enumerate(orbs) for e in orb}
    pts = list(range(p))
    cc = ClassicalCC(pts, lambda u, v: 0 if u == v else color_of[(u, v)])
    keys = cc.canonical_keys()
    ccg = ClassicalCC(pts, lambda u, v: 0 if u == v else color_of[(u, v)])
    ccg.set_keys(keys)
    return ccg


@pytest.mark.parametrize("p,seed", [(11, 0), (11, 1), (19, 2)])
def test_upcc_tied_keys_cover_all_isomorphisms(p, seed):
    """Babai Prop. 4.0.4: for every isomorphism pi : x -> y some run on y must produce
    the pi-image of the structure produced on x.  The isomorphisms are v -> pi0(a v + b),
    a != 0 (squares and non-squares; the non-squares swap the two tied orbitals)."""
    rng = random.Random(seed)
    params = SOJParams()
    ccx = _paley_cc(p, list(range(p)), 1)
    rc = RecordingChooser()
    Sx = upcc_split_or_johnson(ccx, 0.75, Structure(p, [("all", frozenset(range(p)))]), rc, params)
    pi0 = list(range(p))
    rng.shuffle(pi0)
    ccy = _paley_cc(p, pi0, 7)
    isos = [tuple(pi0[(a * v + b) % p] for v in range(p)) for a in range(1, p) for b in range(p)]
    found = set()
    for Sy, _ in enumerate_runs(lambda ch: upcc_split_or_johnson(
            ccy, 0.75, Structure(p, [("all", frozenset(range(p)))]), ch, params), rc.trace):
        cy = {(k, c) for k, c in Sy.cells}
        for i, pi in enumerate(isos):
            if {(k, frozenset(pi[v] for v in c)) for k, c in Sx.cells} == cy:
                found.add(i)
    assert len(found) == len(isos) == p * (p - 1)


def _cyclic_cc(p, labels, shuffle_seed):
    """The orbital configuration of the regular cyclic group of prime order p (all p - 1
    non-diagonal colours have valency 1 and tied keys), colour names in random order."""
    inv = {labels[v]: v for v in range(p)}
    shift = tuple(labels[(inv[i] + 1) % p] for i in range(p))
    orbs = orbitals(PermGroup(p, [shift]))
    random.Random(shuffle_seed).shuffle(orbs)
    color_of = {e: ci + 1 for ci, orb in enumerate(orbs) for e in orb}
    pts = list(range(p))
    cc = ClassicalCC(pts, lambda u, v: 0 if u == v else color_of[(u, v)])
    keys = cc.canonical_keys()
    ccg = ClassicalCC(pts, lambda u, v: 0 if u == v else color_of[(u, v)])
    ccg.set_keys(keys)
    return ccg


@pytest.mark.parametrize("p,seed", [(7, 0), (13, 1), (47, 2)])
def test_upcc_cyclic_scheme_is_discrete_and_canonical(p, seed):
    """Case 2b with H = C_p: the tied colours have valency 1.  The output must be
    discrete on V (a class of p - 1 interchangeable singletons is not a coloured
    2/3-partition), and the runs on y must produce the image of the x-structure under
    every isomorphism v -> pi0(a v + b) of the configurations up to colour names."""
    rng = random.Random(seed)
    params = SOJParams()
    m = p + 3
    base = Structure(m, [("Phi", frozenset(range(p))), ("rest", frozenset(range(p, m)))])
    ccx = _cyclic_cc(p, list(range(p)), 1)
    rc = RecordingChooser()
    Sx = upcc_split_or_johnson(ccx, Fraction(2, 3), base, rc, params)
    assert all(len(c) == 1 for _, c in Sx.cells if c <= frozenset(range(p)))
    pi0 = list(range(p))
    rng.shuffle(pi0)
    ccy = _cyclic_cc(p, pi0, 7)
    isos = [tuple(pi0[(a * v + b) % p] for v in range(p)) + tuple(range(p, m))
            for a in range(1, p) for b in range(p)]
    found = set()
    runs = 0
    for Sy, _ in enumerate_runs(lambda ch: upcc_split_or_johnson(ccy, Fraction(2, 3), base, ch, params), rc.trace):
        runs += 1
        cy = {(k, c) for k, c in Sy.cells}
        for i, pi in enumerate(isos):
            if {(k, frozenset(pi[v] for v in c)) for k, c in Sx.cells} == cy:
                found.add(i)
    assert runs == p * (p - 1)
    assert len(found) == len(isos)


# ------------------------------------------------ twin classes in the coloured graph

def _twin_instance(relabel):
    n1, n2 = 300, 210
    V1, V2 = list(range(n1)), list(range(n1, n1 + n2))
    rnd = random.Random(1)
    # twin classes {i, 10 + i} (i < 10) meet both cells B = {0..9} and A = {10..299}
    classes = [[i, 10 + i] for i in range(10)]
    rest = list(range(20, n1))
    classes += [[rest[j], rest[j + 1]] for j in range(0, len(rest), 2)]
    adj, seen = {}, set()
    for cl in classes:
        while True:
            nb = frozenset(rnd.sample(V2, 20))
            if nb not in seen:
                seen.add(nb)
                break
        for v in cl:
            adj[v] = nb
    perm = list(range(n1 + n2))
    if relabel:
        for i in range(10):
            perm[i], perm[10 + i] = 10 + i, i
    adj = {perm[v]: adj[v] for v in V1}
    base = Structure(n1 + n2, [("B", frozenset(perm[v] for v in range(10))),
                               ("A", frozenset(perm[v] for v in range(10, n1))), ("V2", frozenset(V2))])
    return V1, V2, adj, base


def test_bipartite_twins_respect_the_colouring():
    """Twin classes are computed in the coloured graph: the outcome does not depend on
    which end of a twin pair has the smaller label."""
    outcomes = []
    for relabel in (False, True):
        V1, V2, adj, base = _twin_instance(relabel)
        S = bipartite_split_or_johnson(V1, V2, adj, 0.75, base, RecordingChooser(), SOJParams())
        V1s = set(V1)
        cells = [c for _, c in S.cells if c <= V1s]
        assert max(len(c) for c in cells) <= 0.75 * len(V1)
        outcomes.append(sorted(len(c) for c in cells))
    assert outcomes[0] == outcomes[1]


# ------------------------------------------------------------ letters by value

def test_letters_compared_by_value():
    G = PermGroup(3, [from_cycles(3, [[0, 1]]), from_cycles(3, [[0, 1, 2]])])
    a, b = frozenset([0, 8]), frozenset([8, 0])
    A = Solver().iso(G, (1, 0, 0), (True, 0, 0))
    assert A is not None and A.order() == 2
    C = Solver().iso(G, (a, 1, 1), (1, b, 1))
    assert C is not None and C.order() == 2 and maps_string((a, 1, 1), (1, b, 1), C.rep)
    assert Solver().iso(G, (a, 1, 1), (1, 1, frozenset([0, 9]))) is None
    assert canon(1) == canon(True) and canon(a) == canon(b)
    assert canon((1, "a")) != canon((1, "b")) and canon([1]) != canon((1,))
    with pytest.raises(TypeError):
        canon(object())
    nx_, ny_ = normalize_letters((a, 1, "s"), ("s", b, True))
    assert sorted(nx_) == sorted(ny_) and nx_[0] == ny_[1] and nx_[1] == ny_[2] and nx_[2] == ny_[0]


def test_string_isomorphism_mixed_letters():
    n = 6
    G = PermGroup(n, [from_cycles(n, [[0, 1]]), from_cycles(n, [list(range(n))])])
    x = (frozenset([1, 2]), 0, "a", (0, 1), 0, True)
    rng = random.Random(3)
    for _ in range(5):
        p = list(range(n))
        rng.shuffle(p)
        y = act_string(x, tuple(p))
        C = string_isomorphism(G, x, y)
        assert C is not None and maps_string(x, y, C.rep)
        assert C.order() == _brute_aut_order(G, x)


# -------------------------------------------------------------------- fallbacks

def test_fallbacks_are_gated():
    assert Params.paper().allow_fallbacks is False and Params.paper().soj.allow_fallbacks is False
    assert Params.small_scale().allow_fallbacks is True and Params.small_scale().soj.allow_fallbacks is True
    fallback(True, "allowed")
    with pytest.raises(TheoremViolation):
        fallback(False, "excluded")


# ------------------------------------------------------------------------ tower

def _f(r):
    return 2 * (r.bit_length() - 1) - 1


def test_potential_drops_when_a_level_is_split():
    """f(ab) >= f(a) + f(b) + 1 for a, b >= 2: inserting a level strictly decreases rho."""
    for a in range(2, 65):
        for b in range(2, 65):
            assert _f(a * b) >= _f(a) + _f(b) + 1


def _towers(n):
    """Towers of the divisor chains of n, as consecutive-interval partitions."""
    def chains(d):
        yield [d]
        for e in range(d + 1, n + 1):
            if n % e == 0 and e % d == 0:
                for rest in chains(e):
                    yield [d] + rest
    for ch in chains(1):
        sizes = [s for s in ch if 1 < s < n]
        yield Tower(n, [tuple(p // s for p in range(n)) for s in sizes]), sizes


def test_tower_potential_bound_and_restriction():
    for n in (8, 12, 16, 24, 36, 64):
        for T, sizes in _towers(n):
            rho = T.potential()
            assert 0 <= rho <= 2 * (n.bit_length() - 1)
            assert T.block_counts() == [n] + [n // s for s in sizes]
            if sizes:
                # restriction to a block of the top level, and to a union of two such blocks
                top = T.top_blocks()
                for window in (top[0], top[0] + top[1]):
                    R = T.restrict(window)
                    assert R.n == len(window) and R.potential() <= rho
                # adding a level strictly between two levels decreases rho
            full = [1] + sizes + [n]
            for lo, hi in zip(full, full[1:]):
                for mid in range(lo + 1, hi):
                    if hi % mid == 0 and mid % lo == 0:
                        new = sorted(sizes + [mid])
                        T2 = Tower(n, [tuple(p // s for p in range(n)) for s in new])
                        assert T2.potential() < rho


def test_tower_extend_and_trivial():
    T = Tower.trivial(9)
    assert T.is_trivial() and T.top_blocks() == [[i] for i in range(9)] and T.potential() == 5
    T2 = T.extend([[0, 1, 2], [3, 4, 5], [6, 7, 8]])
    assert T2.block_counts() == [9, 3] and T2.potential() == 2
    assert T2.top_blocks() == [[0, 1, 2], [3, 4, 5], [6, 7, 8]]
    assert T2.restrict([0, 1, 2]).is_trivial()
    R = T2.restrict([0, 1, 3, 4])
    assert R.block_counts() == [4, 2] and R.levels == ((0, 0, 1, 1),)


def _wreath(H, s):
    """H wr S_s in imprimitive action on s blocks of size deg(H)."""
    k = H.n
    n = k * s
    gens = [tuple(list(h) + list(range(k, n))) for h in H.gens]
    gens.append(tuple((p + k) % n for p in range(n)))
    gens.append(tuple([k + i for i in range(k)] + [i for i in range(k)] + list(range(2 * k, n))))
    return PermGroup(n, gens)


def _sym(k):
    return PermGroup(k, [from_cycles(k, [[0, 1]]), from_cycles(k, [list(range(k))])])


def test_imprimitive_groups_with_tower():
    """Imprimitive groups of order above the brute-force threshold, with two and three
    levels of blocks (the recursion appends levels to the tower)."""
    groups = [_wreath(_sym(3), 4), _wreath(_sym(2), 6), _wreath(_wreath(_sym(2), 2), 4)]
    for G in groups:
        assert G.order() > Params.small_scale().brute_force_order
        rng = random.Random(G.n)
        elements = list(G.elements())
        for _ in range(3):
            x = tuple(rng.randrange(3) for _ in range(G.n))
            A = Solver(Params.small_scale()).iso(G, x, x)
            assert A.order() == sum(1 for g in elements if maps_string(x, x, g))
            y = act_string(x, elements[rng.randrange(len(elements))])
            C = Solver(Params.small_scale()).iso(G, x, y)
            assert C is not None and maps_string(x, y, C.rep)


# ------------------------------------- Split-or-Johnson with the paper parameters

def test_bipartite_soj_paper_parameters_half_split():
    """V1 = all 3-subsets of a 6-set: complete hypergraph with |V2| = 2 d1.  With the
    small-|V2| step disabled (paper default) this is the half split: one point of V2
    is chosen and V1 splits into the two halves of 10 subsets."""
    from babai_gi import soj
    V2 = [100 + i for i in range(6)]
    triples = list(itertools.combinations(V2, 3))
    V1 = list(range(20))
    adj = {v: frozenset(triples[v]) for v in V1}
    base = Structure(106, [("V1", frozenset(V1)), ("V2", frozenset(V2)), ("rest", frozenset(range(20, 100)))])
    soj.STATS.clear()
    ch = RecordingChooser()
    S = bipartite_split_or_johnson(V1, V2, adj, 0.75, base, ch, SOJParams())
    assert soj.STATS["bipartite_soj_half_split"] == 1 and soj.STATS["bipartite_soj_small_v2"] == 0
    assert sorted(len(c) for _, c in S.cells if c <= set(V1)) == [10, 10]
    runs = list(enumerate_runs(lambda c: bipartite_split_or_johnson(V1, V2, adj, 0.75, base, c, SOJParams()),
                               ch.trace))
    assert len(runs) == 6                      # one run per point of V2


def test_bipartite_soj_paper_parameters_random_instances():
    """Twin-free random bipartite graphs with the paper parameters (no small-|V2| step,
    arity d = d1 or 2s): the output is a beta-partition of V1 or a Johnson scheme, and
    it is canonical relative to the choices (some run on a relabelled copy aligns)."""
    from babai_gi import soj
    from babai_gi.structure import align
    for seed, (n1, n2, r) in enumerate([(14, 6, 3), (24, 8, 3), (30, 9, 4)]):
        rng = random.Random(10 + seed)
        V2 = [200 + i for i in range(n2)]
        V1 = list(range(n1))
        chosen = rng.sample(list(itertools.combinations(V2, r)), n1)
        adj = {v: frozenset(chosen[v]) for v in V1}
        base = Structure(200 + n2, [("V1", frozenset(V1)), ("V2", frozenset(V2)),
                                    ("rest", frozenset(range(n1, 200)))])
        soj.STATS.clear()
        ch = RecordingChooser()
        S = bipartite_split_or_johnson(V1, V2, adj, 0.75, base, ch, SOJParams())
        assert soj.STATS["bipartite_soj_small_v2"] == 0
        cells = [c for _, c in S.cells if c <= set(V1)]
        assert S.johnson is not None or max(len(c) for c in cells) <= 0.75 * n1
        perm = list(range(200 + n2))
        p1, p2 = V1[:], V2[:]
        rng.shuffle(p1)
        rng.shuffle(p2)
        for v, w in zip(V1 + V2, p1 + p2):
            perm[v] = w
        adj2 = {perm[v]: frozenset(perm[w] for w in adj[v]) for v in V1}
        base2 = Structure(200 + n2, [("V1", frozenset(V1)), ("V2", frozenset(V2)),
                                     ("rest", frozenset(range(n1, 200)))])
        found = False
        for S2, _ in enumerate_runs(lambda c: bipartite_split_or_johnson(V1, V2, adj2, 0.75, base2, c, SOJParams()),
                                    ch.trace):
            sigma = align(S, S2, False)
            if sigma is not None:
                key2 = S2.key_of_vertex()
                assert all({key2[sigma[v]] for v in c} == {k} for k, c in S.cells)
                found = True
                break
        assert found


# ------------------------------------------------ exact integer thresholds

def test_iroot_exact():
    from babai_gi.johnson import iroot
    rng = random.Random(5)
    for _ in range(300):
        s = rng.randint(1, 12)
        N = rng.randint(0, 1 << rng.randint(1, 3000))
        r = iroot(N, s)
        assert r ** s <= N < (r + 1) ** s
    for c in (3, 2 ** 60 + 7, 3 ** 200):
        for s in (2, 3, 7):
            assert iroot(c ** s, s) == c and iroot(c ** s - 1, s) == c - 1


def test_cameron_candidates_huge_degree():
    """N >= 2^1024, where a floating-point s-th root would overflow."""
    from babai_gi.johnson import _cameron_candidates
    c = 2 ** 300 + 1
    out = _cameron_candidates(c ** 4, (1,))
    assert (c, 1, 4, c) in out
    assert all(cc ** s == c ** 4 for _, _, s, cc in out)
