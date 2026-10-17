"""Tests of the permutation-group machinery against known group orders."""

import itertools
from math import factorial

import pytest

from babai_gi.perm import from_cycles, identity, mul, inv, parity, act_string
from babai_gi.group import PermGroup, even_subgroup_gens
from babai_gi.action import GroupWithAction, WindowLifter
from babai_gi.johnson import johnson_group_gens, pairs_of


def sym(n):
    gens = []
    if n >= 2:
        gens.append(from_cycles(n, [[0, 1]]))
    if n >= 3:
        gens.append(from_cycles(n, [list(range(n))]))
    return PermGroup(n, gens)


def alt(n):
    g = [from_cycles(n, [[0, 1, 2]])]
    if n % 2 == 1:
        g.append(from_cycles(n, [list(range(n))]))
    else:
        g.append(from_cycles(n, [list(range(1, n))]))
    return PermGroup(n, g)


def dihedral(n):
    rot = from_cycles(n, [list(range(n))])
    ref = tuple((-i) % n for i in range(n))
    return PermGroup(n, [rot, ref])


def cyclic(n):
    return PermGroup(n, [from_cycles(n, [list(range(n))])])


def wreath_sym(a, b):
    """Sym(a) wr Sym(b) in imprimitive action on a*b points."""
    n = a * b
    gens = [from_cycles(n, [[0, 1]]), from_cycles(n, [list(range(a))])]
    # permute blocks
    blk_swap = list(range(n))
    for i in range(a):
        blk_swap[i], blk_swap[a + i] = a + i, i
    gens.append(tuple(blk_swap))
    blk_cycle = tuple(((i // a + 1) % b) * a + i % a for i in range(n))
    gens.append(blk_cycle)
    return PermGroup(n, gens)


@pytest.mark.parametrize("n", range(1, 9))
def test_symmetric_orders(n):
    assert sym(n).order() == factorial(n)


@pytest.mark.parametrize("n", range(3, 9))
def test_alternating_orders(n):
    assert alt(n).order() == factorial(n) // 2


@pytest.mark.parametrize("n", [3, 4, 5, 7, 10])
def test_dihedral_cyclic(n):
    assert dihedral(n).order() == 2 * n
    assert cyclic(n).order() == n


@pytest.mark.parametrize("a,b", [(2, 3), (3, 2), (3, 3), (2, 4), (4, 2)])
def test_wreath_orders(a, b):
    assert wreath_sym(a, b).order() == factorial(a) ** b * factorial(b)


@pytest.mark.parametrize("m", [4, 5, 6, 7])
def test_johnson_group_orders(m):
    gens = johnson_group_gens(m, 2)
    G = PermGroup(len(pairs_of(m)), gens)
    assert G.order() == factorial(m)


def test_membership_and_sift():
    G = alt(6)
    for g in itertools.islice(G.elements(), 50):
        assert G.contains(g)
    odd = from_cycles(6, [[0, 1]])
    assert not G.contains(odd)
    assert len(list(G.elements())) == 360


def test_orbits_and_blocks():
    G = wreath_sym(3, 2)
    assert G.is_transitive()
    blocks = G.minimal_block_system()
    assert sorted(map(sorted, blocks)) == [[0, 1, 2], [3, 4, 5]]
    assert sym(5).minimal_block_system() == [[i] for i in range(5)]
    D = dihedral(6)
    bl = D.minimal_block_system()
    assert len(bl) in (2, 3)


def test_pointwise_stabilizer():
    G = sym(6)
    H = G.pointwise_stabilizer([0, 1])
    assert H.order() == factorial(4)
    for g in H.gens:
        assert g[0] == 0 and g[1] == 1


def test_even_subgroup():
    G = sym(5)
    E = PermGroup(5, even_subgroup_gens(G.gens, 5))
    assert E.order() == 60
    for g in E.gens:
        assert parity(g) == 0


def test_window_lifter():
    G = wreath_sym(3, 2)
    # window = the invariant set of the point stabiliser... use full group with window {0,1,2}? not invariant.
    H = G.pointwise_stabilizer([0])  # fixes block {0,1,2} setwise
    W = WindowLifter(H, [0, 1, 2])
    assert W.restricted.order() == 2
    for h in W.restricted.elements():
        g = W.lift(h)
        assert g is not None
        assert H.contains(g)
        assert tuple(W.index[g[p]] for p in W.pts) == h
    assert W.kernel().order() == 6


def test_group_with_action():
    m = 5
    pairs = pairs_of(m)
    gens_omega = johnson_group_gens(m, 2)
    gens_gamma = [from_cycles(m, [[0, 1]]), from_cycles(m, [list(range(m))])]
    G = PermGroup(len(pairs), gens_omega)
    A = GroupWithAction(G, m, gens_gamma)
    assert A.kernel().order() == 1
    assert A.image_is_giant() and A.image_is_sym()
    for g in itertools.islice(G.elements(), 30):
        tau = A.phi(g)
        # consistency: tau acts on pairs as g
        for i, (a, b) in enumerate(pairs):
            assert pairs[g[i]] == tuple(sorted((tau[a], tau[b])))
        assert A.lift(tau) == g
    H = A.preimage([from_cycles(m, [[0, 1]])], image_order=2)
    assert H.order() == 2


def test_act_string_convention():
    x = ("a", "b", "c")
    p = from_cycles(3, [[0, 1, 2]])  # 0->1->2->0
    y = act_string(x, p)
    for u in range(3):
        assert y[p[u]] == x[u]
    q = from_cycles(3, [[0, 1]])
    assert act_string(act_string(x, p), q) == act_string(x, mul(p, q))
