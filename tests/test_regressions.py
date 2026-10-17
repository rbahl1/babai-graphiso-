"""Edge cases of the search (non-isomorphic inputs with no successful branch, the
pruned exhaustive search, giants, C_14), plus the slow Cai-Furer-Immerman instance
over K4 (a 3-WL-equivalent pair that the group-theoretic machinery must separate)."""

import random
from math import factorial

import networkx as nx
import pytest

from babai_gi.action import GroupWithAction
from babai_gi.graph import GraphInstance, graph_isomorphism
from babai_gi.group import PermGroup
from babai_gi.main import Params, Solver, _chain_search
from babai_gi.perm import act_string, from_cycles, maps_string, mul
from babai_gi.structure import Structure

from .helpers import cfi, check_isomorphism, edges_of, relabel  # noqa: F401


def _sym(n):
    return PermGroup(n, [from_cycles(n, [[0, 1]]), from_cycles(n, [list(range(n))])])


# ------------------------------------------------------------ branch(), x != y

def test_branch_without_successful_branch_returns_none():
    """Solver.branch used to return the known automorphisms (with the identity as
    representative) when x != y and no branch produced an isomorphism, i.e. a
    false 'isomorphic' answer whenever F was non-trivial."""
    n = 6
    G = _sym(n)
    Gw = GroupWithAction(G, n, list(G.gens), phi_fn=lambda g: g)
    x = (0, 0, 0, 1, 1, 1)
    y = (0, 0, 1, 1, 1, 0)  # a translate of x, but the recursion below is told that no branch succeeds

    def proc(s, chooser):
        chooser.check(("letters", sorted(s)))
        return Structure(n, [("all", frozenset(range(n)))])

    swap = from_cycles(n, [[0, 1]])  # an automorphism of x
    s = Solver()
    assert s.branch(Gw, x, y, proc, [swap], recurse=lambda G1, x1, y1: None) is None
    # with the genuine recursion the translate is found and the full coset is returned
    C = s.branch(Gw, x, x, proc, [swap])
    assert C is not None and C.group.order() == factorial(3) ** 2


# ------------------------------------------------- pruned exhaustive search

@pytest.mark.parametrize("seed", [1, 2, 3])
def test_chain_search_equals_plain_enumeration(seed):
    rng = random.Random(seed)
    n = 7
    gens = [from_cycles(n, [[0, 1, 2, 3]]), from_cycles(n, [[1, 3]]), from_cycles(n, [[4, 5, 6]]), from_cycles(n, [[0, 4]])]
    G = PermGroup(n, gens)
    for _ in range(5):
        x = tuple(rng.randrange(2) for _ in range(n))
        g = tuple(range(n))
        for _ in range(10):
            g = mul(g, rng.choice(gens))
        for y in (x, act_string(x, g), tuple(rng.randrange(2) for _ in range(n))):
            ref = sorted(h for h in G.elements() if maps_string(x, y, h))
            assert sorted(_chain_search(G, x, y)) == ref


def test_giant_group_uses_trivial_case_not_enumeration():
    """Sym(7) on 7 points (order 5040) with a 3-letter string: the trivial case
    (letter multiplicities) must answer, with the exact automorphism group."""
    G = _sym(7)
    x = (0, 1, 2, 0, 1, 2, 0)
    s = Solver(Params(brute_force_order=1))
    C = s.iso(G, x, x)
    assert C.group.order() == factorial(3) * factorial(2) * factorial(2)
    assert s.stats["trivial_case"] >= 1 and s.stats["strong_luks"] == 0 and s.stats["brute_force"] == 0


def test_c14_cycle_is_fast_enough():
    """C14: the Extended Design Lemma splits the vertices into the two colour
    classes of the bipartition and the recursion goes through the product action
    S7 wr S2 and the enumeration of Sym(7); this took minutes before the pruned
    search / trivial-case fixes."""
    e = [(i, (i + 5) % 14) for i in range(14)]
    e2, _ = relabel(e, 14, random.Random(14))
    s = Solver(Params.small_scale())
    iso = graph_isomorphism(e, 14, e2, 14, solver=s)
    assert iso is not None
    check_isomorphism(e, e2, 14, iso)
    assert s.stats["cameron_product_action"] >= 1


# ------------------------------------------------------------ CFI over K4

@pytest.mark.slow
def test_cfi_k4_twisted_vs_untwisted():
    """CFI graphs over K4 (28 vertices, 48 edges): 3-WL equivalent, hence the
    verdict comes from Local Certificates / AggregateCertificates (Case 2b here).
    Non-isomorphic inputs pay the full multiplicative cost (every branch of every
    reduction is explored): about 15-20 minutes in pure Python."""
    base = nx.complete_graph(4)
    A, B = cfi(base, False), cfi(base, True)
    n = A.number_of_nodes()
    eA, eB = edges_of(A), edges_of(B)
    assert not nx.is_isomorphic(A, B)
    GraphInstance._shared.clear()
    s = Solver(Params.small_scale())
    assert graph_isomorphism(eA, n, eB, n, solver=s) is None
    assert s.stats["imprimitive_johnson"] >= 1 and s.stats["lc_full"] + s.stats["lc_notfull"] >= 1
    assert s.stats["agg_case_2b"] >= 1
