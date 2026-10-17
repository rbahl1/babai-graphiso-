"""Direct tests of the combinatorial procedures: Weisfeiler-Leman, the Design
Lemma, Bipartite / Coherent Split-or-Johnson (incl. the January-2017 fix of the
primitive case) and the canonical-structure machinery (Structure, align).

On the graph sizes reachable in pure Python the top-level recursion rarely
needs the bipartite and coherent procedures (individualizing one vertex of a
small uniprimitive configuration already gives an alpha-colouring), so they are
exercised here on hand-built inputs; the counters in ``babai_gi.soj.STATS``
confirm which branch ran.
"""

import itertools
import random
from math import comb, factorial

import pytest

from babai_gi import soj
from babai_gi.cc import ClassicalCC
from babai_gi.design import extended_design_lemma
from babai_gi.group import PermGroup
from babai_gi.johnson import johnson_group_gens, orbitals, subsets_of
from babai_gi.perm import from_cycles
from babai_gi.soj import (SOJParams, bipartite_split_or_johnson, coherent_split_or_johnson, design_lemma,
                          upcc_split_or_johnson)
from babai_gi.structure import RecordingChooser, Structure, align, enumerate_runs
from babai_gi.wl import KStructure, classical_wl, refine_structures

from .helpers import edges_of, paley, shrikhande, rook


# ------------------------------------------------------------ Weisfeiler-Leman

def _graph_structure(n, edges):
    E = {frozenset(e) for e in edges}
    raw = []
    for u in range(n):
        for v in range(n):
            raw.append(-1 if u == v else (1 if frozenset((u, v)) in E else 0))
    distinct = sorted(set(raw))
    cmap = {c: i for i, c in enumerate(distinct)}
    return KStructure(n, 2, [cmap[r] for r in raw], len(distinct))


def test_2wl_is_coherent_and_canonical():
    e = edges_of(paley(13))
    X = refine_structures([_graph_structure(13, e)])[0]
    cc = ClassicalCC(list(range(13)), lambda u, v: X.color((u, v)))
    # Paley(13): rank 3, homogeneous, primitive
    assert cc.is_homogeneous() and len(cc.off_diagonal_colors()) == 2 and cc.is_uniprimitive()
    # structure constants are well defined (coherence)
    for col in cc.colors:
        reps = [(i, j) for i in range(13) for j in range(13) if cc.c[i][j] == col]
        sigs = set()
        for (i, j) in reps:
            sig = tuple(sorted((cc.c[i][z], cc.c[z][j]) for z in range(13)))
            sigs.add(sig)
        assert len(sigs) == 1


def test_2wl_cannot_separate_shrikhande_and_rook():
    S, R = edges_of(shrikhande()), edges_of(rook(4))
    XS, XR = refine_structures([_graph_structure(16, S), _graph_structure(16, R)])
    assert sorted(XS.colors) == sorted(XR.colors)  # same colour multiset: 2-WL equivalent


def test_3wl_separates_shrikhande_and_rook():
    S, R = edges_of(shrikhande()), edges_of(rook(4))

    def k3(edges):
        E = {frozenset(e) for e in edges}
        raw = []
        for t in itertools.product(range(16), repeat=3):
            raw.append(tuple(1 if frozenset((t[i], t[j])) in E else 0 for i in range(3) for j in range(i + 1, 3)
                             if t[i] != t[j]))
        distinct = sorted(set(raw))
        cmap = {c: i for i, c in enumerate(distinct)}
        return KStructure(16, 3, [cmap[r] for r in raw], len(distinct))

    XS, XR = refine_structures([k3(S), k3(R)])
    assert sorted(XS.colors) != sorted(XR.colors)


# --------------------------------------------------------------- Design Lemma

def test_design_lemma_on_graph_with_dominant_nonclique_class():
    """K_{1,1,...} style: a 13-vertex graph consisting of Paley(13) ... with 3 extra
    pendant-free isolated vertices: the dominant class (Paley part, 13/16 > 3/4)
    carries a non-clique coherent configuration -> kind 'b'."""
    e = edges_of(paley(13))
    X = refine_structures([_graph_structure(16, e)])[0]
    ch = RecordingChooser()
    res = design_lemma(X, 0.75, ch)
    assert res is not None
    tup, kind, col = res
    assert tup == () and kind == "b"
    groups = {}
    for v, c in enumerate(col):
        groups.setdefault(c, []).append(v)
    assert sorted(map(len, groups.values())) == [3, 13]


def test_extended_design_lemma_outputs_alpha_partition_or_johnson():
    e = edges_of(paley(13))
    X = refine_structures([_graph_structure(13, e)])[0]
    ch = RecordingChooser()
    soj.STATS.clear()
    S = extended_design_lemma(X, Structure(13, [("all", frozenset(range(13)))]), 0.75, ch, SOJParams.small_scale())
    assert soj.STATS["edl_upcc"] == 1 and soj.STATS["upcc_soj"] == 1
    assert S.johnson is None
    assert max(len(c) for k, c in S.cells) <= 0.75 * 13
    # canonical relative to the choice: replaying every choice sequence on a
    # relabelled copy must produce structures aligned with S (and vice versa)
    perm = list(range(13))
    random.Random(1).shuffle(perm)
    e2 = [(perm[u], perm[v]) for u, v in e]
    X2 = refine_structures([_graph_structure(13, e2)])[0]
    aligned = 0
    for S2, chosen in enumerate_runs(lambda c: extended_design_lemma(X2, Structure(13, [("all", frozenset(range(13)))]),
                                                                     0.75, c, SOJParams.small_scale()), ch.trace):
        sigma = align(S, S2, False)
        if sigma is not None:
            aligned += 1
            # sigma maps every cell of S onto a cell of S2 with the same key
            key2 = S2.key_of_vertex()
            for k, c in S.cells:
                assert {key2[sigma[v]] for v in c} == {k}
    assert aligned >= 1


# ------------------------------------------------- Bipartite Split-or-Johnson

def _check_bipartite_output(S, V1, beta, n1_orig):
    cells = [c for k, c in S.cells if c <= frozenset(V1)]
    if S.johnson is not None:
        return
    assert all(len(c) <= beta * n1_orig for c in cells), [len(c) for c in cells]


def test_bipartite_soj_finds_johnson_scheme():
    """V1 = the 15 two-subsets of V2 = [6] (complete 2-uniform neighbourhood
    hypergraph): HBD Prop. 5 step 4 -> Johnson scheme J(6,2) on V1."""
    V2 = [100 + i for i in range(6)]
    pairs = list(itertools.combinations(V2, 2))
    V1 = list(range(15))
    adj = {v: frozenset(pairs[v]) for v in V1}
    base = Structure(106, [("V1", frozenset(V1)), ("V2", frozenset(V2)), ("rest", frozenset(range(15, 100)))])
    ch = RecordingChooser()
    soj.STATS.clear()
    S = bipartite_split_or_johnson(V1, V2, adj, 0.75, base, ch, SOJParams.small_scale())
    assert soj.STATS["bipartite_soj_johnson_scheme"] == 1
    assert S.johnson is not None and (S.johnson.m, S.johnson.t) == (6, 2)
    # Aut of the structure restricted to V1 is Sym(6) acting on pairs
    gens = [tuple(g[v] for v in V1) for g in S.aut_gens()]
    gens = [g for g in gens if g != tuple(V1)]
    assert PermGroup(15, gens).order() == factorial(6)
    # alignment with a relabelled copy
    perm = V1[:]
    random.Random(2).shuffle(perm)
    adj2 = {perm[v]: adj[v] for v in V1}
    S2 = bipartite_split_or_johnson(V1, V2, adj2, 0.75, base, RecordingChooser(), SOJParams.small_scale())
    sigma = align(S, S2, False)
    assert sigma is not None
    for v in V1:
        assert S2.johnson.labels[sigma[v]] == S.johnson.labels[v]


def test_bipartite_soj_random_instance_canonical():
    """A random twin-free bipartite graph (|V1| = 14, |V2| = 6): the output is a
    beta-partition of V1 (or a Johnson scheme) and is canonical relative to
    the choices made (alignment with a relabelled copy succeeds)."""
    rng = random.Random(4)
    V2 = [50 + i for i in range(6)]
    V1 = list(range(14))
    subsets = list(itertools.combinations(V2, 3))
    chosen = rng.sample(subsets, 14)
    adj = {v: frozenset(chosen[v]) for v in V1}
    base = Structure(56, [("V1", frozenset(V1)), ("V2", frozenset(V2)), ("rest", frozenset(range(14, 50)))])
    ch = RecordingChooser()
    soj.STATS.clear()
    S = bipartite_split_or_johnson(V1, V2, adj, 0.75, base, ch, SOJParams.small_scale())
    _check_bipartite_output(S, V1, 0.75, 14)
    assert soj.STATS["bipartite_soj"] >= 1
    perm = list(range(56))
    p1 = V1[:]
    rng.shuffle(p1)
    p2 = V2[:]
    rng.shuffle(p2)
    for v, w in zip(V1, p1):
        perm[v] = w
    for v, w in zip(V2, p2):
        perm[v] = w
    adj2 = {perm[v]: frozenset(perm[w] for w in adj[v]) for v in V1}
    found = False
    for S2, _ in enumerate_runs(lambda c: bipartite_split_or_johnson(V1, V2, adj2, 0.75, base, c, SOJParams.small_scale()),
                                ch.trace):
        sigma = align(S, S2, False)
        if sigma is None:
            continue
        found = True
        key2 = S2.key_of_vertex()
        for k, c in S.cells:
            assert {key2[sigma[v]] for v in c} == {k}
    assert found


# -------------------------------------------------- Coherent Split-or-Johnson

def _schurian_cc(G, C1, C2):
    """The orbital configuration of G on C1 + C2 (a coherent configuration)."""
    orbs = orbitals(G)
    color = {}
    for ci, orb in enumerate(orbs):
        for (u, v) in orb:
            color[(u, v)] = ci + 1
    n = G.n
    diag = {}
    for orb in G.orbits():
        for v in orb:
            diag[v] = ("d", min(orb))
    cc = ClassicalCC(list(range(n)), lambda u, v: diag[u] if u == v else color[(u, v)])
    cc.canonical_keys()
    return cc


def test_coherent_soj_primitive_c2_2017_fix():
    """Sym(7) acting on C1 = 3-subsets (35 points, J(7,3)) and C2 = 2-subsets
    (21 points, J(7,2)): X[C1], X[C2] primitive, c nonconstant on C1 x C2.
    HBD Prop. 6, X[C2] primitive -> fix y in C2, violet / blue colours."""
    S3 = subsets_of(7, 3)
    S2 = subsets_of(7, 2)
    n = len(S3) + len(S2)
    idx3 = {T: i for i, T in enumerate(S3)}
    idx2 = {T: len(S3) + i for i, T in enumerate(S2)}
    gens = []
    for tau in (from_cycles(7, [[0, 1]]), from_cycles(7, [list(range(7))])):
        g = [0] * n
        for T, i in idx3.items():
            g[i] = idx3[tuple(sorted(tau[v] for v in T))]
        for T, i in idx2.items():
            g[i] = idx2[tuple(sorted(tau[v] for v in T))]
        gens.append(tuple(g))
    G = PermGroup(n, gens)
    C1, C2 = list(range(35)), list(range(35, 56))
    cc = _schurian_cc(G, C1, C2)
    base = Structure(n, [("C1", frozenset(C1)), ("C2", frozenset(C2))])
    ch = RecordingChooser()
    soj.STATS.clear()
    kind, data, S = coherent_split_or_johnson(cc, C1, C2, lambda u: u, lambda w: w, base, ch, 0)
    assert soj.STATS["coherent_soj_c2_primitive_2017fix"] == 1
    assert kind == "bipartite"
    W1, W2, adjW = data
    assert set(W1) <= set(C1) and set(W2) <= set(C2)
    assert len(W1) > len(C1) / 2 and 1 <= len(W2) < len(C2) / 2
    assert len(W1) == 20 and len(W2) == 10   # 3-sets meeting the fixed pair in one point; pairs disjoint from it
    degs = {len(adjW[u]) for u in W1}
    assert len(degs) == 1 and 0 < degs.pop() < len(W2)   # semiregular, nonempty, not complete
    twin = {}
    for u in W1:
        twin.setdefault(adjW[u], []).append(u)
    assert max(map(len, twin.values())) <= len(W1) / 2


def test_coherent_soj_imprimitive_c2():
    """Sym(3) wr Sym(2) acting on the 3x3 rook's graph (C1, uniprimitive) and
    on its 6 lines (C2: rows and columns, an imprimitive configuration):
    HBD Prop. 6 / Babai Sec. 7.7 (imprimitive case)."""
    pts = [(a, b) for a in range(3) for b in range(3)]
    lines = [("r", a) for a in range(3)] + [("c", b) for b in range(3)]
    objs = pts + lines
    idx = {o: i for i, o in enumerate(objs)}
    n = len(objs)

    def act(f):
        g = [0] * n
        for o in objs:
            g[idx[o]] = idx[f(o)]
        return tuple(g)

    def rowcycle(o):
        if o in pts:
            return ((o[0] + 1) % 3, o[1])
        return ("r", (o[1] + 1) % 3) if o[0] == "r" else o

    def rowswap(o):
        s = {0: 1, 1: 0, 2: 2}
        if o in pts:
            return (s[o[0]], o[1])
        return ("r", s[o[1]]) if o[0] == "r" else o

    def transpose(o):
        if o in pts:
            return (o[1], o[0])
        return ("c" if o[0] == "r" else "r", o[1])

    G = PermGroup(n, [act(rowcycle), act(rowswap), act(transpose)])
    assert G.order() == 72
    C1, C2 = list(range(9)), list(range(9, 15))
    cc = _schurian_cc(G, C1, C2)
    assert cc.induced(C1).is_uniprimitive()
    assert cc.induced(C2).disconnected_off_diagonal_colors()
    base = Structure(n, [("C1", frozenset(C1)), ("C2", frozenset(C2))])
    ch = RecordingChooser()
    soj.STATS.clear()
    kind, data, S = coherent_split_or_johnson(cc, C1, C2, lambda u: u, lambda w: w, base, ch, 0)
    assert soj.STATS["coherent_soj_c2_imprimitive"] == 1
    assert kind == "bipartite"
    W1, W2, adjW = data
    assert sorted(W1) == C1 and len(W2) == 3     # one parallel class of lines
    twin = {}
    for u in W1:
        twin.setdefault(adjW[u], []).append(u)
    assert max(map(len, twin.values())) == 3 <= len(W1) / 2
    # feeding the result to the bipartite procedure gives a 3/4-partition of C1
    S2 = bipartite_split_or_johnson(W1, W2, adjW, 0.75, S, RecordingChooser(), SOJParams.small_scale())
    _check_bipartite_output(S2, C1, 0.75, 9)


def test_upcc_soj_on_rook_and_paley():
    for g, m in ((rook(4), 16), (paley(13), 13)):
        X = refine_structures([_graph_structure(m, edges_of(g))])[0]
        cc = ClassicalCC(list(range(m)), lambda u, v: X.color((u, v)))
        assert cc.is_uniprimitive()
        soj.STATS.clear()
        S = upcc_split_or_johnson(cc, 0.75, Structure(m, [("all", frozenset(range(m)))]), RecordingChooser(), SOJParams.small_scale())
        assert soj.STATS["upcc_soj"] == 1
        assert S.johnson is not None or max(len(c) for k, c in S.cells) <= 0.75 * m


# ------------------------------------------------------- structures / align

def test_structure_automorphisms_and_align():
    m = 9
    S = Structure(m, [("a", frozenset([0, 1, 2])), ("a", frozenset([3, 4, 5])), ("b", frozenset([6, 7])), ("c", frozenset([8]))])
    assert S.aut_order() == factorial(3) ** 2 * 2 * 2
    assert PermGroup(m, S.aut_gens()).order() == S.aut_order()
    perm = [3, 4, 5, 0, 1, 2, 7, 6, 8]
    T = Structure(m, [("a", frozenset([perm[v] for v in (0, 1, 2)])), ("a", frozenset([perm[v] for v in (3, 4, 5)])),
                      ("b", frozenset([6, 7])), ("c", frozenset([8]))])
    sigma = align(S, T, False)
    assert sigma is not None
    key_T = T.key_of_vertex()
    key_S = S.key_of_vertex()
    assert all(key_T[sigma[v]] == key_S[v] for v in range(m))
    sigma_even = align(S, T, True)
    assert sigma_even is not None
    from babai_gi.perm import parity
    assert parity(sigma_even) == 0
    U = Structure(m, [("a", frozenset([0, 1, 2, 3])), ("a", frozenset([4, 5])), ("b", frozenset([6, 7])), ("c", frozenset([8]))])
    assert align(S, U, False) is None
