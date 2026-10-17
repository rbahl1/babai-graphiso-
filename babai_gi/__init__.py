"""babai_gi: an implementation of Babai's quasipolynomial-time Graph / String
Isomorphism algorithm (arXiv:1512.03547v2) following the exposition of
Helfgott, Bajpai and Dona (arXiv:1710.04574).

Public entry points (see babai_gi.graph and babai_gi.main):
    graph_isomorphism(edges1, n1, edges2, n2)  -> isomorphism (dict) or None
    graph_automorphism_group_order(edges, n)  -> |Aut|
    string_isomorphism(G, x, y)               -> Coset or None
"""


def __getattr__(name):  # lazy re-exports to keep submodules importable standalone
    if name in ("graph_isomorphism", "graph_automorphism_group_order", "graph_automorphisms"):
        from . import graph
        return getattr(graph, name)
    if name in ("string_isomorphism", "Params"):
        from . import main
        return getattr(main, name)
    raise AttributeError(name)
