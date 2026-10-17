"""Command-line demo:  python -m babai_gi [--small-scale] graph1.txt graph2.txt

Graph Isomorphism through the String Isomorphism reduction of Babai Sec. 1.1.1
(HBD Sec. 1): the graphs become 0/1 strings on binom(V, 2) acted on by Sym(V).

Edge-list format: first line "n" (number of vertices, optionally followed by
the number of edges), then one edge "u v" per line (0-based vertices; lines
starting with '#' are comments).  Prints an isomorphism or NOT ISOMORPHIC.

By default the papers' thresholds are used (``Params.paper()``); for graphs
with fewer than 160 vertices they prescribe the enumeration of Sym(V), which
is feasible only up to ~9 vertices.  ``--small-scale`` selects
``Params.small_scale()`` (small constants, the Johnson-case machinery runs;
see README Sec. 5).
"""

import sys
import time

from .graph import graph_isomorphism, parse_edge_list
from .main import Params, Solver


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    small = "--small-scale" in argv
    argv = [a for a in argv if a != "--small-scale"]
    if len(argv) != 2:
        print(__doc__)
        return 2
    with open(argv[0]) as f:
        n1, e1 = parse_edge_list(f.read())
    with open(argv[1]) as f:
        n2, e2 = parse_edge_list(f.read())
    solver = Solver(Params.small_scale() if small else Params.paper())
    t0 = time.perf_counter()
    iso = graph_isomorphism(e1, n1, e2, n2, solver=solver)
    dt = time.perf_counter() - t0
    if iso is None:
        print("NOT ISOMORPHIC")
    else:
        print("ISOMORPHIC")
        print(" ".join(f"{u}->{v}" for u, v in sorted(iso.items())))
    print(f"# time {dt:.3f}s; params {solver.params.preset}; recursive calls {solver.stats['calls']}; "
          f"johnson cases {solver.stats['johnson_case']}; branches {solver.stats['branches']}")
    return 0 if iso is not None else 1


if __name__ == "__main__":
    sys.exit(main())
