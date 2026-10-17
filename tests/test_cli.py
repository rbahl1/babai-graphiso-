"""The command-line interface: ``python -m babai_gi graph1.txt graph2.txt``."""

import os
import subprocess
import sys

import networkx as nx

from babai_gi.graph import parse_edge_list

from .helpers import edges_of, relabel

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _write(path, n, edges, comment=None):
    with open(path, "w") as f:
        if comment:
            f.write(f"# {comment}\n")
        f.write(f"{n} {len(edges)}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")


def _run(*files):
    proc = subprocess.run([sys.executable, "-m", "babai_gi", *files], cwd=ROOT, capture_output=True, text=True, timeout=600)
    return proc.returncode, proc.stdout, proc.stderr


def test_parse_edge_list():
    n, e = parse_edge_list("# comment\n5 3\n0 1\n1 2\n\n2 3\n")
    assert n == 5 and e == [(0, 1), (1, 2), (2, 3)]


def test_cli_isomorphic(tmp_path):
    """10 vertices: with the default (paper) thresholds the CLI would enumerate
    Sym(10); ``--small-scale`` selects Params.small_scale()."""
    import random
    e = edges_of(nx.petersen_graph())
    e2, perm = relabel(e, 10, random.Random(1))
    f1, f2 = tmp_path / "petersen.txt", tmp_path / "petersen_relabeled.txt"
    _write(f1, 10, e, "Petersen graph")
    _write(f2, 10, e2)
    code, out, err = _run("--small-scale", str(f1), str(f2))
    assert code == 0, err
    lines = out.strip().splitlines()
    assert lines[0] == "ISOMORPHIC"
    mapping = dict(tuple(int(t) for t in tok.split("->")) for tok in lines[1].split())
    assert sorted(mapping) == list(range(10)) and sorted(mapping.values()) == list(range(10))
    E2 = {frozenset(x) for x in e2}
    assert {frozenset((mapping[u], mapping[v])) for u, v in e} == E2
    assert lines[2].startswith("# time") and "params small_scale" in lines[2]


def test_cli_not_isomorphic(tmp_path):
    e1 = edges_of(nx.disjoint_union(nx.cycle_graph(5), nx.cycle_graph(5)))
    e2 = edges_of(nx.cycle_graph(10))
    f1, f2 = tmp_path / "a.txt", tmp_path / "b.txt"
    _write(f1, 10, e1)
    _write(f2, 10, e2)
    code, out, err = _run(str(f1), "--small-scale", str(f2))
    assert code == 1, err
    assert out.strip().splitlines()[0] == "NOT ISOMORPHIC"


def test_cli_default_is_paper_preset(tmp_path):
    """Without the flag the papers' thresholds are used (Params.paper()); on 8
    vertices Reduce-to-Johnson line 5 enumerates Sym(8) (|G| = 8! < 28^{1+log2 28})."""
    import random
    e = edges_of(nx.hypercube_graph(3))
    e2, _ = relabel(e, 8, random.Random(8))
    f1, f2 = tmp_path / "q3.txt", tmp_path / "q3b.txt"
    _write(f1, 8, e)
    _write(f2, 8, e2)
    code, out, err = _run(str(f1), str(f2))
    assert code == 0, err
    lines = out.strip().splitlines()
    assert lines[0] == "ISOMORPHIC"
    mapping = dict(tuple(int(t) for t in tok.split("->")) for tok in lines[1].split())
    assert {frozenset((mapping[u], mapping[v])) for u, v in e} == {frozenset(x) for x in e2}
    assert "params paper" in lines[2] and "johnson cases 0" in lines[2]


def test_cli_usage():
    code, out, err = _run()
    assert code == 2
    assert "Edge-list format" in out
