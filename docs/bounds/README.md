# Per-function operation bounds

The documents in this directory prove, for every function of `babai_gi`, an explicit bound on
the operations of one call, and combine these bounds into the own work of each node type of the
recursion (`PROOF.md` Part III). The cost model and the method are stated in `SPEC.md`;
`PROOF.md` Part I (§1–§2) states the same cost model.

| file | content |
|---|---|
| `SPEC.md` | the cost model and the method of the per-function bounds |
| `group.md` | `perm.py`, `group.py` (Schreier–Sims), `action.py`, `canon.py`, `tower.py` |
| `structure_cc_wl.md` | `structure.py`, `cc.py`, `wl.py` |
| `soj.md` | `soj.py`, `design.py`: one run of Split-or-Johnson, its choice count (Theorem B, the `β y² + R(y)` of the time bound) |
| `johnson_certs.md` | `johnson.py`, `certificates.py`, with the number of solver calls of a certificate and of a comparison |
| `main.md` | `main.py`, `graph.py`, and the own work of every node type in terms of the symbols of the other documents |
| `ownwork.md` | all symbols substituted: `W(node) ≤ λ^e 2^ω` for every node type |
| `ownwork_gaps.md` | complete proofs of the items `ownwork.md` §9 gives only in outline |

`group.md`, `structure_cc_wl.md`, `soj.md`, `johnson_certs.md` and `main.md` are the per-module
bound documents. The instruction profiles the documents use are frozen in
`babai_gi/_opprofiles.py` and checked against the code by `tests/test_opbounds.py`;
`tests/test_attribution.py` checks the hypotheses of `PROOF.md` Lemma 1.1 on which the
profiles rest, and lists the code objects bounded by hand instead.
`tests/test_soj_regions.py` checks the hypotheses of `soj.md` Lemma 1.1' and freezes the region
profiles that `soj.md` and `ownwork.md` §3 use. `ownwork.md` §3 gives the bounds of `johnson.iroot`
and `johnson._cameron_candidates` and checks the bounds of `johnson.recognize_cameron`,
`soj.upcc_split_or_johnson`, `soj._thin_cycle_structure` and the functions listed in its §3.5
against the code.
