# Verification records

| File | What it is |
| --- | --- |
| `build.log` | Output of `lake build` for the V4 sources (incremental, seeded from the V3 build cache) |
| `v4-certificate-incremental.log` | `lake env lean --trust=0 FregeanECA/V4/Certificate.lean` on the same build |
| `verify-run.log`, `fresh-build.log`, `*-certificate.log`, `axioms.log`, ... | Live logs of `lean/verify.py` (fresh-source rebuild, all certificates, transitive axiom audit) |
| `verification.json` | The verifier's machine-readable record: commands, exit codes, source hashes, dependency pins, audited declarations, required endpoints, unexpected axioms |

## Status

- 27 October 2026, incremental: `lake build` completed and the V4 certificate,
  restated for the printed theory (A3 = functional Basic Law V), passed under
  `--trust=0` with only `propext`, `Classical.choice` and `Quot.sound`
  (`build.log`, `v4-certificate-incremental.log`).
- 28 October 2026, fresh-source audit (`verify.py`), final run with the
  printed-theory module `V4/PrintedTheory.lean` (A3 = functional Basic Law V,
  A5 = T ≠ F) and the choice module `V4/Choice.lean`: **PASS**. All ten commands
  exited 0 (V4, V3, V2, FE and three-way certificates; terminal, Part II and
  research audits; full declaration audit). 179 project modules, 19 vendored
  modules, 7,831 audited declarations, 297 required endpoints, 205 recorded
  source/configuration hashes. No admissions, unexpected axioms, missing
  endpoints, changed vendor sources, dependency-pin mismatches or source
  drift. Record: `verification.json`; live logs: `verify-run.log` and the
  per-command logs listed above. The runs of 22 and 23 September 2026, before
  the printed-theory module, also passed.
- The hand audit of the paper-to-Lean correspondence is `../COVERAGE.md`.
- Local paths in the logs are replaced by `<repo>` (this repository),
  `<toolchain>` (the Lean toolchain and dependency cache), `<temp>` (the
  verifier's fresh source copy) and `<home>`.
