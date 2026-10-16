# Three-module publication validation, 2026-10-16

Scope: publication validation only. Research was not resumed. The only repository edit made by this validator was adding these three imports to the existing semiprime block of `RiemannGaussian.lean`:

```lean
import RiemannGaussian.SemiprimeFermatQuotientCatalog
import RiemannGaussian.SemiprimeSparseResidueGauss
import RiemannGaussian.SemiprimeSparseResidueGaussRadius
```

The repository HEAD at this validation was `c6916d08aba9d5fe3059b630ae74dc7b6128efee`; the validated new files and three import additions were still uncommitted. Current source hashes in the companion JSON identify those inputs separately from HEAD.

All commands below ran from `/home/dbsanfte/riemann/formal`. There are no scoped blockers. Full-root build, whole-project gates, staging, commit, push and exact-SHA remote CI remain owned by the parent publication task; this report does not claim their completion.

## Lean validation

The targeted Lake build exited 0:

```bash
/home/dbsanfte/.elan/bin/lake build RiemannGaussian.SemiprimeFermatQuotientCatalog RiemannGaussian.SemiprimeSparseResidueGauss RiemannGaussian.SemiprimeSparseResidueGaussRadius --wfail
```

Its log is `leaf-build.log`; all three selected leaves rebuilt successfully (reported 11s, 9s and 19s respectively), with their dependencies reused/built by Lake. Project `lakefile.toml` also sets `warningAsError = true`.

Each direct warning-as-error compilation independently exited 0 without diagnostics:

```bash
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true RiemannGaussian/SemiprimeFermatQuotientCatalog.lean
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true RiemannGaussian/SemiprimeSparseResidueGauss.lean
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true RiemannGaussian/SemiprimeSparseResidueGaussRadius.lean
```

The existing checker scripts each exited 0:

```bash
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true scripts/CheckSemiprimeFermatQuotientCatalog.lean
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true scripts/CheckSemiprimeSparseResidueGauss.lean
/home/dbsanfte/.elan/bin/lake env lean -DwarningAsError=true scripts/CheckSemiprimeSparseResidueGaussRadius.lean
```

| Module | Authored declarations | Generated declarations | All module declarations | All module theorems | Namespace linters |
| --- | ---: | ---: | ---: | ---: | ---: |
| SemiprimeFermatQuotientCatalog | 24 | 9 | 33 | 28 | 15, all passed |
| SemiprimeSparseResidueGauss | 4 | 2 | 6 | 6 | 15, all passed |
| SemiprimeSparseResidueGaussRadius | 11 | 4 | 15 | 14 | 15, all passed |
| Total | 39 | 15 | 54 | 48 | |

The checker scans use compiled module provenance, including private/generated declarations; each rejects a project-defined axiom and rejects every transitive axiom outside `propext`, `Classical.choice`, and `Quot.sound`. All 54 declarations passed. Logs are `check-FermatQuotientCatalog.log`, `check-SparseResidueGauss.log`, and `check-SparseResidueGaussRadius.log`.

A separate placeholder scan of the three proof files and three check scripts found no `sorry`, `admit`, or `sorryAx` tokens. `git diff --check -- RiemannGaussian.lean` exited 0.

## Existing executable probes

Both existing probes exited 0 using the repository virtual environment and `-B`:

```bash
../.venv/bin/python -B scripts/probe_semiprime_fermat_quotient_catalog.py --self-test
../.venv/bin/python -B scripts/probe_semiprime_sparse_residue_gauss.py --self-test
```

The catalog probe reported PASS for 18 test groups, including larger-factor reciprocal completion and the equal nonzero quotient case. The Gauss probe reported `{"checks": 287, "status": "pass"}`. Their exact outputs are in `fermat-python-self-test.log` and `gauss-python-self-test.log`. Both Python sources also parsed successfully with `ast.parse`.

These replay existing implementation checks; they are not universal acquisition proofs, complexity measurements, or new theorem claims. There is no separate new runtime algorithm in the radius leaf; it uses the unchanged Gauss probe, whose pin matches.

## Audit preservation and taxonomy

All pin-shaped records (`path` plus `sha256`) recursively read from the three existing JSON audits matched their current files: 14 catalog entries, 21 Gauss entries, and 23 radius entries. These are 58 pin records, including repeated references; there were zero mismatches and zero missing files. No historic JSON audit or hash was rewritten. Source byte counts, current SHA256 values for the three proof files, three checkers, two Python probes and three audits, and detailed pin results are retained in `source-and-pin-recheck.json`.

The actual `module_family` function from `scripts/build_theorem_explorer.py` assigns all three new module names to `semiprime` using the existing `modulePrefixes: ["Semiprime"]` rule. No explicit taxonomy override is required. This validator did not edit `docs/theorem-explorer/metadata.json` or generated indexes.

The first auxiliary Python attempt to import the explorer helper omitted `scripts` from `sys.path` and failed with `ModuleNotFoundError: numerical_certificate`; rerunning the read-only inspection with the correct import path succeeded. No project source or test failed from that inspection setup error.

The source/doc review preserves the existing boundaries: catalog arithmetic coverage, four Gauss arithmetic/certificate identities, and the certified radius/public-cap closure. No all-semiprime one-sixth factoring theorem or full Lean bit-complexity theorem is asserted.
