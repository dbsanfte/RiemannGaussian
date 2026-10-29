# Pinned external SAT endpoint and completed closure audit

## Completed result: PASS

The original strict closure build completed **2569/2569 modules, zero failures**, with terminal exit0 confirmed by root (6255.96 seconds). No restart or duplicate closure build was launched.

The post-build runner completed successfully:

| Check | Result | Exact scope |
|---|---|---|
| Pinned artifacts | PASS | All 2569 source Git blobs and build-record SHA256 hashes; all 2569 isolated `.olean` SHA256 hashes; comparator/config/docs pinned; compiler and commit match |
| Expected endpoint type | PASS | Comparator theorem signature copied verbatim and proved by `Final.exact_count_and_sat`; only standard axioms |
| Every original emitted declaration | PASS | **2569 source modules, 90,034 declarations, 63,007 theorem constants**; no source-defined axioms; every transitive axiom among `propext`, `Classical.choice`, `Quot.sound` |

Endpoint process elapsed 6.632 seconds including wrapper overhead (time-tool wall 5.74 s), maximum RSS7,925,060 KiB. Complete declaration audit elapsed 10.039 seconds including wrapper overhead (time-tool wall 9.15 s), maximum RSS8,022,584 KiB. Both strict Lean processes exited 0. Cached imported axiom metadata made the full audit practical; this was not an estimate or sampled audit.

Passing artifacts are `external-final-audit-results.json`, `external-every-declaration.json` (per-module exact counts), `external-complete-artifacts.json`, `external-audit-plan.json` (pin and generated/runner hashes), `external-comparator-signature-check.json`, `ExternalComparatorEndpoint.log`, `ExternalEveryDeclaration.log`, and their `.resources.txt` files. Generated Lean sources and `run_external_final_audit.py` reproduce the checks.

**Verified theorem rate:** fixed-width canonical k-CNF exact counting/SAT in `(L+1)^{O_k(1)} 2^{O_k(n(loglog n)^2/sqrt(log n))}`, with polynomial all-prefix visited-tape space. This is the documented older formalized rate. The sharper Oct25 manuscript `n loglog n/sqrt(log n)` and bounded-density `n/sqrt(log n)` exponents, and Appendix D.1 generic tensor contraction, are NOT established by this audit. No unconditional sixth-rate factoring theorem follows from this endpoint alone.

**Configured Main wrapper not run:** Main requires 522 additional source modules (3091 total closure) beyond Final. It was not treated as a one-file wrapper and was not built under the small-increment instruction. Thus the exact requested theorem in **Final is verified**, while a full run of the JSON-configured Main comparator wrapper is not claimed.

The rest of this report records the precise theorem, model, reproduction and limits of that completed result.

This is a read-only audit of pinned `openai-math` commit `7ef5c0cc...`, not our new counter extension and not paper Appendix D.1. The existing live isolated closure build has NOT been restarted.

## Exact endpoint and computational model

Source: `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean:74`,
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`.
Its exact original signature is preserved in `external-comparator-signature.txt` and checked whitespace-normalized against `ComparatorChallenges/SubexponentialSAT.lean:194` in `external-comparator-signature-check.json` (TRUE).

For each fixed integer k>=2, the theorem asserts one fixed finite-state/finitely-many-tapes `Computation.PrimitiveMachine`, designated count/answer tapes, positive real C,A,S and positive natural d,e, working for ALL variable counts n and ALL canonical Finset CNFs F on Fin n of width<=k. From the literal `Encoding.encodeCNF F` initialization it has a finite actual primitive trace ending with:

* the count tape exactly containing `countWord(SAT.count F)`;
* answer tape and halt state equal to `decide(0<SAT.count F)`;
* countWord decodes to the exact count and has length<=n+1;
* time <= `C*(formulaBitLength(F)+1)^d * 2^(A*runtimeScale(n))`;
* every intermediate prefix trace visits at most `S*(formulaBitLength(F)+1)^e` cells.

`runtimeScale(n)=n*(log(log(n+16)))^2/sqrt(log(n+16))`. Constants/machine may depend on fixed k. This is NOT a uniform algorithm taking arbitrary unbounded k as part of the input, and it does not specify behavior on malformed/noncanonical Boolean words.

`Computation.lean:273–309` defines the computational model: finite control scans one selected tape's single bit-or-blank head and performs one head move or one cell write per primitive transition, or halts. There are no unit-cost arithmetic or tensor-contraction primitives. `SqrtLogSpace/VisitedTape.lean:14–62` instruments all head positions with min/max coordinates; visitedSpace sums inclusive intervals and includes the initial input cells. It is an all-execution-prefix visited-space statement, not only final nonblank space.

The stronger helper `compiled_exact_count_and_sat` exhibits a fixed `BitProgram.Program 80 1220 labels` with count tape256 and answer tape1216, compiled into this primitive model. `exact_count_eth` transports to polynomial `(n+F.card+1)` factors for n>=20 with the SAME older rho scale. `sat_polynomial_space` gives decision for k>=3 and `original_sat_main` recovers the old main decision interface.

Documentation `lean/docs/378.md` agrees: formalized rate is `n(loglog n)^2/sqrt(log n)`. It explicitly distinguishes the sharper Oct25 manuscript rates `n loglog n/sqrt(log n)` and bounded-density `n/sqrt(log n)`. The final theorem does not establish generic high-arity Boolean tensor counting or the Appendix D.1 tensor theorem. Therefore this external endpoint alone is not a proved factoring runtime; our separate generic layout/counter/network extension is still necessary.

## Comparator checks, with exact limits

`ComparatorChallenges/SubexponentialSAT.json` requests this exact theorem, permitted axioms `{propext,Quot.sound,Classical.choice}`, and `enable_nanoda=false`. Its configured solution module is **Main**, whose imports include both `SqrtLog.ExecutionNativeFinal` and `SqrtLogSpace.Final`.

The live closure is the **2569-module Final dependency closure**. It does not include Main or the extra ExecutionNativeFinal branch. Thus the following audit directly verifies the requested theorem in Final, but is not reported as running the entire officially configured Main comparator wrapper. No additional closure compilation is silently launched.

`ExternalComparatorEndpoint.lean` is generated by copying the comparator theorem signature VERBATIM (renaming only the new audit declaration), importing Final, and proving it by the pinned final theorem. This is a strict elaboration/type check of the exact expected contract under the actual pinned supporting declarations. The comparator's `sorry` stub is NEVER imported. The supporting machine, encoding, count and visited-space definitions were inspected against the source versions and describe the same model above. This is not an independent nanoda/kernel recheck or an execution of an external comparator harness; the configuration itself disables nanoda and lists no separate definition_names checks.

## Every original declaration, not just final theorem axioms

`ExternalEveryDeclaration.lean` selects ALL 2569 module names from the pinned closure manifest. It iterates each imported module's `moduleData.constants`, including generated/private declarations; rejects source-defined axioms; and checks each declaration's TRANSITIVE `Lean.collectAxioms` against the standard allowlist. It asserts every expected source module was present and records per-module declaration/theorem counts in `external-every-declaration.json`. It does not merely inspect theorem names beginning with a selected namespace.

Lean4.34.1 precomputes imported per-declaration axiom dependencies in its persistent exported-axioms extension (`Lean/Util/CollectAxioms.lean`). Therefore calls on imported constants use cached dependencies instead of independently traversing the full proof DAG repeatedly. Axiom allowlisting still does not independently prove the intended mathematical interpretation or exclude a mistaken theorem specification; that is why the endpoint/model checks above are separate.

Mathlib/core declarations outside the selected 2569 source modules are not themselves enumerated as roots, but any nonstandard axiom USED transitively by a selected source declaration is rejected. No new axiom is added by the audit.

## Reproduction and gating

`run_external_final_audit.py` uses only standard Python libraries and existing Lean/Lake binaries. It NEVER calls a closure build. It regenerates the expected endpoint and every-declaration audit from the pinned manifests, and constructs LEAN_PATH exactly as the build script does: isolated `lean-build` FIRST, then matching package/toolchain caches, excluding the repository's own output directory so it cannot shadow original OAI modules.

Prepare / inspect (safe while the build is running):

```
python3 /tmp/semiprime-layout-assembly-20261026/run_external_final_audit.py
```

Execute only after the EXISTING build is complete:

```
python3 /tmp/semiprime-layout-assembly-20261026/run_external_final_audit.py --run --timeout 3600
```

The runner refuses with NOT_READY while state is not complete, on any failures, or if completed module names differ from the closure. Before running it hashes EVERY original source and `.olean` against the strict build's recorded hashes and verifies the checkout commit. It then runs the comparator endpoint and complete-closure axiom audit strictly with `autoImplicit=false`, `warningAsError=true`, one Lean worker. `/usr/bin/time -v` records resource usage per audit. The audit disables elaborator heartbeat counting for the finite inspection loop; that is unrelated to any theorem's computational runtime claim.

Preflight already PASS on the previously built Factor module: 78 declarations/37 theorem constants, standard-only axioms, 9.6 seconds. This checks the inspector API and environment without rebuilding any dependency. It is NOT the full-closure audit result. Generated full plan is `external-audit-plan.json`; the completed passing results are recorded in `external-final-audit-results.json`.

Resource risk: loading the entire final environment and 2569 module metadata may require substantial memory even though axiom traversal is cached. The runner allows one hour per process, records peak RSS/time, emits progress every128 source modules, and fails rather than claiming a partial audit passed. It never installs software or changes pinned source, build state, AGENTS or frozen packets.

Full-selector syntax probe also PASS: the generated 2569-module name selector was exercised while importing only the already-built Factor+LeanCompat subset (two modules), checking 84 declarations/43 theorem constants. This exposed and fixed the default elaborator recursion-depth limit for the large literal; the final audit explicitly sets `maxRecDepth 20000`. The probe does not substitute for the complete-closure audit. Its second strict run exited 0 in11.4 seconds; `external-array-probe.log` and resource file record it. Prepared generated files and manifest were regenerated after this correction.

Configured Main-wrapper assessment: recursive original-source import traversal finds 3091 source modules in Main's full closure, of which **522** are outside the live Final closure. The exact extra module list and pin are in `external-main-extra-plan.json`. This is a substantive additional execution branch, not a one-file wrapper. It was not launched under the instruction to build Main only if the increment is small/useful. Direct verification of the exact requested endpoint in Final is kept separate and prioritized.

The full runner additionally verifies each original Lean source against its exact pinned Git blob (not merely against the build's recorded source hash), and verifies the comparator `.lean`/`.json` and docs/378.md against the pinned tree. The manifest records the runner hash and each complete artifact record includes the source commit-blob hash. The state compiler and commit must match the prepared explicit compiler/pin. These checks guard against a dirty checkout being mistaken for the pinned proof.
