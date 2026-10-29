# Executable enumeration frontend and enum-parametric counter

Four new modules close the `defaultEnumerations` dependency for the explicit indexed network and actual typed macro graph. No frozen source was changed. They do not yet make the entire source row/interpolation/certificate/counter execution computable.

## Actual data and theorem interfaces

* `SemiprimeFiniteEnumerations`: literal ascending Fin lists; transported, disjoint-sum, Cartesian, dependent Sigma and dependent function lists. Each is a `FiniteEnumeration`, hence carries actual nodup/completeness proofs. Lengths are proved for all combinators, words (`r^Q`), universal types (`r^(2Q)`), and original indexed incidences (`sum arity`). `sourceEnumerations` assembles all lists required by the source constructor, with zero-first word order. `indexed` specializes to physical dependent port indices. None of these data definitions is noncomputable.
* `searchWords`, `searchPacking`, `searchWordsCounted` call the actual vendor `Packing.computedWords`, `computedPacking`, and counted word search, using explicit supplied lists and exact rational scales. Their equality to the source semantic wrappers is definitional, not an asserted algorithm contract. The counted theorem is the source bound `indices.length * (2*wordTail.length*(terms.length*alphabet.length^4))` for its charged score-entry calls. It is not a primitive bit-time theorem.
* `SemiprimeEnumeratedCounter`: `layout p en`, `nodeDesign p en`, `problem ... p en`, rank/summary cardinality bounds, constructed prefix count/search soundness/none/query-count theorems accept the actual `EnumerationData p`. `indexed_prefix_count` instantiates the executable indexed lists directly. No equality with classical `defaultEnumerations` is required. This semantic layer remains noncomputable where the inherited row/interpolation/certificate definitions do.
* `SemiprimeMacroFiniteEnumerations`: explicit constructor-code equivalences and lists for `WordSignal`, `FlagSignal`, arithmetic `Vertex`, `BitSignal`, literal `Edge`, `SubdividedVertex`, and its dependent ordered port incidences. `source r t digits palette Q` assembles the actual typed public graph enumerations. No arbitrary `Fintype.equivFin` reindexing is used. These lists instantiate the preceding enum-parametric interface directly.
* `SemiprimeMixedRadix.decode`: a list-free equivalence `Fin (product bounds) ≃ (i → Fin(bounds i))`, recursively using `finProdFinEquiv.symm` (division/remainder) and `Fin.consEquiv`; zero radices and empty domains are covered. `nested` handles the group/row summary box without allocating the possibly exponential list. `filtered` turns a filtered supplied vertex list into a concrete `Fin length ≃ head fibre` via get/idxOf, for the executed row selector.

## Actual execution checks

`ComputablePackingSmoke.lean` executes the source word-search and complete-block/leftover packing on an indexed two-variable one-factor two-port diagnostic. Its source universal alphabet has 16 entries and its score-term list 12; it produces concrete head words, zero complete blocks and the two literal leftovers. This tests the actual compiled search path, not only constructor lengths.

`FrontendSmoke.lean` evaluates actual macro graph constructor lists at `(r,t,digits)=(1,4,1)`: 53 word signals, 534 literal subdivided edges, 314 subdivided vertices, 1068 ordered incidences. It decodes mixed radix `[2,3]` code 5 to `[1,2]`, and encodes the all-2 two-group singleton-row ternary summary to 8. These are structural checks, not factoring fixtures or a cost benchmark.

Replay from `/home/dbsanfte/riemann/formal`:

```
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true /tmp/semiprime-counter-frontend-20261027/ComputablePackingSmoke.lean
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true /tmp/semiprime-counter-frontend-20261027/FrontendSmoke.lean
python3 /tmp/semiprime-counter-frontend-20261027/strict_recheck.py
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true /tmp/semiprime-counter-frontend-20261027/CombinedFrontendAudit.lean
```

## Paid sizes and remaining execution obligations

The source constructor explicitly allocates `r^Q` words, `r^(2Q)` universal types, and `M^2+Q*v^2` score terms. These sizes must be charged under the schedule; no summary box of exponential cardinality is allocated by the mixed-radix decoder. The exact rational score search is compiled, but the score-call bound alone does not bound all list traversal, lookup, arithmetic bit height, or memory allocation. The explicit macro constructor lists are polynomial in the physical graph parameters; derived Fintype dictionaries are only used for cardinal constants and theorem interfaces, not to replace these lists.

The following are still separate exceptions, not erased by calling the enum-parametric theorem:

1. `SemiprimeSourceLayout.universalLayout` uses source universal swap-polynomial interpolation and its unit/interpolation interfaces, before block assembly and owner pullback. `sampleUnits` goes through `NodeUnits.ofField`. No newly proved compiled interpolation implementation is supplied here.
2. `SemiprimeLayoutSelection.selectRows` explicitly invokes `Classical.choice` on `exists_actual_row_basis`. Skein's executed original-row selector is a separate new task. `filtered` now supplies its constructive head-column enumeration, but does not itself select rows.
3. Existing `sampleEquiv` and selected certificate representation/readout use noncomputable finite equivalences/choice. Supplying explicit enumerations at the packing frontend does not claim these later choices have disappeared. The new summary mixed-radix API supplies a constructive code space, not a proved replacement of every inherited certificate operation.
4. The old counter value remains a semantic finite expression; full loop refinement and primitive bit/space assembly remain distinct. The new prefix-count/search correctness uses explicit `en`, without demanding equality with the old default layout, but is not an extracted machine or a final exponent theorem.

## Gates and provenance

All four modules strict-compile with `autoImplicit=false` and `warningAsError=true`. Combined ordinary-root `#lint+` runs all 15 linters for all four namespaces. The all-generated transitive audit checks 139 declarations, including 79 theorems: no project axioms, only `propext`, `Classical.choice`, `Quot.sound`. `strict_recheck.py` independently emits isolated objects and verifies source stability and byte identity with the dependency objects.

Original combinators and adapters are new repository code under the standard Apache header. Vendor algorithms are imported, not copied: `vendor/openai-semiprime/OpenAISemiprime/Algorithms/SubexponentialSAT/Subexp/ConstructivePacking.lean` and `.../Packing.lean`, retaining declaration namespaces and the previously pinned OpenAI source provenance. The enum-parametric theorem layer adapts the existing local `SemiprimeConstructedCounter` proof to supplied enumeration data. No new algorithmic claim is attributed to the external SAT endpoint.

## Executed node-design and actual fibre-packet connection (final extension)

Three further new modules close two downstream choices for the new indexed path:

* `SemiprimeIndexedNodeCertificate.Data` uses `Group=Fin r`, `Local g=Fin(h g)`, `Index g=Fin(m g)`, literal integer matrices `C`, entry bounds `W`, explicit original-variable grouping and native off-group locality. `certificate d` uses the original signed summary boxes and the executed `summaryRepresentative` scans, rather than `firstRepresentative` or a default Boolean decoder. Its finite/equality fields are explicitly canonical Fin instances. `fibreAt_native_spec` proves that root's actual cached representative/group scans (`FibreArrayExecution.fibreAt`) produce the low coefficients of the existing native fibre-packet summand `term d T correction S y`. The required callback specification is only the *local group callback*; it is supplied by the separate `NativeGroupExecution` refinement. Actual forced membership is in original coordinates via `d.grouping.symm`.
* `SemiprimeExecutedNodeDesign.data` is an ordinary **compiled def**, with no blanket `noncomputable section`. It takes the supplied source `Layout.Data`, explicit variable enumeration and literal entry-height theorem. It filters each source head, computes selected original rows using `selectedRowsWithColumns`, retains their unscaled integer entries, and uses the actual integer-kernel locality to prove the native rational row span. Thus neither actual row selection nor representative search is chosen in this new data path. `selected_count` proves its selected list length is the actual original rational rank. The source `Layout.Data` itself remains an input; this module does not implement the universal interpolation row construction.
* `SemiprimeIndexedFibrePacket.packet_eq_sum` identifies the sum of those executed summands with **the existing** `CounterCompose.fibrePacket`. The proof explicitly reconciles exhaustive finite instances in the local-word sum and decision procedures in branch conditions. It neither assumes a whole-packet value nor substitutes an unrelated finite expression.

The earlier four-module exception list describes the inherited `EnumeratedCounter.nodeDesign` wrapper. The new executed-design branch now replaces its original-row selection and representative choices. Remaining source-row interpolation, sample reindexing where used, explicit cached materialization, full finite-loop composition and primitive bit/space accounting must still be stated separately.

`Data` fields are function suppliers. In particular repeated accesses can recompute filtering/elimination; no caching-once claim is made here. Root's runtime array wrappers must materialize/reuse node matrices or charge this polynomial overhead. The mathematical `certificate`/packet layer retains `noncomputable` declarations where inherited measurement/finite-sum interfaces require them; runtime representative search and selected matrix data are separately actual compiled functions. No new exponent theorem follows solely from this frontend.

Final combined gate: all **seven** modules strict PASS, ordinary-root 15-linter PASS, and every-generated transitive standard-axiom audit PASS: **190 declarations, 102 theorems**. The final seven-module audit is `CombinedNativeFrontendAudit.lean` / `combined-native-frontend-audit.log`; the original four-module audit is retained as an earlier valid stage. The independent strict recheck and source/object manifest cover all seven.
