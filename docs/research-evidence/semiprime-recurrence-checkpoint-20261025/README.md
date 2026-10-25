# Semiprime recurrence checkpoint — 25 October 2026

This packet preserves the semiprime scratch evidence accumulated after the fifteen existing frozen packets. The complete scalar-catalogue algorithm remains at **soft O(k^(5/4)) = soft O(N^(5/24))**, where k = Theta(N^(1/6)). The guaranteed soft O(N^(1/6)) objective and its full Lean bit-cost proof remain open. This construction does not improve the known general deterministic N^(1/5) factoring comparison.

The archive contains 604 verbatim internal reports, reviews, scripts and historical metadata files. Its provenance ledger fingerprints 219 external-paper/full-text/binary/source-cache files without copying their contents, and references three already-present repository evidence files. All 376 inherited pins were checked against their source bytes. The fifteen prior packet manifests and all 270 of their entries remain unchanged.

## Read these corrections before the historical reports

[ERRATA.md](ERRATA.md) records the precedence of corrections. In particular:

- The actual swap-closed catalogue guarantees the **same globally zero index**, and sign symmetry supplies another distinct index. The historical denial of a common index and its accepting review are preserved as superseded evidence. This is a statement about the aggregate polynomial, not one globally vanishing scalar leaf.
- The later “genuine diagonalizer” repackages the already acquired Cauchy factorization in `paired-pencil.md`, Sections 4–5. It receives no new-input or runtime credit. The exact native contraction still needs simultaneous correlated evaluations.
- The fixed-Q joint-mask improvement requires a factorized mask on coefficient indices. A folded mixture over target indices generally supplies a nonfactorized moment sequence instead; no whole-family thin-product input acquisition follows.
- Every varying-quadratic Hecke-strip and class-group-generator consequence is **conditional on correctness of family 029, Theorem 1.2**. The source-scope and endpoint-Mellin audit did not independently verify all representation, local, reflection and other intermediate lemmas. No family-029 Lean link was present in the checked catalogue. Neither deterministic smooth-relation hitting nor complete integer factoring follows.

## Current evidence and exact missing operation

The acquired monic degree-J target polynomial and scalar initialization are paid in soft O(J). For J about k and h about k^(3/2), the remaining operation is to acquire the q-Pochhammer remainder, its zero-safe product, or a useful original collision locator faster than soft O(J + sqrt(Jh)). A short Ore operator, implicit long product, scalar row oracle, ordinary Cauchy matvec or known-zero promise does not itself acquire that operation.

| Subject | Portable report |
| --- | --- |
| Complete scalar catalogue and paid consumer | [scalar-catalogue.md](evidence/semiprime-paired-weighted-query-20261024/scalar-catalogue.md) |
| Shared-index erratum and pair preprocessing | [swap-erratum.md](evidence/semiprime-arithmetic-locator-20261024/swap-erratum.md), [review](evidence/semiprime-arithmetic-locator-20261024/swap-erratum-review.md) |
| Historical common-index error | [terminal-contract.md](evidence/semiprime-scalar-terminal-20261024/terminal-contract.md), [review](evidence/semiprime-scalar-terminal-20261024/terminal-review.md) |
| Existing Cauchy-factorization credit | [paired-pencil.md](evidence/semiprime-paired-contraction-20261024/paired-pencil.md), [review](evidence/semiprime-paired-contraction-20261024/paired-pencil-review.md) |
| Later Toeplitz presentation and padded stripe | [diagonalizer.md](evidence/semiprime-genuine-stripe-diagonalizer-20261024/diagonalizer.md) |
| Paid scalar Ore recurrence and varying quotients | [ore-recurrence.md](evidence/semiprime-varying-quotient-recurrence-20261024/ore-recurrence.md) |
| Executed q-Newton parity attempt | [qnewton-parity.md](evidence/semiprime-qnewton-decimation-20261024/qnewton-parity.md) |
| All-mask and fixed-Q acquisition | [all-mask-sharing.md](evidence/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md), [joint.md](evidence/semiprime-thin-fixed-q-joint-20261024-36wtj7ic/joint.md) |
| Changed-scale mask ledger | [mask-ledger.md](evidence/semiprime-changed-scale-mask-ledger-20261024/mask-ledger.md) |
| Late no-gain and attribution record | [cauchy-tensor-followup.json](evidence/semiprime-power-selector-20261024/cauchy-tensor-followup.json), [recurrence-advancement-followup.json](evidence/semiprime-power-selector-20261024/recurrence-advancement-followup.json) |
| Conditional varying-quadratic source audit | [audit.md](evidence/semiprime-varying-quadratic-hecke-20261024-aLLfXK/audit.md), [upstream source pins and LF normalization](evidence/semiprime-varying-quadratic-hecke-20261024-aLLfXK/source-pins.json) |
| Independent base-change/consequence review | [quadratic-consequences.md](evidence/semiprime-quadratic-basechange-review-20261024/quadratic-consequences.md) |

The paused 25 October recurrence-literature search had not produced its requested scratch writeup when publication began. This checkpoint does not fabricate that unfinished report or claim an improvement from the search.

## Provenance and reproducibility

- [path-index.tsv](path-index.tsv) maps every captured absolute source path to its portable archive path, existing repository reference, or fingerprint-only disposition.
- [source-provenance.json](provenance/source-provenance.json) records exact byte lengths, SHA-256 values and capture policy. [source-url-index.json](provenance/source-url-index.json) indexes URLs recorded in the captured source context.
- [inherited-376-pins.json](provenance/inherited-376-pins.json) preserves the complete inherited pin union: the locator's 371 source pins plus its five pinned final reports. [frozen-baseline.json](provenance/frozen-baseline.json) preserves the fifteen old manifest fingerprints and 270-entry counts.
- [manifest.json](manifest.json) fingerprints every packet file except itself and the generated validation result. [validation.json](validation.json) records the actual verification run.

The copied evidence retains original `/tmp` references, stale historical status statements and validator paths verbatim. Resolve references through the path index and apply the correction precedence above. Historical `validate-continuation.py` scripts are archival evidence: some contain append modes and original absolute paths. They were **not executed** to prepare this archive. Use the new read-only packet validator instead:

```sh
python3 docs/research-evidence/semiprime-recurrence-checkpoint-20261025/validate.py
```

The validator checks archive bytes and the inherited pin mapping. In this repository it also checks all fifteen old manifests and 270 entries. A standalone copy can validate its own bytes without the original scratch files; `--check-originals` additionally checks every captured original when those files remain available. No Lean build or mathematical experiment was run: this is evidence publication, not a theorem/proof change.
