# Integer layout data to an actual counter NodeCertificate

Sole new module `RiemannGaussian/SemiprimeLayoutCertificates.lean`. No previous source or frozen evidence was modified. This module imports local counter algebra and Mathlib only, not the optional vendor closure.

## Integer-kernel locality really implies rational row span

`clear_vector_denominators` obtains a nonzero integer d and integer vector z with `cast(z_v)=d*x_v` for EVERY coordinate of an arbitrary finite rational vector. It uses the finite localization denominator-clearing theorem over ℤ→ℚ.

`rational_kernel_locality` transfers vanishing of all integer constraint dots to the entire rational kernel: integer dot equalities are proved by injective rational casting, then the target dot is cancelled by nonzero d.

`rowFunctional` is the actual rational dot-product linear map. `row_span_of_integer_kernel` applies finite-dimensional kernel/dual-span theory and evaluates the resulting equality on coordinate unit vectors. It yields actual c_i with `a_v=sum_i c_i*C_iv`. Its ONLY locality premise is integer-kernel annihilation, not the desired row-span conclusion. No converse was postulated.

## Explicit finite summary boxes

`signature` computes integer Boolean constraint dots. `signature_bound` proves the literal radius mW for m local coordinates and entry bound W.

`Summary V I W = (I → Fin(2*(card V*W)+1))` is the FULL signed box. `measurement` actually shifts each integer dot by mW and encodes it by toNat with its bound proof. `readout` subtracts that same radius after rational embedding; `readout_measurement` proves it is the actual cast integer row dot.

`summary_card` and `grouped_summary_card` give exact cardinalities:

`card Summary_g = (2*m_g*W_g+1)^c_g`,
`card(all summary tuples) = product_g (2*m_g*W_g+1)^c_g`.

No opaque finite type of attained signatures is used to hide enumeration cost. Empty groups/constraint families are permitted by these formulas.

## Finite first representative

`scanFrom` is a bounded tail-recursive ordered scan: evaluate the current candidate, return it on success, otherwise decrement fuel and increment index. It stores no candidate list in its recursive definition. `scanFrom_complete` proves a matching candidate in the retained range is returned with its test true.

`booleanDecode` and `booleanDecode_covers` give a finite index enumeration of every local Boolean assignment using the supplied Fintype enumeration; the range length is `card(V→Bool)=2^(card V)`. `firstRepresentative` scans this range and defaults to all-false on empty fibres. `firstRepresentative_valid` proves actual measurement equality whenever the fibre is inhabited. Forced bits never restrict this representative scan.

Important execution boundary: `booleanDecode` currently uses Mathlib's finite equivalence and is a noncomputable semantic decoder in this section. The scan itself is tail-recursive and avoids a materialized candidate list, but cheap bit-mask decoding and a primitive polynomial-space refinement of that decoder/scan are NOT inferred from this theorem. This is an honest finite-search correctness interface, not an unproved small-cost Fintype oracle.

## Actual builder

`ofIntegerConstraints` takes arbitrary finite groups/local coordinates, explicit grouping equivalence from original variables, assigned factor groups, arbitrary finite constraint indices, bounded integer matrices C_g, and exact off-group integer-kernel locality of the supplied rational native rows. It RETURNS a complete `CounterCompose.NodeCertificate`:

* measurement rows are the casts of the actual integers;
* summaries/readouts are the signed boxes above;
* row spans are derived by `row_span_of_integer_kernel`;
* representatives are the actual finite scan and their nonempty-fibre property is proved.

The builder accepts scalar node evaluations, so root can instantiate it separately at each sample with the actual polynomial rows evaluated there. Row restoration/degree concern those polynomial rows and are separately supplied by the source layout; they are not fields of the node certificate.

No supplied row-span witness, desired contraction identity or attained-summary enumeration oracle is required. Selected row cardinality/height and source-layout group load are not assumed proved by this generic adapter: they are inputs for the next source-layout assembly theorem.

## Validation

Strict absolute-lake compilation PASS (`autoImplicit=false`, `warningAsError=true`). Repository and identical scratch `.olean` saved. Five explicit theorem/definition axiom reports contain only `propext, Classical.choice, Quot.sound`. Log `layout-cert-build.log`. Remaining obligations include source-layout assembly/selection, quantitative schedule/range connection, primitive measurement/decoder execution and full counter/factoring resource composition.

Final root-import audit PASS: `CheckCertificates.lean` ran all 15 namespace linters with zero errors and audited all 45 emitted declarations (31 theorem declarations); only standard axioms. Log `layout-cert-audit.log`. No broad build was launched.
