# Actual counter packet heights

New module: `RiemannGaussian/SemiprimeCounterPacketHeight.lean`. Strict compile PASS; root-import 15-linter audit PASS; every generated declaration standard-axiom audit PASS: **54 declarations, 43 theorem constants**. Logs: `packet-build.log`, `packet-audit.log`; auditor: `CheckPacketHeight.lean`. No prior source/evidence files were changed.

## Actual native input and output

Let n=card V, m=sum_e arity(e), delta=rowDenominator(Q,R), and let B be the original owner-fibre bound. The constructor supplies integer row polynomials with common delta, degree at most R, and coefficient bound

`Brow = B*2^rowNumeratorExponent(Q,R)`.

At an actual integer sample t with |t|<=T, define

`Bshift = shiftBound(R,Brow,T)`.

`inputNumerator` constructs the literal integer corrected input: its constant uses Boolean base x, while its positive coefficients independently use U. `inputNumerator_map` proves it maps to delta times the **actual** fibre frontend, and `inputNumerator_bound` gives n*Bshift for every coefficient. `builtLayout_correctedPort_representation` derives its row premises from the actual searched-packing/complete-block/original-owner constructor; it does not assume a desired port/output height.

`termNumerator` then runs the existing integer streamed tensor numerator recursion for each local factor and multiplies the results. `termNumerator_map` proves the common denominator is exactly delta^m. Finite sums do not multiply it again. A coefficient below precision J>=1 has integer numerator envelope

`Hterm = J^(card E) * [J*(delta+2n*Bshift)]^m`.

The actual table hypothesis is integer entries of absolute value at most 1, covering Boolean zero/one entries. Arbitrary rational callbacks require additional input hypotheses and are not silently covered.

## Actual raw/node/Taylor packet

`rawPacket_expansion` proves the actual separated raw polynomial is a finite signed sum of native corrected factor products, including support cutoff, U⊆S, forced S⊆x and Möbius sign. Its logical coarse index space has size 8^n (all S,U,x triples); invalid leaves have zero weight. This is used only to bound integer magnitude, **not** to execute or charge an 8^n algorithm. The executed menu still has the separate proved Cq count.

`built_rawPacket_representation`, `built_nodePacket_representation` and `built_globalTaylor_representation` give, for every k<J,

`Representation(actual coefficient, delta^m, 8^n*Hterm)`.

The global Taylor conclusion follows from the previously proved actual packet identity, with native row degree supplied by the constructor. No desired global H height is a premise. Truncation keeps the same denominator and envelope. This is the actual polynomial-coefficient input to the Hermite height module; extracting/generating its arrays is not hereby treated as free execution.

## Partial separated accumulators and padding

`signed_terms_representation` and its native-constructor wrapper cover **any finite subset** of signed terms (weights abs<=1), with a factor-dependent Boolean base. Such bases can differ for different assigned groups. Their bound is `s.card*Hterm` over the SAME delta^m, without relying on eventual cancellation or the final logical assignment sum.

`groupValue_corrected_product` identifies the actual group value as a selected-factor product. `groupValue_boolean_base` covers every actual Boolean representative/update, using the explicit assignment equivalence; it does not require a representative to satisfy forced bits or to match other groups' representatives.

`built_masked_terms_representation` covers partial selected-factor products and finite signed sums of them. Its proof substitutes constant-one tensors for inactive factors while retaining their original arities. The integer numerator therefore contains the padding delta^(remaining incidences), with no inverse or denominator growth from sums. This is an algebraic representation used for height, not a proposal to execute inactive tensor evaluations. Group and support partial sums can be indexed by their actual finite loop records; repeated numerical values must retain distinct records so multiplicity is not lost. Labels/fibre choices can be included in that index type, and the cardinal multiplier accounts for them.

For example, a conservative partial separated expansion uses at most Cq times the full summary-box cardinal times 2^n assignment records, with partial-factor masks and zero/one forced/measurement gates. Its logarithm is polynomial in the public dimensions (and the already proved summary bound is stronger). The module gives uniform finite-subset representation and actual group frontend identities; it does **not** yet provide a full tracked interpreter theorem matching every Python loop prefix to its record set. That execution attachment and finite index-cardinality bookkeeping remain separate, rather than being inferred merely from final raw-packet cancellation.

## Explicit logarithmic envelope

`rawBound_le_power` formally bounds the actual numerator envelope by 2^E, where

`E = 3n + clog2(J+1)*card E + clog2(J*(delta+2n*Bshift)+1)*m`.

`packetDenominator_le_power` gives

`delta^m <= 2^[(R+clog2(Q)*Q*(Q+1))*m]`.

Together with the constructor's explicit row exponent and shift bound, these are polynomial logarithmic numerator/denominator budgets in n,m,Q,R,J,T,log(B+1). They contain no universal-alphabet cardinality factor in their exponent. Applying `representation_reduced_bound` bounds the actual canonical rational fields, so the root bit backend can use genuine proved Fits bounds.

The remaining whole-execution obligations include the explicit array/frontend correspondence, all index/loop cardinalities for the chosen implementation, row-construction and packet arithmetic intermediates, and primitive bit/allocation/space costs. This module closes actual packet **output** height and supplies cancellation-independent partial-product/sum tools; it does not claim those remaining execution/refinement obligations have already vanished.
