# Independent final integration review

24 October 2026. **PASS. No draft corrections required.** This review was frozen only after the final dense-action source and its exact-hash independent PASS arrived. No source, draft, previous packet or shared repository document was edited; only this scratch review was written.

Exact final drafts:

| Draft | SHA256 |
|---|---|
| journal-append.md | `f76c046ff1c27922b0b797d61675e107387a1f40318f28644e0db2a30f7408e1` |
| agents-append.md | `dbb0538136e36a8b24c5dc047373e82fa300e962e63f5b29295a5a6548c0dc48` |

All three source/review pairs match their frozen bytes:

| Source | Source SHA256 | Independent PASS review SHA256 |
|---|---|---|
| digit-mask-attempt.md | `300952af3de79e56b9c90d4fe02c756e640273a3e2db444010c0c79d7cb07400` | `6181de9f3141f6fb707cc932b724c5db7fe3307c420a4fa5a770aa67ecb9b40e` |
| working.md | `84c8f8036a33637d6c05dc9e444c75f29ee98b4efe68f18d4d3b55b09d3b5435` | `bd3f762d6b87eeed820c4e03c7411a40401b5f2cf24e301941d3ef2029fcf934` |
| all-mask-sharing.md | `5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31` | `131aa98fb6f09ce933d20dddb35045ab5ac3b555e233fabcb15f43413d6eaa02` |

## Positive primitives and their actual costs

The drafts correctly state real acquisition results, rather than asserting that every implicit encoding must acquire all b coefficients. Selected q-factorial prefixes, selected coefficient masks, and one fixed mask's consecutive-clock outputs include their full coarse blocks, dyadic tails, actual starts and constant-one rational-series initialization. All unit divisions have the actual short-q guard; the native b<=L<C range is retained. Sparse mask dimension and output counts are qualified, and arbitrary aliases or zero sums receive no false factor decoder.

The stronger dense action is also correctly summarized. The adjacent-coefficient identity is cleared and does not divide an input coefficient or x. Its rational Newton numerator/denominator and every row-start coefficient are actually acquired. The prefix-sum tree uses the exact left/right composition, and its FINAL dummy leaf (1,1,v_last) removes the unused outgoing transition. Full-row denominators end at an index <=b. The last partial row is explicitly acquired and evaluated, with no extended guard or omitted coefficients. The balanced soft-sqrt-b action includes all H outputs, not a selected-entry oracle or a low ordinary rank claim.

The transpose is paid over the actual ring: nonlinear preprocessing is independent of the input vector, and the reversed operations are linear additions/fixed convolutions/remainders with acquired constants. Zero/nonunit weights cause no inversion. All 6^m inner masks for ONE supplied outer vector follow by actual tensor transforms with geometrically summed array sizes. The balanced b^0.6463 scale includes all those output writes. It is not an assertion that the primary thin layout is balanced or that the varying active-Q outer vectors have been supplied for free.

The complete fixed-Q mixed-radix summand is properly included as a stronger result. Its actual band offset is divisible by the mixed-radix block length and hence by the chosen digit-boundary cut. Low and high digit weights therefore separate without a hidden carry, and their actual vectors have O(sqrt b) entries. Clipping uses the real partial row; short blocks use the selected-coefficient primitive. The final journal explicitly handles bounded b directly. The source's no-full-degree-b-array claim is limited to balanced widths; extreme D=1 may acquire all row starts at the correctly charged H cost. No unbalanced bound is silently upgraded by the drafts.

## Whole-encoding and terminal boundary

The AP-residue primitive includes its actual transition-polynomial construction only in the small-stride branch, uses no division by a sum, and avoids an extra final transition. It is not charged once for every residue or every native x. Its exact active-Q/outer-box forms remain separate from the sparse inner-mask and all-inner-mask results.

The source's actual singleton/negative-pair inner masks and outer ternary boxes are represented safely. A single active Q collapses the bilinear identity to its matching singleton inner products; the paper's multi-Q saving is not imputed to an isolated mask. The strict full-preencoding output count is explicitly for m>=1. It counts that literal phase, not distinct values or a lower bound against a lazy wanted-leaf union. Neither draft claims that the sum over different grid-assigned Q has been contracted.

The exact native block convention is preserved, including V_j^b, arguments q^(ab)/V_j, the literal tail and original row/block/index labels. Auxiliary pure-clock, mask, partial-output or box zeros are not original witnesses. Both explicit terminal-output reductions retain their unpaid costs: partial matrix entries still require weighted column contraction, and diagonal folding moves the native weighted input into an unacquired left operand.

For the original P_b(y), BOTH paired vectors u_rho=y^(D*rho) and v_r=y^r move with the SAME y. The drafts clearly identify their simultaneous diagonal bilinear evaluation or restricted product as the NEXT missing operation. Fast action for one vector, one outer combination or one fixed-Q term is not presented as that whole-family theorem. The guaranteed completion remains soft(J+sqrt(JL))=soft k^(3/2), with no one-sixth factoring, full executable/Lean composition, generic lower bound or absolute novelty claim.

## Pre-append preservation

Read-only checks against this packet's continuation baseline confirm current AGENTS.md is unchanged at 22466 lines/1440918 bytes, SHA256 `f58a14dbc974381e1b8e27da4f5f2cd7f0b0b73f0cee0617fdefce8964bc671c`, and the journal is unchanged at 40870 lines/2152265 bytes, SHA256 `5ac94ed4edba263691e63182d9074a2951c815d608fd959f7e7add44d5e6ebc6`. All fifteen frozen manifest hashes and all 270 frozen entry byte lengths/SHA256 values still match. These are pre-append checks; the root validator must verify the later append/prefix result. The final integration is ready without edits.
