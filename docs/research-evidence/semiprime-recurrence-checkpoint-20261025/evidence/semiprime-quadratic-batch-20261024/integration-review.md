# Independent integration review: quadratic-batch packet

Verdict: PASS after the balanced-main-prefix availability correction. No further corrections required. No source, draft or shared repository file was edited by this integration audit; the reviewer updated only its own review artifacts.

Exact draft SHA256 pins:

* `journal-append.md`: `e7749bce6e0230705666d47bf93ce7a2b35d72770ce1af90856e51a36abdaa4a`.
* `agents-append.md`: `bc6e5370ca150ca16092b143dde224cfcd9bb1a5619c9c9014860dc9e0fe98e3`.

Exact final source SHA256 pins:

* `reciprocal-recurrence.md`: `4642b776f4c72a42a5a2c20beac07b25dbff0a21ba9f3569cd495108d4801f1b`.
* `quadratic-product.md`: `69d3bbc5a0813ba7a5a5cd40e315b250f51d209b82e7085073a9aed52b607eb1`.
* `filter-reciprocity.md`: `55c5961f6391d3acf76050d4bbdfd725edb0fd007b5cd6d62ab814681c3efd25`.
* `centre-alignment.md`: `8c2d18c27951d5b07c67fcc852f4cd0d7d688d8de41e5429658f5d935cf011e5`.

Independent final reviews are PASS: reciprocal review SHA256 `f73675dd2b712132a82a9ae492b1f80a4f9ec7912256f2c48ac2acd8da31b033`; quadratic-product review SHA256 `a711c16cc08aaf99aa4b8270ab109f806dbd6c45b9b572f1449359f9c017ce3a`; filter review SHA256 `bc65ad6ff7658fccbf5b97f6fd30f15ed8d9392dbe51f341dec4bcdb7361533b`. The final centre-alignment independent PASS review has SHA256 `1f6b1ce7a32f5cf2421fa7500f5001ecb6589d743e9376518fd2e8b246a98963`. This audit read the actual reports and reviews, not just their verdict labels.

The reciprocal quotient, relative norm and changing involutions are faithfully integrated without augmented-point separation assumptions. The degree-J generators and top-m coefficient acquisition use actual S_G evaluations and only certified small integer divisions; they do not invert possibly unguarded 1-q^(mr). Augmentation supplies the actual bottom coefficients and normalization, but no middle remainder or amplitude. The drafts preserve that exact boundary between acquired data and the unresolved terminal resultant.

One necessary availability correction was identified during this audit and is now present in both source and drafts: the full horizon2H+2 need not admit balanced factors m,G. The executed main prefix is L0=2H, with m=k,G=2k and reciprocal parameter a0=q^(1-L0). The two remaining original factors are acquired at indices2H,2H+1 in soft J. The main augmented resultant is a KNOWN UNIT times the main product squared; multiply the actual tail squared to obtain the full-query square. The main reverse-index map is L0-1-i. The optional repaired horizon3H+2 uses main3H and G=3k. These corrections prevent silently reusing the full-horizon reciprocal centre after clipping. All guards and index consumers remain valid.

The uniform original-grid distinctness argument uses the global beta-order product, the actual delta span and m>=6, without inferring local unit separation or augmented-grid distinctness. Its lower-cost statement applies only to full explicit output of the JG points and degree-m baby coefficients. Both drafts expressly exclude an implicit-solver or early-factor lower bound. No generic recurrence, scalar-query or factoring lower bound is claimed.

The theta section explicitly resets the repaired horizon to3H+2. Negation preserves the low-a mask but interchanges colours, with varying centre beta^[2(N+a')]q^mu. Both finite-theta Laurent identities and their guarded range2L are correct. General paired transport retains four boundary factors and no zero denominator is inverted. Equality of actual centres forces equal(a',mu) via the global beta-order bound. The reviewed centre-alignment addendum strengthens the older at-most-O(1) matching corollary to ZERO actual matches: at the nonsplit side the odd scalar beta order divides r-1 and the odd norm-one W order divides r+1, so they are coprime. The W order bound forces mu=-1 from hypothetical C*q=1; global equality then forces D_beta to divide N+a' and hence the positive P+Q+a'-1<H², contradicting D_beta>256H². This uses no split-side scalar/torus coprimality and no cross-prime W coprimality. The coefficient primitive therefore makes every actual centre test proper-factor-or-unit, with no guaranteed factor discovery. The final drafts correctly state this limited literal-alignment exclusion, superseding the older weaker matching corollary; it does not exclude another joint evaluator for varying centres. Mixed starts and all required outputs remain paid at the retained query clock.

The self-dual enlargement treats1-u as a NONUNIT auxiliary label, never as a native tag or character value. The acquired two strips have O(k) labels and their two symmetric products both equal A_eta B_eta; they do not identify or cancel A_eta. All seven actual carries and the original minus-colour rows retain coverage. Extra plus-type leaves have actual near-N exponents with delta in(-6H,2H), and the separately proved bounded factor-sum consumer handles them. Their unit separation is correctly proved using pi^d-1 dividing the certified unit q^d-1 for |d|<8H, rather than inferred from distinct norms in split components. The easy boundary polynomial is acquired cheaply, while its long interval-unit certificate is still charged at soft k^(3/2). Simultaneous explicit closure under both reflections has all H labels, a statement about that particular closure only.

The integration credits prior reciprocal/Dickson folds, antipodal centres, canonical rows and coefficient-action primitives. It preserves the covered family, all original or proved auxiliary witness maps, and the unchanged soft(J+sqrt(JL)) complete query. It claims neither a new factoring exponent nor completion of the executable/Lean bit-cost theorem.

Both shared-document baseline prefixes were independently checked against continuation-baseline.json read-only. The final append-capable validator was inspected but not run by this reviewer; verification of all inherited270 manifest members, source/cache pins and the eventual exact append remains the parent's validator step. No new claim of executed preservation beyond the prefix checks is made here.
