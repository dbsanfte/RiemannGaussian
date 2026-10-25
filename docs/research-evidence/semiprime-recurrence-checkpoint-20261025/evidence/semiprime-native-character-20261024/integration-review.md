# Independent native-character integration review

24 October 2026. **PASS for final pinned drafts.** No source/repository or draft edits by this reviewer. One requested exponent clarification in the agents draft has been incorporated by root; no required correction remains.

Exact draft SHA256 pins:

- `journal-append.md`: `bb32f75d6a5e2da2630e6f5598f0f18563abf4311584ba137dc46d9cdb555dc1`.
- `agents-append.md`: `4cd7b79c7e1557d57cdc639be1f110f2a36d8f322c4ad5b787fb71c9d5e22839`.

Compared against all final reports and their exact independent reviews:

- Composite source `66795af6eae4e0cde23b6e84a6beb7ae18a656e41bdf9f94d739c83f3cbccb74`; review `d6df6253b443d6b92e47cc59df2c6fe386408647c48f755747d09291a8d78ca6`.
- Acquisition source `83bd40ae27d975320566827bba50ae73d63464218d2993bfc5b226e60e7749a7`; review `88af4e6fb0df963ce6901ad3406675dea9786e68e2f01b7fe2c27de76fa910a3`.
- Literature source `24ec2dd1529a9c36070df12e880347c21c8841e7367eaa711c0bd7cfcf601c02`; review `0ae57466adb44e9b80fcf8ea797012fb8fd3bc4004bd5a71a3da430237e4f613`.

## Composite source and actual cost

Both drafts correctly close only the conductor-supply obligation by choosing ell first and setting even composite k=ell-1. Public factorization, primitive-root tests and logarithm enumeration retain soft-k cost. They use unit tags and exact integer quotients, not a field or two-root assumption modulo k. Coprime-order preparation, its exact-common-order branches and the actual post-H-power q screen are preserved. Neither scalar order preparation nor the prime-conductor supply is assigned to Gauss-component orders automatically.

The quarter refinement is faithful: E_j=a_j(j-1)²+k(D_j+b_j), with the second parenthesis even, proves divisibility by four for all even k. Direct quarter powers preserve every scalar hit because beta has odd local orders and both companion factors are units. The q-quarter guard and original recovery follow as in the reviewed source. This changes no J or L. General odd content extraction is explicitly guarded, composite fibers may be larger, and the corrected Kronecker issue is limited to v2(k)=1 rather than the trivial squared 2-character at v2(k)=2.

## Packed phases, primitive norm and actual input requirement

The even-order Gauss phase D=e0+ell*epsilon*(1-e0) and shared antipodal pair formula are correct. The native raw target and seed have augmentation one, so every raw difference has zero augmentation and its FULL cyclic norm is always zero. The drafts reject that full norm as a detector even on no-hit restrictions.

The primitive Ramanujan projector, public CRT unit-group generators and norm-doubling recursion do acquire a scalar norm of ONE ACTUAL supplied rank-k vector in soft k. Coefficient permutations, ring multiplications, fixed-subring scalar extraction and unit k/phi(k) factor are properly charged. No inverse of V is used. The text does not turn this into acquisition of the missing packed vector, all weighted rows, or the long row/seed product. It also does not infer original-beta recovery from a saturated primitive norm.

The orbit test correctly transforms the seed as well as the weighted target. Replacing that varying native family with one common orbit would change the query; no such substitution is credited as covered. Multiplicative Stickelberger data remain distinct from mixed unit-minus-one data.

## Grade-zero Frobenius and paired recovery

The group-ring factorization expands correctly. Crucially both drafts retain the final source's correction: P-rho_j acts on the ZERO-GRADE intermediate u^(Q-a_j*rho_j), because Q-a_j*j=0 modulo k. It is not stated to annihilate raw Gauss u, whose Frobenius retains an auxiliary additive-root phase. Private P,Q are proof variables, not acquired group-ring inputs.

The norm-one normalization preserves the own witness through the actual even multiple (P-1)(Q-a_j)/2 and gives R_j R_-j=Q0^tau_j. Its shifted pair product still needs the mixed trace. Beta coupling gives the exact division-free ideal identity (f,bar(f))=(f,G_beta). Only a conjugate-PAIRED hit at the SAME original row/index forces the scalar beta condition. Different leaves or unpaired primitive-norm zeros cannot be combined into that certificate, and neither draft does so. The scalar augmentation of the safe coupling returns the old covered scalar query.

## Single-quotient completion and powered-hit guard

The exact rewrite is T_j^j=q_G^c_j*rho_(j^-1)(C_j)^N*C_j^(-a_j*j). The corrected agents draft now spells the last exponent explicitly, avoiding the former ambiguous compressed `-aj`. Its sign, extra j and c_j expression match the final source.

The actual histogram/prefix stream performs k updates each costing soft k, followed by row powers/permutations and one live packed product. Thus fixed-index time soft k² and live memory soft k are correctly distinguished. This is an acquired overbudget scalar value for the chosen powered differences, not a general output-size lower bound or a complete long-interval evaluator.

Cancellation of the extra j is tied to PAID BOTH-local-order k-rough cleaning of the original scalar beta0, with its kernel and order/q screens. Unit j modulo k alone is expressly insufficient. The paired beta-coupled powered equality then permits cancellation of 2j, returns an original bounded scalar leaf, and uses its proper decoder. Raw Gauss saturation is never assigned that bridge.

## Classification and preservation scope

The final classification is faithful: conductor-first composite setup, a zero-safe one-vector primitive norm and a same-leaf paired scalar bridge are supporting constructions. They do not acquire the full weighted difference family at soft k. The original guaranteed scalar query remains soft(J+sqrt(JL)), at most soft k^(3/2), with no new whole-input exponent or completed bit/Lean claim.

Repository-prefix preservation, the 270 frozen entries and concurrent RH work are the root continuation validator's operational responsibility. This audit verifies mathematics, exact final pins, hypotheses, cost and recovery scope; it does not perform or certify the repository append operation itself.
