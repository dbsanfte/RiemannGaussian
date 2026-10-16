# Independent review: structured determinants and signed shifts

2026-10-15. Algebraic review by the coverage investigator. No general acquisition lower bound or new Lean verification is asserted.

## Structured determinant report

Verdict: PASS on the frozen final bytes pinned below. Both the off-diagonal block-size wording and the corrected historical native provenance were incorporated and checked.

1. The Cauchy determinant signs match C_ji=1/(x_j-y_i). The diagonal displacement equation is rank one on its legitimate unit-denominator domain. At an actual collision, the corresponding all-ones generator equation reduces to 0=1 in a hidden field, so no such matrix exists there. Canonical full-grid collision coverage makes this failure unavoidable for the proposed Cauchy interface, not merely a possible bad input. This rules out calling that promised-domain interface; it does not rule out a different division-free determinant.

2. The companion representation is correct: with C_H=Z-h e_last^T, M=G_L(C_H) commutes with C_H, hence ZM-MZ=h e_last^T M-Mh e_last^T, a sum of two outer products. Thus displacement rank is at most two over either hidden field regardless of collision. Since C_H^k e_0=e_k for 0<=k<J, M e_0 is exactly the remainder coefficient vector of G_L modulo H. Knowing a rank bound does not acquire these entries or the displayed generators. This is an interface information gap, not a lower bound against all generator-evolution algorithms.

3. Distinct-node Cauchy submatrices have full rank by their nonzero determinant. Therefore small displacement rank cannot be substituted for small exact quasiseparable rank. For an n-by-n square matrix strict off-diagonal block size is at most floor(n/2); the frozen final report correctly says Theta(min(J,L)) subject to available block sizes.

4. Denominator clearing gives E_ji=prod_(k!=i)(x_j-y_k), and its displacement RHS g_j=G_L(x_j) is correct. It stays defined at collisions but its generator includes the unpaid long values. The report correctly avoids treating that generator as supplied for free.

5. The summed subgroup/block estimates in section 6 are costs of that chosen evaluator, explicitly not matching lower bounds. The warning that a new nearlinear oracle changes the situation is essential and is present. The canonical reduction's target/interval bisection is therefore compatible with this report.

6. CORRECTION 2026-10-15: later historical inspection found that SemiprimeSeedSumAcquisition.common_seed_sum_exact ALREADY compiles every global first-current hit sum identity on a padded interval covering [0,2m^2+2). Its long_public_route_seed_batch_succeeds compiles the original seed arithmetic recovery. Earlier review bytes incorrectly called this a new classical extension because only the earlier PhaseSumRecovery endpoint had been checked. The final structured report now correctly credits this later native endpoint; the distinct new interface is only restriction-stable scalar-oracle bisection, not arithmetic coverage or sum recovery.

## Primary paper checked locally

Reviewed downloaded primary Khichane--Neiger v1 manuscript, title Matrices with displacement structure: a deterministic approach for linear systems and nullspace bases, arXiv:2603.02425v1. The PDF title page is dated March 4, 2026, and its arXiv stamp reads 2 Mar 2026. Local source pins:

- structured/khichane-neiger-2026.pdf SHA256 6f8256f25eeb11c1dc3b67e8f91bd1c58b8c3f40f2261c5c268738fb7e51b4bf
- structured/khichane-neiger-2026.txt SHA256 e817066548ec24611937c23b9c0945960706ffcd0d20b5e416926c7e47f78fbd

Text lines 80--107 explicitly assume an effective field and an invertible displacement operator. Theorem 1 at lines 148--155 gives deterministic O(alpha^(omega-1)(M(m)log(m)+M(n)log(n)^2)) field operations for the stated operators. This implies the simplified soft O(alpha^(omega-1)(m+n)) statement using fast field polynomial multiplication. Algorithm 5 at lines 1392--1409 explicitly takes disjoint, repetition-free x,y and computes f_y inverse modulo f_x. Thus the report's applicability/domain and dimension-accounting claims are supported by this saved primary source. No claim about every later manuscript revision is made.

## Signed-shift interface report

Verdict: passes within its explicitly labeled-factor contract.

The endpoint identity (1-z)P_L(zq)=(1-zq^L)P_L(z) is exact. Interior zeros can cancel from the signed ratio, so cheap endpoints do not acquire either original long product or its denominator-unit certificate.

The plateau proof is exact for arbitrary finite signed stencil weights: on the common intersection every interval indicator equals one, giving multiplicity sum_s c_s. When that sum is nonzero, at least the common-interior length of distinct labels survives; when it is zero, those labeled collision events disappear. Bounds about B explicitly acquired denominator labels are valid for this factor-support accounting. They do not exclude identities between unequal numerical factors, algebraic compression, or a new succinct denominator evaluator, and the report expressly makes those exclusions.

The actual-source congruence E_j=N(1-j^(-1))^2 modulo m is correct with either integer carry convention. Its fiber has at most two nonzero tags because N is nonzero modulo odd prime m. An exact same integer ray modulo m^2 must lie in such a low-digit fiber. The report correctly refuses to infer disjoint local q-orbits: when gcd(m,ord(gamma))=1 the q and gamma subgroups are identical. The antipodal low-digit difference is -4N/j, nonzero, so this pairing does not supply same-origin signed cancellation. Pair-dependent reciprocal normalization is a separate exact product identity with its phase retained.

No mathematical corrections to the signed-shift report are requested. Neither reviewed report pays the core query acquisition.

## Final reviewed artifact pins

- structured/report.md: SHA256 29d79b3e23b986bdd73ffa2d0df3c204c02cc09d4a0133660cfee517e4b315e2 (author declared frozen; final sections 3 and 8 re-read).
- cancellations/signed-shift-interface.md: SHA256 b004461d88b37ecc2ac0ddfdfa6ef79da17ec532341a5d3c933b62de0d6f9f5d.

Verdict applies to these exact bytes. No outstanding substantive correction requested.

Final historical-provenance correction checked against SemiprimeSeedSumAcquisition.lean lines 42--49 (padded bounds), 90--150 (common_seed_sum_exact), and 450 onward (actual long route source/recovery). Coverage/native-pins.json now includes that module plus the routing/controller sources. The coverage report itself contains an explicit correction notice and no claim of a newly compiled or newly proved arithmetic sum theorem.
