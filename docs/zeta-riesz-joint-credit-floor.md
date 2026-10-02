# Keep the whole phase credit in the signed-energy floor

`ZetaRieszJointCreditFloor` proves the missing cost comparison and combines
the previous whole-carrier phase credit with every independent pair payment.
This strengthens the current whole-floor inequality. It does **not** prove
the remaining arithmetic budget, a floor of `-399/5000`, or a zero exclusion.

The distinction between cost and carrier matters. A lower bound
`Re(P) >= -cost - error` alone does not let us add a credit to its right side.
The previous complex projection proved

$$
\operatorname{nativeCost}_j+\operatorname{nativeCredit}_j
\le\operatorname{negativeCost}_j.
$$

The new `core_negativeCost_bound` supplies the other necessary inequality:

$$
\operatorname{negativeCost}_j
\le\sqrt{\max(E_{\rm remaining,j},0)\,129N_j/200}
+\operatorname{paidPrice}_j.
$$

The proof keeps the **same** whole-population adverse cutoffs throughout.
It separates the diagonal, large common factors, near labels, phase periods,
the stronger common-factor payment and the two wider phase payments. Each
pair difference is priced once. The entire remaining signed energy is kept
inside one square root, including all cross-count and cross-period terms.
No positive reserve size, orthogonality, or energy monotonicity is assumed.

Combining those cost inequalities with `native_floor` gives the checked theorem
`eventually_joined_floor_with_credit` for the original `joinedPhysical`:

$$
\boxed{\quad
\Re P_j\ge
\operatorname{nativeCredit}_j
-\sqrt{\max(E_{\rm remaining,j},0)\,129N_j/200}-e_j.
\quad}
$$

Here `e_j` is exactly the independently paid pair prices plus the previous
`nativeError = 4*abs(Im(P_j)) + 5*norm(Q_j-P_j)`. The latter concerns the
**whole** original carrier and the proved count-cropped core transfer. Under
the existing exposed-zero source, `tendsto_joinedError` proves `e_j -> 0` for
every analytic multiplicity. No imaginary null for an adverse subset is used.

The global credit is nonnegative and is now retained in the energy floor
rather than dropped. Its native size remains unbounded. Under the source
hypothesis the new comparison therefore keeps a real improvement in the
main cost, with only a vanishing correction; it supplies no percentage of
the numerical floor deficit by itself.

The next independent arithmetic target can now be posed jointly:

$$
\sqrt{\max(E_{\rm remaining,j},0)\,129N_j/200}
-\operatorname{nativeCredit}_j\le\frac{399}{5000}
\quad\text{cofinally}.
$$

`false_of_cofinal_cost_sub_credit` connects that **open premise** immediately
to the preserved relaxed simple-exposed-zero contradiction. There is no need
to bound the energy and credit separately. The old energy-only target
`987/(100000*(N+1))` remains a sufficient fallback; neither target is proved.
The multiple-zero ceiling also remains open. No new carrier is defined.

All previous sources and no-go audits are preserved. The finite pair and
complex projection probes remain exploratory and optional; no small-order
subset is treated as a cofinal full-population or source-budget certificate.

The [shared scoped audit](riesz-finite-phase-payment-audit.json) records the
22 checked public proofs, standard transitive axioms and all numerical limits.
