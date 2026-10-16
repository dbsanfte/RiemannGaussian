# Independent review: finite-order rational adjoint trace criterion

2026-10-15. Verdict: PASS on the final frozen bytes below. The theorem explicitly assumes a FIELD K. No substantive correction requested. This is a classical solvability review, not a query algorithm or Lean verification.

## Base report and byte validation

The full reviewed base report was rational/report.md SHA256 b102a549325860a5d4ae59a6205282059f8f939e8f03177d917bcd7d451ac326, 9,852 bytes. A final pin after the explicit-field wording correction is appended below rather than erasing this history.

Independently recomputed every source/artifact hash and byte length from rational/manifest.json: all SIX source entries and SEVEN artifact entries passed. Independently expanded density-source-pins.json and hashed all TEN nested source paths: all passed. These include the original native source, historical prime-order reports, actual full-row density theorem, transform and formal-AD contracts. The base manifest hash was 1e86c990eda18fcd7af0e66e63bedef4c7dcb3be606a330eec07b21d3d90c468.

## Exact gauge and cyclic solvability

For H=prod_(r<L)(1-q^(-r)x^d), replacing x by x/gamma shifts each factor index by one. Therefore (1-x^d)h(x/gamma)=gamma^(-A)x^A B. Also u(q^L-x^d)h=u q^L x^A B, and gamma^(-A)=u q^L by A=U-dL. Thus T(h)=0 and T(hy)=C(S-1)y exactly. All h,C are nonzero rational functions, even though they can vanish at numerical orbit points. Dividing in K(x) is legitimate and does not assume a unit value at any such point.

The cyclic identity is correctly oriented:

(S-1) sum_(t=0)^(R-1)t S^t(g)=Rg-Tr(g).

It follows by shifting the sum and using S^R=1. Hence trace zero is both necessary and sufficient, with y=(1/R)sum t S^t(g). Characteristic not dividing R is material and explicitly assumed through invertibility of R. This is an existence formula with R terms, not a fast construction or hidden-order acquisition.

## Periodic coefficient and row-product formula

The coefficient b_n in 1/B is the complete-homogeneous/q-binomial product prod_(s=1)^L(1-q^(-(n+s)))/Q_L^-. The denominator is nonzero since L<R and q has order R. The formula is valid for every nonnegative coefficient index; it is R-periodic after specialization, and b_(R-L),...,b_(R-1) vanish. Thus 1/B=(sum_(n<R)b_n x^(dn))/(1-x^(dR)) is exact as a rational identity. Equivalently it is the explicitly expanded complementary factor of 1-x^(dR). No evaluation at a zero of B occurs.

The denominator is invariant under S, and tracing x^k keeps exactly exponents divisible by R. Since gcd(d,R)=1, exactly one n_e in [0,R) survives. Its congruence gives q^(n_e)=gamma^(U-e)q^(-L), so every factor in b_(n_e) is 1-z_e q^(L-s). Consequently b_(n_e)=P_L(z_e;q)/Q_L^-, with the coefficient and monomial in (6) exactly correct. Every remaining factor is nonzero in K(x). This proves the monomial iff, including sufficiency. Signed integer e and L=0 are also consistent with the same proof and empty-product convention.

## Formal rational weights and the cokernel

The shift fixes the formal independent w_j. The weighted trace is a polynomial linear in those variables with rational-function coefficients. It vanishes iff each coefficient vanishes, regardless of whether the sought certificate is allowed to be rational in the weights. A numerical specialization may cancel trace terms and the report correctly declines the corresponding iff there.

Over the fixed field K(x^R), the cyclic extension K(x) has degree R and trace is surjective because Tr(1)=R is invertible. The explicit formula identifies im(S-1) with ker Tr, so its cokernel is ONE-dimensional over the fixed field. The gauge and multiplication by nonzero C preserve this dimension. The report correctly abandons the independent-Laurent-sector count for arbitrary rational certificates; it retains only the formal-weight coefficients of this single trace remainder.

## Actual-family and composite interpretation

With d=m^2,U=N+3d,e_j=3d-delta_j, the parameter z_e is exactly gamma^(-N-delta_j). No target phase or valid interval has changed. R divides P-1, is invertible in F_P, is coprime to d and exceeds L. The inherited actual full-row density theorem supplies m-o(m) complete products that are units modulo N, simultaneously over the required menu/length range. In particular there are nonzero row coefficients in EACH hidden field. Their formal weighted trace cannot vanish, so the fixed rational adjoint equation has no solution in either field.

For squarefree N, a non-zero-divisor denominator polynomial has nonzero projection in both hidden polynomial rings. A valid composite rational identity with such a denominator would reduce to the excluded field identities. A denominator that becomes the zero polynomial is not a legitimate inverse in that component; allowing a vacuous cleared identity would change the contract. The report explicitly distinguishes this degeneration and requires factor-aware interpretation.

The obstruction concerns exact rational identities in x, not agreement on finitely many points or identities modulo x^R-1. Finite-grid interpolation with omitted poles, deformation/finite parts and new anomaly terms therefore remain outside its conclusion. This distinction is essential and present.

## Optional pole-chain check

In the coefficient-zero orbit x_t=gamma^t zeta, the first coefficient vanishes at t=0 and the second at t=L. A pole of p at t contributes at t through the second term and at t+1 through the shifted first term. An incomplete pole string must therefore start at L and end at R-1, giving R-L distinct poles. The orientation and off-by-one count check. Actual field characteristic does not divide d, so those coefficient zeros are simple. Other pole orbits require full-cycle propagation.

The homogeneous example h/(x^R-1) is valid because its extra denominator is shift-invariant. On the gamma orbit the L zeros of h cancel the first L denominator zeros, leaving R-L poles. It does not solve a nonzero-trace equation. Neither pole number nor denominator degree is promoted to an arithmetic operation lower bound.

## Scope and outcome

The row-product trace criterion is an exact rational solvability theorem for this specified operator. It is not a no-go for another operator, an evaluator retaining its trace remainder, norm-only methods, nonrational functions or a general formal weighted SLP. Computing its obstruction coefficient is the original query, not free denominator preprocessing. Formula (3) supplies no softly linear clock. The report preserves all these limits.

Primary papers are context rather than premises of the self-contained proof; their artifact bytes were verified, but this review does not claim an additional broad literature search or import their characteristic-zero algorithms into finite fields.

## Final frozen pin after the field clarification

The author made ONLY the explicit-field wording clarification. Re-read that statement and independently revalidated every final manifest source/artifact hash and byte count. All pass. Final report rational/report.md SHA256 fae3439b4f7380ec1c819ce03d0f818c2f2b036e8777aca8686c4d17945342eb, 9,866 bytes. Final manifest SHA256 2daa1bf4520008162357c62953d2308d305bfdb4150e7d23e55d7157a0db51c3. The preceding base pin is preserved as historical review provenance; the PASS verdict applies to these final frozen bytes.
