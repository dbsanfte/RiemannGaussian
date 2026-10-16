# Independent review: formal weighted holonomic interfaces

2026-10-15. Verdict: PASS. No substantive correction requested. This review covers exact algebra, actual-versus-formal scope, explicit cost contracts and saved primary-source premises. No Lean build or faster query implementation is asserted.

## Exact reviewed bytes and manifest validation

Reviewed holonomic/report.md SHA256 c424a84a41c4390a4ce55ea26278f5e0da87ad86e979aec02a795675a02d5334, 11,357 bytes. Manifest SHA256 72c9bab6d9c4308963457f46e9d1821e73b575fb94b4572acd7c21e74751adaf.

Independently read every manifest source/artifact, recomputed all SHA256 values and byte lengths, and checked all entries. All seven source entries and five artifact entries passed, including both PDFs and texts, the actual-source native definitions and the report itself.

Saved 2026 primary pins: polynomial-reduction-2026.pdf 0fac298246672cc41c67795df940a4e7516239349a7c3bde0cf4f2008e515319; text cd396cac630dcdbff012a93a9c0b96de3606a0f1a906c527e47808bac9900f0f.

## Actual regular-start order bound

The actual offset span has width 4m^2, smaller than each retained local order R>16m^2. Consequently integer offset equality is exactly target equality in either hidden field. The source congruence c j^2+2Nj-N=0 modulo m is nonzero even for c=0, and each low digit has at most two tags. This proves D>=ceil((m-1)/2) distinct targets fieldwise, not merely globally modulo N.

At a regular recurrence start, coefficient comparison in the FORMAL independent weights gives a polynomial Q vanishing at all D targets. The q-Newton polynomials have distinct degrees with nonzero unit leading coefficients, so a nonzero coefficient vector makes Q nonzero. The degree/root bound r>=D is correct. At later regular positions only rows with P_n(z_j) nonzero may be divided, as the report explicitly restricts. Singular starts, weight-dependent coefficients, nonlinear/state-space interfaces and horizon-only output are excluded. Thus this actual-family order statement is narrow but valid.

## Exact unit-leading order-J closure and beta formula

The relation Y B_k=q^(-k)(B_k-B_(k+1)) is exact. Triangular basis conversion gives Y^i=sum beta_(i,k)B_k. Substituting xZ and multiplying by h_i x^(J-i) proves the stated x^J H identity. The leading coefficient a_J=(-1)^J q^(-J(J-1)/2) is a known unit. Multiplying by P_n(z_j) converts B_k(q^n z_j) into P_(n+k)(z_j) without division, so recurrence (1) is valid over every commutative ring with q a unit.

The explicit beta formula with the COMPLETE homogeneous symmetric polynomial h_(i-k)(1,q^(-1),...,q^(-k)) checks, including its sign and q exponent. For example beta_(2,1)=-(1+q^(-1)), beta_(2,2)=q^(-1), agreeing with direct expansion.

There are exactly (J+1)(J+2)/2 natural dense x-coefficient slots. In the characteristic-zero symbolic gamma model, each h_i coefficient of H has one fixed sign and positive Laurent coefficients, and each beta has its own fixed sign and positive Laurent coefficients. Each x degree selects one i, so there is no cancellation within that slot; all are nonzero symbolically. The report correctly allows numerical modular cancellations and does not transfer this positivity into a finite-ring density lower bound. Explicit dense array materialization pays Omega(J^2) slots by its contract; it is not a circuit or sparse-representation lower bound. The stated O(J^2) construction is a valid upper bound, not asserted to be optimal for implicit representations.

## Cleared Hadamard closure

The coefficient recurrence (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k has the correct sign and does not divide by c_k. Starting from sum_r h_r s_(k+r)=0, multiply by the common products of the hypergeometric ratios to obtain exactly equation (3): the r term has the first r denominator factors and the last J-r numerator factors. It holds as a polynomial q-binomial identity, so exceptional coefficient zeros do not invalidate it. The natural coefficient degrees are at most J. Leading-step inversions, if used, are the displayed 1-q^(k+r) and must be handled/routed; the alternative order-J closure avoids them.

Nothing in these closure identities supplies a fast long-horizon clock. The report properly retains growing order, coefficient acquisition, initial data and matrix dimension, and does not promote a binary-splitting leaf count into an arbitrary lower bound.

## 2026 adjoint reduction and sector argument

The substitution u=gamma^(-N-3d), e_j=3d-delta_j gives u gamma^(e_j)=z_j exactly. Thus sum_k E(gamma^k)u^k c_k is the desired formal weighted sum. The first-order operator is correct, and applying the formal adjoint yields

(gamma^(-e)-u q^L)x^e+(u-gamma^(-e))x^(e+d).

The first coefficient vanishes only at e=N+3d-dL and the second only at e=N+3d, in the indeterminate-gamma model. Both belong to the same residue class N modulo d. In every other class a finite Laurent input has a surviving lowest term and a different surviving highest term d steps above its maximum. Its image cannot be a single monomial. Sector preservation means other classes cannot cancel these extremal terms. Hence each such monomial represents a nonzero quotient class for this specific adjoint-image interface.

At least ceil((m-1)/2) source sectors are occupied; removing at most one exceptional sector leaves Omega(m). Formal independent weights prevent cancellation of individual weighted quotient classes. This is a valid symbolic polynomial-adjoint remainder obstruction. It is NOT an assertion of general nonsummability of the finite coefficient stream, nor an actual finite-field obstruction: numerical gamma can create additional coefficient zeros and long certificates. The report explicitly excludes those transfers, rational certificates outside the Laurent interface and different implicit evaluators.

## Saved primary-source premises

The saved Wang--Yang--Zhong title page identifies arXiv:2606.07061v1, 5 June 2026. Section 2.1 (text around lines 137 onward) explicitly assumes characteristic zero and q indeterminate. The adjoint definition and Lemma 2.2 (around lines 188--219) give the shifted adjoint and Lagrange identity. Theorem 2.4 (around lines 298--312) requires gcd(a_0(x),a_J(q^i x))=1 for every i in N for its Laurent characterization. Thus the report correctly treats these as symbolic field statements with explicit coprimality/leading-cancellation premises, rather than composite-ring or bit-cost theorems.

No issue was found in the reported algebra or scope. The new actual finite-ring transfer/full-density companion mentioned by the root is separate and is not granted review credit here. No soft O(J+sqrt L) weighted program or fast high-order propagator is supplied by this report.
