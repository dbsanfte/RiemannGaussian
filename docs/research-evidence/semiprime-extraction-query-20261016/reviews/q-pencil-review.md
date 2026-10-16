# Independent review: exact paid rank-two block q-pencil

2026-10-16. Verdict: PASS for the explicit generalized displacement and paid operator/generator claims. This is not an ordinary compatible generator or a full diagonal algorithm.

Reviewed `/tmp/semiprime-extraction-20261016/diagonal/report.md`: 6653 bytes; SHA-256 `ef999aa2cfbea33c29192035900542808532e906b70a95f55a8c7a30a3819433`. The report entry and all THREE prerequisite source paths in its manifest independently match recorded byte lengths and hashes. The actual paid block-transform and mixed-matrix prerequisites were independently reviewed previously. No frozen report or repository file was edited; no build was run.

## Exact pencil and orientation

W has rows z_j^s and is the transpose of the usual evaluation Vandermonde. For a polynomial coefficient ROW vector p, its node-value row is pW. Right multiplication by Q_z=W^(-1)diag(q^s)W gives p diag(q^s)W, exactly the values P(qz_j). This proves interpolation closure for degree<J block polynomials even though the target set itself is not closed under q. Unit pairwise differences supply the required interpolation inversions, with the ordinary soft O(J) setup and action costs.

For P_n(t)=sum_(s<B)c_(Bn+s)t^s and X_n=q^(Bn), the coefficient of t^k, 1<=k<B, in

    (1-q^L t)P_n(t)-X_n(1-t)P_n(qt)

is (1-X_n q^k)c_(Bn+k)-(q^L-X_n q^(k-1))c_(Bn+k-1)=0 by the finite coefficient recurrence. The constant is (1-X_n)c_(Bn), and the t^B coefficient is -(q^L-X_n q^(B-1))c_(Bn+B-1)=-(1-X_n q^B)c_(Bn+B). Therefore equation (1), with u_n and v_n exactly as stated and right factor (z_j^B), has the correct sign, endpoint and q weights.

T=floor((L+1)/B) ensures all complete block indices lie within [0,L], and the endpoint TB is at most L+1. If TB=L+1, its coefficient is declared zero; the terminal recurrence then has numerator q^L-q^L=0. No inverse 1-q^(L+1) is needed. If T=0 the block matrix and generators are empty and the earlier mixed-matrix ragged term contains the full polynomial. No missing padding data or separate T-fold seed acquisition is hidden.

All endpoint coefficients share ONE selected-coefficient setup at soft O(sqrt L+T). The C/C^T actions, W/interpolation/transposed actions, and q/node powers are paid at the claimed soft O(J+T+sqrt L) work/storage scale for B=J. The low-rank right side has only O(T+J) explicit data. There is no inverse of a potentially colliding scalar factor 1-z_j or 1-q^L z_j: retaining a pencil is essential and the report does retain it.

## Boundary and power expansion

For the column-value interpolation convention Q=V diag(q^s)V^(-1), QZ-qZQ is rank at most one because it vanishes on polynomials of degree<=J-2. Since Q_z=Q^T, the row defect Q_zZ-q^(-1)ZQ_z is -q^(-1) times its transpose and also rank at most one. The displayed B-term expansion telescopes exactly with coefficient q^(-h), leaving Q_zZ^B-q^(-B)Z^B Q_z. Equation (2) has the correct orientation and weights.

As the report states, a B-term expansion is an upper-bound representation, not a small-rank theorem. Its ordinary powered-node compatibility correction is not supplied cheaply as polylogarithmic-rank generators. Our separate actual-source defect theorem strengthens this point for the natural interpolation defect, but does not change the reviewed report's valid claim or imply a rank lower bound for YS-SY itself.

## Differentiation and remaining scope

The determinant deformation derivative at theta=0 equals S_ii over every commutative ring by the universal determinant expansion. A formal division-free scalar determinant circuit would suffice via reverse differentiation; fast S actions are not that circuit. The mixed Hessian of x^T S y has entries S_ij, while gradients and Hessian-vector products supply only the already paid actions. The report does not infer a diagonal-Hessian algorithm, determinant clock, or general lower bound from these observations.

The final scope is correct: explicit paid rank-two q-pencil, not the missing ordinary Trummer generator, not a fast whole query, and not a new Lean or all-semiprime controller theorem.
