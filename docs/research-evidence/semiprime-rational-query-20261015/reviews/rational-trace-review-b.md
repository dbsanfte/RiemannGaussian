# Second independent review: finite-order rational adjoint trace criterion

2026-10-15. PASS. The final theorem explicitly assumes K is a FIELD. No further mathematical correction required.

Reviewed report: /tmp/semiprime-rational-query-20261015/rational/report.md
FINAL SHA256: fae3439b4f7380ec1c819ce03d0f818c2f2b036e8777aca8686c4d17945342eb
FINAL bytes: 9866
FINAL rational/manifest.json SHA256: 2daa1bf4520008162357c62953d2308d305bfdb4150e7d23e55d7157a0db51c3

The final change from b102a549.../9852 bytes is only the explicit field hypothesis. Final report/manifest hashes were freshly recomputed. All SIX external source entries and SEVEN local artifact entries in that manifest matched hashes and lengths. All TEN recursively pinned density-source entries also matched exactly. The inherited prime supply, actual offsets/order facts and row-density result remain identified as inherited inputs; no new analytic premise is hidden.

## Exact gauge and trace solvability

With A=U-dL, q=gamma^d and u=gamma^(-U), shifting H replaces factors r=0,...,L-1 by r=1,...,L. Thus both (1-x^d)h(x/gamma) and u(q^L-x^d)h(x) equal gamma^(-A)x^A B(x). The exact constants and signs in T(hy)=C(S-1)y and g_e=gamma^A x^(e-A)/B are correct.

S has order R on K(x). Summing an S-difference gives zero trace. Conversely direct reindexing verifies

    (S-1)sum_(t=0)^(R-1) t S^t(g)=R g-Tr(g).

Since R is invertible in the field, the displayed R-term rational y is a valid solution whenever trace vanishes. This works in positive characteristic as stated; characteristic zero is not required. The formula is existence, not an acquired fast algorithm, and the hidden R is not supplied to any algorithm by this proof.

## Periodic Gaussian expansion and obstruction constant

For L<R, every factor in Q_L^-=prod_(s=1)^L(1-q^(-s)) is nonzero. The q-binomial generating identity therefore specializes without a denominator collision. Its coefficients b_n are R-periodic in n. At the last L positions before R, one numerator factor is1-q^(-R)=0, giving the stated zeros. Summing the periodic formal series yields exactly

    1/B(x)=(sum_(n=0)^(R-1)b_n x^(dn))/(1-x^(dR)).

This is a formal/rational identity, not an analytic expansion at a numerical orbit pole. It also handles L=0 and L=R-1 under the stated assumptions.

For v=e-A, gcd(d,R)=1 gives exactly one n_e in [0,R) with v+d n_e=0 mod R. The trace of x^k is R x^k for R|k and zero otherwise, so only that term survives. From d n_e=U-e-dL mod R one obtains q^(-(n_e+s))=u gamma^e q^(L-s). The product b_(n_e) is therefore EXACTLY P_L(u gamma^e;q)/Q_L^-, with no sign or power omitted. All remaining factors in formula(6) are nonzero rational functions, including the invariant possibly Laurent monomial x^(e-A+d n_e). Necessity and sufficiency of row-product zero follow.

## Formal weights and actual fields

The same cyclic argument applies over K(w_1,...,w_J), with S fixing every weight. The trace remains a linear polynomial in algebraically independent weights with coefficients in the invariant field. Hence it vanishes iff every individual row coefficient vanishes, even when the proposed certificate is rational in the weights. Numerical specialization could cancel coefficients and is correctly excluded from this iff.

In each actual hidden field R_P divides P-1, so R_P is invertible; R_P>16m² and gcd(R_P,m)=1 give all theorem hypotheses. With U=N+3d and e_j=3d-delta_j the target is exactly gamma^(-N-delta_j), with no changed interval or source phase. The independently reviewed row-density theorem supplies unit rows in both fields; these force a nonzero formal weighted trace in each field. Legitimate composite rational certificates with non-zero-divisor polynomial denominators reduce to field certificates and are thus excluded. Degenerating denominators are correctly not accepted as inverses or meaningful rational identities.

The report correctly DOES NOT claim Omega(m) independent rational sectors. Multiplication by the nonzero gauge factors transports the cokernel to the cyclic-difference cokernel, which is one-dimensional over the fixed field K(x^R). Formal weights preserve the separate row coefficients inside that one invariant trace; they do not create an independent rational sector grading.

## Secondary pole check

At x_t=gamma^t zeta with zeta^d=1, the first coefficient vanishes only at t=0 and the second only at t=L. A finite proper pole chain must start at L and finish at R-1; its length is R-L, with the orientation and endpoints stated correctly. Away from coefficient-zero orbits a pole propagates around the entire cycle. On the actual supply P does not divide d, so the coefficient zeros are simple. The homogeneous h/(x^R-1) example has exactly the claimed R-L remaining poles on the gamma orbit and does not solve an inhomogeneous nonzero-trace equation. Pole counts are not used as an arithmetic evaluation lower bound.

## Scope

The theorem concerns exact rational-function identity for THIS T, allowing arbitrary poles. Pointwise agreement on selected finite-grid points, identities only modulo x^R-1, parameter-deformation finite parts and anomaly-corrected equations have different contracts and are not excluded. Another operator, retaining a nonzero weighted remainder, or a norm-only evaluator remains possible. No fast rational residue acquisition, nearlinear long-query evaluator, generic circuit lower bound, new Lean theorem or guaranteed sixth-rate algorithm follows.

Only this local independent-review artifact was written. No repository edits or builds were performed.
