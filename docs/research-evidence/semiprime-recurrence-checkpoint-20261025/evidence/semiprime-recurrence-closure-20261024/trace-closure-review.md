# Independent actual-trace closure audit

24 October 2026. **PASS. No required fixes.** Reviewed exact `/tmp/semiprime-recurrence-closure-20261024/trace-closure.md`, SHA256 `bf6e0fa9c41c25af10f4575d098b51d2c7556af709ffb3ed4391d45c14f415cc`. Scratch review only; no source/repository edits, examples or additional primary theorem needed. All substantive identities below were checked directly.

## Acquired center and two-stream normalization

D is the full even-character unit, fixed by bar and all unit automorphisms, with its epsilon phase retained. U*bar(U)=D^k gives W=D^(-k/2)U bar-norm one. Consequently v=W^(k/2) is actually acquired, v²=W^k=D^(-H/2)u^H=q, and bar(v)=v^-1. This uses integer powers and legal Gauss/D units, not extraction of an unknown square root or transfer of scalar beta orders.

Centering X_j=v^(-tau_j)R_j gives X_j X_-j=1. Thus x_j is the actual centered trace and the old S_j is v^tau_j*x_j. Expanding the original pair difference verifies equation (1), including the unit prefactor z*v^tau and index 2i-tau. Its product prefactor q^[M L(L-1)/2]*v^[L sum(tau M_tau)] is correct.

The even/odd recurrences have the displayed starts and coefficient theta²-2=q+q^-1. Equation (2) follows by separating the endpoint d0 of the tau=0 stream, endpoint d_(2L) of tau=-2, and common interior even indices. It is a division-free product identity for the nonempty source interval; empty products are handled directly. No endpoint is removed by numerical division. In particular d_(2L) corresponds to ORIGINAL i=L-1 in tau=-2, not a new out-of-range collision index. Restrictions must retain their actual clipped endpoints, exactly as stated.

Acquisition of the shared center/starts is soft k, but all trace polynomials require their actual row-dependent x_j values and coefficients, soft(kM) in this implementation. Two-stream sharing changes neither total degree nor horizon asymptotics.

## Normalized quotients and every carry in the actual update

For odd unit e, C_e*bar(C_e)=D^(e-1), so Z_e=D^(-(e-1)/2)C_e has bar-norm one. The cocycle, e+k and kth-power identities (3) have the correct D exponents:

    Z_(ab)=Z_a^b*rho_a(Z_b),
    Z_(e+k)=W*Z_e,
    Z_j^k=W^j/rho_j(W).

Inserting C_j=D^((j-1)/2)Z_j and U=D^(k/2)W into the prior packed row cancels D exactly because k*n_j=ell_j+a_j*j+N*s. Centering contributes W^(-k*tau_j/2), proving the actual h_j in (4).

For j'=[g*j]_k and s'=[t*s]_k with t=g^-1 modulo k, the inverse update is correct and a'=[t² a_j]_k is the actual native coefficient. All e,f,d are integers; g*a'-t*a_j is divisible by k since g*t=1 modulo k. Cocycle transport gives the two displayed Z updates with W^(-e), W^(-f).

Before eliminating Z_j's kth power, the multiplier relative to X_j^t is

    W^[h_j'+e*a'+f*N-t*h_j] * Z_j^(-k*d)
      *rho_j(Z_g)^(-a')*rho_s(Z_t)^(-N).

Using Z_j^(-k*d)=W^(-j*d)*rho_j(W)^d proves equation (5) with EXACTLY the stated A_j and L_j. All exponents are public polynomial-size integers and every negative power is of a certified unit. The O(log k) public generator vectors and all metadata are paid soft k; applying these automorphisms/powers across all rows remains soft(k*|G|). No descriptor is counted as an expanded row.

## Next mixed trace term and initialized alternate basis

The identity y^n=(D_n(tr y)+delta(y)V_n(tr y))/2 is valid for all integer n with the stated negative-index convention and unit y. Expanding X_j^t L_j and its inverse proves (6). Their difference proves (7), including the next term delta(X_j)*delta(L_next). It is not supplied by the preceding mixed product. The source does not assert independence or impossibility for another representation; it identifies the exact missing state of this one.

The triple-generator formula (8) has the correct factor 1/4 and three positive pair-delta terms. Inverting all three powers cancels odd delta counts, which proves it directly. Monic quadratic-algebra binary powering supplies D,V at O(log N) A operations for these bounded-bit exponents; Y inverse is t-Y, so no trace discriminant or anti-invariant vector is inverted. The required per-row t_2,t_3,b_rs are explicitly acquired and charged. Formula validity includes delta=0 and zero trace answers.

## Seed invariant, pullback degree and value completion

Dickson addition gives d_(2n)=d_n²-2 and d_(2n+1)=d_n*d_(n+1)-theta. Hence both consecutive-state branches (9) and invariant x²+y²-theta*x*y=4-theta² check, including startup (2,theta). The circuit generates individual terms but does not acquire their evaluation product. Pullback of a monic degree-M F by T²-2 has exact degree 2M over the composite ring because its leading coefficient is one. The source does not call that implementation-specific degree increase a general lower bound.

After supplied row vectors, the stated monic baby-polynomial/multipoint completion is valid over A even without Gauss-component order separation: product/remainder arithmetic is monic and does not invert cross differences or stream values. Explicit coefficients and giant points cost soft(J+sqrt(JL)) A operations, hence soft k times that base-ring work, with row acquisition paid. The final primitive norm is taken only after its actual vector input is supplied. This is correctly classified as a VALUE computation with possible component-hit recovery unresolved.

## Support and verdict scope

All identities preserve the actual row/seed labels and permit zeros. Proper scalar gcds are valid factors. A raw saturated primitive norm is not assigned the original scalar beta decoder or a new component-order certificate. Only a selected conjugate-paired beta-coupled hit invokes the previously proved SAME-leaf bridge; otherwise the original covered scalar query remains the complete fallback at soft(J+sqrt(JL)). No unbounded auxiliary Dickson index is mistaken for an original bounded index.

The acquired center, two-stream merge and generator-based unit update are real supporting constructions. Their actual mixed starts, next correlations and terminal polynomial/norm remain charged. The report claims neither soft-k full-query acquisition nor a new whole-input exponent, and makes no general recurrence lower-bound claim. Exact reviewed bytes pass.
