# Cross-row cancellation and a scalar recurrence for the unique pole

26 October 2026. The preceding turn proved a public whole-bin unique-hit cover with the original short weighted clock. This pass uses that promise to obtain **an actual cross-row cancellation to a constant numerator** and **a fully initialized scalar recurrence whose final two values locate the hit**. These give concrete algorithms to accelerate.

**No acquisition exponent improvement is established.** The scalar recurrence currently costs soft Jh; the existing joint engine remains better at soft(J+sqrt(Jh))=soft K^(5/4). Whole-family soft-K acquisition and the complete deterministic all-semiprime sixth-rate bit proof remain open. The findings are paper derivations and exact identity diagnostics, not Lean proofs or a factor-success campaign.

## 1. A cancellation that applies to the actual rows

Use the selected native T_j, with J<=K/3, h=O(K^(3/2)), and canonical tags u_j. A guarded soft-K derivative/evaluation step either factors or certifies every row difference a unit. Its nonunit branch localizes an ORIGINAL difference before invoking the existing short mixed-relation decoder; it does not interpret an arbitrary additive zero as an annihilator.

Let D(Z)=product_j(Z-T_j), A=1+delta and alpha_j=T_j^(J-1)/D'(T_j). All alpha_j are then actual units, and

    sum_j alpha_j/(A-T_j X) = A^(J-1)/product_j(A-T_j X).

Thus the entire row sum has a constant numerator. Interpolation acquires the corresponding marked numerator in soft K. Global row separation makes the delta poles simple at every component, so the numerator can be frozen at delta=0 for residue extraction. The common clock factorial normalizer can also be omitted from BOTH projective outputs.

The resulting sufficient pair is

    V=Res_delta L_h(1/D_delta),
    U=Res_delta L_h(R/D_delta),

where D_delta=product_j(1+delta-T_j X), R is an acquired degree-<J polynomial, and

    L_h(f)=[X^(h-1)](X^(h-1)*f mod W_h),
    W_h=product_(i<h)(X-rho^i).

Rational inverses here are componentwise Laurent identities; this is a target specification, not permission to invert a nonunit constant numerically. At the unique good hit, V is nonzero and U/V=u after actual unit checks. Only one selected coefficient and its short marked companion are requested; the full inverse need not be emitted.

The normalized ordinary moments are Gaussian binomials, L_h(X^k)=[h+k-1 choose k]_rho, initialized at 1. The first O(J) are genuinely acquired in soft J. The remaining operation is applying this functional to the deformed rational inputs. Exact residue reciprocity retains the original finite-clock singular data.

See [weighted-contraction.md](weighted-contraction.md), its [review](review-weighted.md), and the normalized [hybrid handoff](hybrid-handoff.md).

## 2. A concrete scalar recurrence, including its start

A companion-adjugate column gives a nonzero cyclic projection of the unique common root. Its two top coefficients suffice, even if other row roots repeat. This does not assume the whole long remainder is supplied.

The derived scalar algorithm uses a_n=q^n and consecutive divided differences B_k(a_n)=D[a_(n-k),...,a_n]:

    E_0=1,
    E_n=-sum_(k=1)^min(J,n) B_k(a_n)
             *product_(i=n-k+1)^(n-1)D(a_i)*E_(n-k).

There is no division by a possibly vanishing D(a_i) or E_i. Its first J regular values and the input polynomials cost soft J; an encountered short-prefix collision takes the actual factor/tag branch. Only its final two values are needed:

    theta=a_(h-1)+D(a_(h-1))*E_(h-2)/E_(h-1).

The final denominator is nonzero at the good field, so its norm gate permits a proper factor or a legal inverse. Short cofactor evaluation then recovers the tag. Wrong-bin attempts remain bounded and cannot suppress later bins.

Current execution has O(J) state and soft-J work per clock step. The explicit high-lag tail is still present; a constant-state Riccati truncation has not eliminated it. This is a specific recurrence to accelerate, not a claim of minimal recurrence order or a general lower bound.

See [selected-subresultant.md](selected-subresultant.md), especially §6, and its [independent review](review-subresultant.md).

## 3. Finite q-Pearson and continued-fraction connection

The finite clock satisfies an exact Pearson equation with vanishing endpoints. Its natural polynomial version after row modification is already implied by the row multiplication equation, so it contributes no new support constraint. The rational version is valid but connects shifted denominators and retains the interior pole.

The same finite functional is a terminating little-q-Jacobi specialization. Its three-term coefficients, exceptional initial coefficient and singular terminal boundary are explicit and correctly guarded. Both an O(J)-length prefix and suffix are acquired in soft J. Connecting them across the remaining finite tail at the supplied row arguments is still the long operation.

This tests two actual proposed closures rather than treating the existence of a recurrence or a continued fraction as an acquisition algorithm. See [qpearson.md](qpearson.md) and its [review](review-qpearson.md).

## 4. Evidence and next required advance

The [standard-library identity checker](check_pole_identities.py) passed 264 exact finite-field checks, including singular steps, repeated nonhit roots, direct dense adjugate comparisons, the scalar recurrence, finite inverse reciprocity and little-q-Jacobi endpoints. [Validation details](validation.md) distinguish these diagnostics from the uniform paper proofs and bit-cost obligations.

The next substantive acquisition result would be a soft-K evaluation of the normalized selected functional, or of the scalar recurrence's final pair. The current cancellations, initial conditions and unit guards are supplied; that runtime theorem is not. No commit, push, Lean proof or new literature-wide novelty claim is included. Earlier frozen evidence and concurrent work are preserved; [review.json](review.json), [sources.json](sources.json) and [manifest.json](manifest.json) record the scope and integrity checks.
