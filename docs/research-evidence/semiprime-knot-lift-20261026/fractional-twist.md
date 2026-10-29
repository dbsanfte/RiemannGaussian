# Fractional twist interpolation: forced native root and explicit extra divisor

26 October 2026. Scratch algebra/acquisition pass; no numerical campaign or repository edits. Uses the audited negative-twist and fixed-state skein formulas, not a new generic quantum-group assertion.

**Positive result.** A lawful finite linear skein element forces any supplied native collision root without solving the lift exponential equation. Its denominator-cleared scalar factors explicitly into the desired root factor and a second linear factor in the folded clock. Both full native coefficient polynomials are acquired in soft L. Their clock products are still unpaid; the extra divisor is not generally a harmless unit or a fixed q-shift of a native root. Exact cancellation before evaluation returns the already acquired original pair polynomial. No full-query exponent gain is established.

## 1. Formal lift coefficient, with all singular branches retained

Fix a supplied native v, s=v/(v-1)^2 modulo N, u=q^-1 and d=u-1. The screened v,v-1,u,d and u+1 are units. The s sign is the negative twist convention: c=-v/(v-1)^2=-s. Put

    w=B_v=(v-1)(u-v)/v,
    B(a)=(a-1)(u/a-1)=1+u-a-u/a.

The original row collision a=v has B(a)=w. Its inverse orientation a=v^-1 is handled by repeating the construction with v^-1; the same s applies. These are two explicitly supplied orientations, not unknown physical indices.

Allow the coefficient U, formerly u^s, to vary formally. The source scalar becomes

    F_U(B)=1-2s B²/(u d)
          +(u+1)(U-1)B(d+B)/(u d²).                  (1)

When w(d+w) is a unit, setting F_U(w)=0 gives the acquired rational target

    U_*=1+d*(2s w²-u d)/[(u+1)w(d+w)].                (2)

This is the same target as the lift-law equation, but no discrete logarithm is needed if a linear skein element is permitted instead of an actual integer twist. U_* need not be a unit; no actual knot T_-s' with u^s'=U_* is claimed.

Do not invert the denominator of (2) without a gcd/unit check. A proper gcd gives a factor of N. A saturated gcd is an algebraic degeneration, not a beta annihilator. The following cleared scalar avoids that inverse altogether:

    J_v(B)=u*w(d+w)+(2s w²-u d)B-(u+2s w)B².          (3)

It is u*w(d+w)*F_(U_*)(B) where (2) is legal, and is a well-defined polynomial in every branch whether or not (2) exists. Its forced-root identity is exact:

    J_v(B)=(B-w)*[-(u+2s w)B-u(d+w)].                (4)

This remains true for zero divisors and repeated roots. It never invokes a nonexistent fraction at a saturated denominator.

## 2. A lawful finite skein element, not merely a virtual exponent

The three fixed normalized twist states F_0=1, D_1=F_1-1 and D_2=F_2-1 satisfy

    D_1=alpha B+beta B²,
    D_2=alpha(u+1)B+beta(u+3)B²,
    alpha=(u+1)/u, beta=1/u.

Their coefficient determinant is 2(u+1)/u², a certified native unit. Thus every explicitly acquired quadratic j_0+j_1 B+j_2 B² is a lawful linear skein combination of these three scalar states, using

    B=[(u+3)D_1-D_2]/(2alpha),
    B²=[D_2-(u+1)D_1]/(2beta).

Applying these identities to the coefficients in (3) realizes J_v without (2)'s problematic denominator. This is an actual finite linear skein element over the acquired scalar ring, not an unproved tensor representation or an unevaluated formal U. Coefficients require only the already certified units 2,u,u+1 and v,v-1. Product of these scalar elements can be interpreted through connected-sum multiplication, but coefficient-product acquisition below suffices; a single genuine topological knot is not asserted.

The same basis can of course realize the monic linear polynomial B-w directly, eliminating the extra root completely. That is positive initialized root recovery, but it only acquires the known original pair factors: the expensive remaining operation is their physical-clock product. The extra divisor is the specific cost of remaining on the one-U fractional-twist curve (1), not an unavoidable cost of every linear skein construction.

Primary input is Kohli's negative-twist formula, Proposition 2.18, and the finite recovery identity independently derived from it; https://arxiv.org/pdf/2505.08296 . No new literature assertion is needed for the polynomial operations above.

## 3. Second root, degeneracies, and native unit statements

If u+2s w is a unit, the second root in (4) is exactly the proposed

    R_v=-u(d+w)/(u+2s w)
       =-u(v-1)(2uv-v²-u)/[v*(u(v+1)-2v)].           (5)

The formula confirms the proposed sign and normalization. If u+2s w is nonunit, keep the linear factor in (4) rather than inventing R_v. A proper coefficient gcd factors; global coefficient zeros do not supply a licensed short multiplicative annihilator.

At an actual positive odd-clock collision a=v, w is a unit: a-1 and b-1 are nonzero short native differences. At arbitrary supplied v, w need not be a unit. This distinction does not matter for (3),(4). If a whole row has v=u or v=u^-1 globally, its original factor is harmless on every searched positive odd clock because both even exponents +/-2 differ from all searched odd exponents by nonzero guarded amounts. It can be removed as a unit row. Proper gcds in these comparisons factor N. No similar blanket unit statement is available for d+w or u+2s w.

Some exact exceptional cases are constructive:

* If u+2s w=0 globally and d+w is a unit, J_v is a unit multiple of B-w: the extra root has gone to infinity.
* If d+w=0 globally, the extra factor is -(u+2s w)B. Since physical B(a) is a unit, it is harmless provided u+2s w is a unit. At a=v, the earlier identity gives u+2s w=u*(1-2/v); no unit is inferred if v-2 is nonunit.
* If both coefficients of the extra linear factor vanish, J_v is identically zero and is unusable as a query. The direct linear skein element B-w remains available.

These branches are identifiable from acquired row coefficients in soft L, and provide limited safe simplifications. They do not prove most native rows belong to one of the favorable branches.

## 4. Entire native product, with explicit cancellation ledger

Let w_j=B(v_j), w'_j=B(v_j^-1), with s_j=v_j/(v_j-1)^2. The desired single-pair polynomial already acquired from the native roots is

    P_native(B)=product_j P_(s_j)(B),
    P_s(B)=1-s d²/u+s(1+u^-1)B+s² B²/u
          =(s²/u)(B-w)(B-w').                       (6)

Acquire both orientations of (3) and their extra linear factors ell_v(B)=-(u+2s w)B-u(d+w). Product trees give

    J_native(B)=product_j J_(v_j)(B)J_(v_j^-1)(B),
    E_native(B)=product_j ell_(v_j)(B)ell_(v_j^-1)(B),

with degrees at most 4L and 2L, in soft L. The exact full identity is

    J_native(B)=C*P_native(B)*E_native(B),
    C=u^L/(product_j s_j²),                          (7)

where C is a known unit. It is not just an equality of zero sets.

Thus this interpolation has an actual acquired whole native scalar, not merely a rowwise representation. At physical pair clocks B_h=B(eta³*q^(2h)), its product equals the original paired prefix times the additional orbit product of E_native, times a known unit. The extra product has degree-O(L) input and the same clock length. Neither its coefficients nor its short description initialize its long norm at soft(L+sqrt m).

Polynomial cancellation BEFORE physical evaluation is safe: the known monic factors B-w,B-w' can be built directly, recovering P_native in soft L with no inverse of an extra value. If E_native has a nonunit leading coefficient, arbitrary numerical polynomial division is not needed. Cancellation AFTER evaluating at a clock zero is not legal: E_native(B_h) may vanish or be a zero divisor. Certifying its unit orbit product is a separate query of the same unacquired form.

## 5. Test the plausible q-shift telescope specifically

The explicit extra root map in (5) is not generically a fixed multiplicative q-shift or inverse-shift of the original root in the B clock. Over Q(u,v), B(c*v)=1+u-c*v-u/(c*v) and B(c/v) have poles only at v=0 and infinity for a fixed nonzero c. In contrast, R_v has an additional finite pole at v=u/(2-u), with generically nonzero numerator. Hence R_v is not identically B(c*v) or B(c/v) for any c depending only on u. Exceptional parameters may cancel the pole and require their own treatment; this statement is only a test of that concrete telescope proposal.

Even pairing v with v^-1 does not make the additional divisor disappear. An exact compact form for one row's paired extra polynomial is obtained by writing A=u(B+d), C_B=2sB+u:

    ell_v(B)ell_(v^-1)(B)
      =A²-A*C_B*(u+1)/s+C_B²*(u/s²-d²/s).           (8)

Here w+w'=-(u+1)/s and ww'=u/s²-d²/s follow from (6). This uses no individual inverse of an uncontrolled coefficient. It gives another acquired degree-two factor per native row, with unit inverses only of s. This explicit paired divisor is acquired without an uncontrolled inverse. Its additional algebraic dependence on s and B remains part of the next contraction problem; no general native substitution identity or impossibility result is inferred from a formal degree comparison.

The pole calculation rules out only the stated direct shifts. They do not rule out a collective native-catalogue identity or another structured norm algorithm for (8).

## 6. Acquisition, physical readout, and original-label recovery

All row coefficients and both orientations cost soft L, with product-tree coefficient acquisition also soft L. Polylogarithmic extra lift equations have been avoided entirely at this stage. A supplied physical pair value is evaluated in soft L. The current complete geometric evaluator remains soft(L+sqrt(Lm)) up to constant degree/horizon changes; the fractional interpolation does not make the whole physical family cost soft L. An odd unpaired original factor can be evaluated directly at soft L.

At a localized zero of J_v(B_h), the factor B_h-w has a valid original interpretation:

    B(a)-B(v)=-(a-v)(a-u/v)/a.

The second alternative a=u/v means b=u/a=v, so ordinary reciprocity maps it to the second positive original argument. Proper gcds of these actual differences yield factors, and a saturated genuine difference has the existing original nonzero signed-label gap and licensed short-annihilator consumer. No new decoder is necessary for this part.

A zero coming only from ell_v(B_h), however, need not imply an original difference. A proper gcd of its value factors N, but a saturated extra zero is an additive/rational relation, not a beta^K=1 leaf. It cannot be passed to the original extractor without a new theorem. Thus even a cheap J_native norm would still require controlling or decoding the extra divisor, unless the direct monic linear recovery is used; that latter route restores the original hard prefix exactly.

The positive remaining object is therefore explicit: an acquired native finite-skein interpolation whose scalar is the original paired polynomial times the known rational-map divisor (8), together with safe exceptional branches and exact cancellation. A useful next advance must exploit that extra map collectively or contract the recovered original monic factors across their physical clock. No general no-go theorem, attained native counterexample, or factoring exponent improvement is claimed.
