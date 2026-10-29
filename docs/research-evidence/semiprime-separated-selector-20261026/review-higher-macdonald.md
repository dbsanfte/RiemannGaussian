# Independent review: all higher finite Macdonald responses

Disposition: PASS on the derived characteristic polynomial, soft-J conversion, required gates and selector scope. No diagnostic script was yet present at this review; this is an independent paper check, not a claimed replay.

## Formula and all-output acquisition

The matrix identity M=V diag(q^k)V^-1 is correct for polynomial interpolation/shift on degree<J. Multiplying row i of I-uA by T_i-b gives column polynomial

(1-u q^(h+k))X^(k+1)-b(1-u q^k)X^k,

since q^(h+k-1)=b q^k. The omitted-monomial alternant expansion therefore yields exactly (3) with no missing sign or power. Independent boundary checks: its constant coefficient is sum d_s b^s/D(b)=1; its leading coefficient is

(-1)^J q^(J(J-1)/2) q^(hJ) D(q^-1)/D(b),

matching (-1)^J det A from the explicit R_i. J=1 agrees with the given hand control. The principal-minor q^(r(r-1)/2) factor and cross-product are the usual finite Cauchy determinant after clearing; qT_i-T_j need not be inverted and may vanish.

The two-factor Newton recursion correctly splits every summand at the midpoint. Product trees plus balanced polynomial sums give soft J operations for ALL J+1 coefficients, not a per-coefficient cost. w_J A_[0,J) is separately included, so no final term is lost. Outputs and starts are truly supplied. Inverting this basis change also has unit triangular diagonal at u=q^-r after the specified h>J gap guard; normalization by D(b) does not change that scope.

## Gates and actual doubled clock footprint

D'(T_i) must actually be gated; singleton simplicity alone is insufficient. Literal alias deletion and the existing original mixed-label consumer provide the stated legal branch. R_i are units only after BOTH boundary screens. D(qT_i) is a numerator and need not be unit. The implementation by interpolation/evaluation avoids Cauchy-pivot divisions by qT_i-T_j altogether.

For the parity-shortened rooted bank write q'=pi^(H/m²), actual base Q=(q')². Gap 1-Q^s is certified by the original screen on 1-q_original^(2s), via the m²-power factorization. Thus actual use through s=h+J requires the doubled original exponents 2(h+J), not merely h+J. The conservative retuning bound and parity halving supply this: before halving h_raw<=8sqrt(2)K^(3/2)m^(3/2)+9; m³<=K/1024 gives h_raw<=sqrt(2)H/4+9, while 2h<=h_raw+O(1) and 2J<=2K/3. Hence 2(h+J)<16H throughout the inherited K>=54 range, with ample slack. No N<=(K')^6 assumption is needed. For an unhalved bank use its own actual base and the corresponding original exponent footprint. The report correctly requires consistent base normalization and the proved margin rather than assuming q has arbitrary-order unit gaps.

At u=1 only s=0 survives, yielding d_0(q^h;q)_J/D(b). Its factors have original positive exponents up to the above actual footprint; d_0 and D(b) are units. Thus chi(1) really is unit. det A is likewise unit. These facts do not hold for the different singular W_h(C) matrix and are not asserted to do so.

## Dual suffix and scalar-output scope

Every nonsuffix size-r clock subset has an adjacent hole, giving a zero coefficient. The surviving suffix coefficient q^(r(r-1)/2)[h choose r]_q has the right power, including r=h. Its ratio telescopes to D(q^h)/D(q^(h-r)). For r<=J the denominator belongs to the actual original clock because h>J. Monic geometric MPE acquires the J+1 strip values in soft J; a nonunit original strip value must be localized/decoded rather than inverted. D(q^h) is never a denominator. The strip does not cover an arbitrary interior hit.

The acquired chi and implicit A actions are substantive paid operations. Their conversion is a short basis change of D and does not by itself select a clock-intersection branch. The report carefully avoids substituting A eigenvectors for the one-dimensional kernel of W_h(C), or applying a singular W_h diagonal gauge without acquiring its entries. The normal/leave-one-out selector remains unpaid. No new nearlinear selector or universal obstruction is claimed.
