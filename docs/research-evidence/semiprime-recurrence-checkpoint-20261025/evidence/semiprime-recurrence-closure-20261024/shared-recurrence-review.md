# Independent shared scalar recurrence audit

24 October 2026. **PASS. No required corrections.** Reviewed exact `/tmp/semiprime-recurrence-closure-20261024/shared-recurrence.md`, SHA256 `654218a0e5dde8e0261ea662cf40c8ceb82e5e152cebebb4542b831f0b322562`. Read its full predecessor `frobenius-pairing.md`, SHA256 `215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`, and the independently pinned PASS review `147ed84ea489fb61e8e2b47e2c6d09a90cf247f743df017e48314b613f815a97`. No source/repository edits, examples or new external theorem required.

## Common quartic, signs and actual starts

For t=Norm(z) and s=Tr(z), direct expansion gives

    (T-1)(T-t)(T²-sT+t)
      =T⁴-(1+t+s)T³+[2t+s(1+t)]T²
           -t(1+t+s)T+t².

Thus both quartic coefficients and all signs in recurrence (3) are correct. Expanding Norm(V_j-z^i) gives exactly Norm(V_j)+t^i-bar(V_j)z^i-V_j*bar(z)^i. Each of the four bases 1,t,z,bar(z) is annihilated in B by the displayed polynomial. Multiplying the identity by its actual coefficient proves the scalar recurrence, with no eigenvalue decomposition or denominator.

Consequently repeated spectral values, zero/nonunit trace discriminants and zero collision values introduce no exception. t² is a unit, but forward evaluation uses only multiplication and addition. The monic quartic allows T^i reduction and a linear combination of the four supplied starts in O(log(i+1)) constant-size steps.

The starts are genuinely supplied: the predecessor acquires ALL actual rank-two V_j coordinates and z in soft k. z^0,...,z^3 take constant work, and each of four norms per row is constant-rank arithmetic. All row starts and common coefficients therefore cost soft k including bit costs. This is a recurrence for actual source values, not merely four unacquired amplitudes.

## Norm recovery uses the new constructor's exact hypotheses

The predecessor's Jacobi-minus-one discriminant supplies exactly one unknown nonsplit local field. A proper norm gcd factors independently. At a saturated ORIGINAL norm leaf, norm zero at that field implies the whole local element and its conjugate vanish. The same-leaf beta-coupled ideal identity then supplies a nontrivial scalar beta gcd, or a globally saturated original bounded beta leaf. The prepared odd local orders and original global margin license its existing decoder. No survival/order bound for W or arbitrary split-coordinate norm pairing is assumed.

The synthesis correctly limits this recovery to the actual sequence defined by the rank-two constructor. It does not assign a decoder to an arbitrary recurrence with the same coefficients. Its final discussion also distinguishes this NEW constructor from compression of old rank-k Gauss vectors.

## Family expansion and monic annihilator

The row product satisfies

    product_j Norm(V_j-z^i)=Norm(F(z^i)).

Although F(z^i)=(-1)^J product_j(V_j-z^i), that sign has rank-two norm one; there is no missing scalar sign. Multiplying F(z^i) by its conjugate gives exactly

    sum_(a,b) f_a*bar(f_b)*(z^a*bar(z)^b)^i.

Diagonal a=b terms have scalar bases t^a and scalar coefficients Norm(f_a). For each a>b, pair its term with b,a: their bases are conjugates w=z^a*bar(z)^b and bar(w), their sum is Tr(w), and their product is t^(a+b). Hence the indicated quadratic annihilates BOTH terms, including arbitrary conjugate coefficients. The product (5) is therefore a scalar monic annihilator of g(i) over R.

There are J+1 linear factors and J(J+1)/2 quadratic factors, giving EXACT displayed degree (J+1)² and leading coefficient one. This remains its degree after specialization even when factors coincide, because all factors are monic. It does NOT prove that the minimal recurrence has that order, and the source explicitly refuses that inference.

## Complete initialization and charged terminal scope

For a>b, w=t^b*z^(a-b), so Tr(w)=t^b*Tr(z^(a-b)) exactly. Both arrays of length O(J) are acquired by power walks and the scalar quadratic trace recurrence, at soft J. Enumerating O(J²) actual factors and multiplying them by a product tree costs soft J², as stated; compact access to these arrays is not counted as free expansion of the annihilator.

Acquire (J+1)² actual consecutive nodes z^i by a rank-two power walk, perform monic MPE of the actual F, and take every norm. This gives all required initial g values in soft J² even with repeated nodes or zero values, because only monic divisions are used. Node acquisition and every output are included. No unknown local eigenvalues, target separation, diagonalizing inverse or simple-root assumption is required.

A supplied linear annihilator and its starts do not themselves compute the multiplicative endpoint product_i g(i). The source retains that additional obligation, and keeps the cheaper full original blocked query soft(J+sqrt(JL)) with its actual norm localization and bounded-leaf recovery. The current synthesis neither treats a constant-order row recurrence as a constant-order family-product recurrence nor calls a compact outer-product coefficient descriptor an initialized large recurrence.

## Verdict

All quartic/family identities, scalar coefficient claims, initialization costs and nonunit cases check. The only recurrence-order claim is the valid supplied upper annihilator, not a minimal-order lower bound. The paid rank-two constructor/recovery and shared recurrence are positive supporting results; the long terminal product remains unacquired at soft k, and no factoring-exponent or complete backend advance is asserted. Exact reviewed bytes pass.
