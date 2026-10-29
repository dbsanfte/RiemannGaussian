# Independent review: fractional twist interpolation

26 October2026. Read-only algebraic review of `fractional-twist.md`; no new experiments or repository edits. The forced-root construction, whole-family identity and recovery limitations are correct. One degree-comparison explanation in Section5 should be sharpened as described below; it does not affect the exact identities or the direct pole test.

## Forced factor and initialized skein realization

The source negative-twist scalar F_U follows by substituting A=(U−1)/(u−1) and H=((u+1)A−2s)/(u−1) into the previously audited formula. Solving F_U(w)=0 gives the displayed U_* when its denominator is a unit. Clearing that denominator gives exactly

    J_v(B)=(B−w)[−(u+2sw)B−u(d+w)].

Its constant, linear and quadratic coefficients respectively are u w(d+w), 2sw²−ud, and −u−2sw. Thus no discarded scalar or unlicensed inverse is present. The identity is polynomial and survives every nonunit/degenerate specialization.

The three fixed scalar states span quadratics: D_1=alpha B+beta B² and D_2=alpha(u+1)B+beta(u+3)B² have determinant2alpha beta=2(u+1)/u², a certified unit. The printed inversions for B and B² are correct. This realizes J_v as a finite linear skein element over the coefficient ring, and does not assert existence of an integer twist with u^s'=U_*. At a nonunit denominator, a proper gcd factors; a saturated gcd is not an annihilator. The cleared construction remains defined without dividing in that branch.

## Whole-family and exceptional branches

The native pair factor satisfies

    P_s=(s²/u)(B−w)(B−w'),
    w+w'=−(u+1)/s, ww'=u/s²−d²/s.

Consequently the full identity J_native=C P_native E_native has precisely C=u^L/product_j s_j². C is a known unit. The extra product and all scalar coefficients have paid soft-O(L) acquisition, but this acquires no clock norm. Both orientations are needed and are explicitly present. Multiplicities and zero-divisor coefficients cause no problem for product-tree multiplication.

The stated favorable degeneracies are correctly conditional. In particular d+w=0 does not imply u+2sw is a unit; the relation u+2sw=u(1−2/v) on that locus follows using v²−2uv+u=0. If both extra coefficients vanish, J_v is identically zero and unusable. The fallback direct monic factor B−w remains lawful, but restores the original query. Claims about harmless v=u or u^-1 rows require exactly the stated short positive odd-clock range and the existing order guard; they are not assertions about arbitrary integer clocks.

## Telescope scope and one precision correction

The extra-root expression has its generic finite pole at v=u/(2−u), while a fixed multiplicative shift/inverse-shift B(cv), B(c/v) has only0/infinity poles. This correctly excludes those direct rational-map identities only. It neither excludes exceptional u nor collective native catalogue cancellation.

Equation(8) follows by writing ell_v=−A−C_B w and multiplying: its cross term uses w+w' and its constant uses ww'. The expanded s² E_pair has the stated nonzero cubic term −4s³d² B². The following sentence's degree argument should specify the normalization it compares: “P_s is degree2 in s, whereas s² E_pair is degree3” directly excludes s² E_pair=U(B,u)P_s(B') with row-independent U,B'. It does not, as written, directly compare E_pair=U P_s(B'), because multiplying that latter equation by s² also multiplies its right side by s². The latter simple pullback is nevertheless excluded generically: s² E_pair has constant coefficient u³ at s=0, while s² U P_s(B') is divisible by s². This is a formal rational-function check with s indeterminate; native s and v are related, so retain the report's limited simple-pullback scope rather than asserting any broad native nonidentity theorem. The exact factorization and q-shift pole argument require no amendment.

## Collision decoding remains correctly separated

At a physical clock,

    B(a)−B(v)=−(a−v)(a−u/v)/a.

The second factor means the other argument b=u/a equals v. Scan the actual two differences when a product is saturated: mixed CRT signs can give proper gcds even without one globally zero difference. A saturated genuine difference has its original nonzero signed exponent label and the licensed annihilator consumer, subject to the existing deletion proof. No inverse of a collision factor is required.

An extra-factor zero has no such decoder. A proper gcd of its scalar value factors; a saturated additive/rational relation does not supply beta^K=1. In particular a hypothetical cheap J_native norm is insufficient unless the extra orbit is controlled or decoded. Cancellation before specialization via the directly acquired monic original factors is safe; division by evaluated E_native is not. The report consistently preserves this distinction and claims no whole-query or coverage gain.

Integration resolution: the archived report removes the disputed degree/pullback conclusion altogether. It retains the exact paired extra polynomial and the independent generic-pole test for fixed multiplicative shifts. No native substitution obstruction is inferred.
