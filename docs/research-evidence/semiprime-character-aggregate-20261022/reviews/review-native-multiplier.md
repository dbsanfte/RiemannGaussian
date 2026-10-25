# Independent review of native multiplier closure and recursion

22 October2026. Reviewed native-multiplier-closure.md, multiplier-recursion.md and the repaired twist-norm-aggregation.md. Algebraic verdict: PASS. The exact identities and low-digit limitations are correct. The full correction/localization ledger is specified below; it remains soft(m+JK), not softm, for the literal complete recursive tree. No new long-query evaluator or compressed dyadic state action is proved.

## Native cubic/tag identities

With M=m³,e_j=N+a_j+v_j,v_j=ell_j−m²kappa_j, one has v_j²=4a_jN modM and v_j=−2a_jj modm. Since a_j=N j^(−2) modm,

    e_j=N(j^(−1)−1)² modm.

At depth h let b=2^h. The direct no-root recursion indeed uses base q^b and original-origin targets gamma^(e_j−Mt),0<=t<b. Canonical powered-target reuse up to the common stride Q^b requires the INTEGER equality

    e_j=b e_k+M(t+b u), u∈Z.

It is equivalent to the cubic congruence e_j=b e_k modM and the compatible quotient carry class modulo b. The modm square equation in the report is necessary, and its two Mobius candidates follow by taking the two square roots of b. When b is nonsquare, both square arguments must vanish, so j=k=1 is the only possible low-digit candidate. Passing this low-digit test alone says nothing about the cubic congruence/carry.

For c>0 with gcd(c,m)=1 and c²a_j<m, k=j/c modm has canonical a_k=c²a_j exactly, because both are representatives in[1,m). The root c v_j has the correct residue−2a_k k modm, and its derivative2c v_j is a unit modm. Hensel uniqueness therefore gives v_k=c v_j modm³, with an acquired bounded integer carry s=O_c(1). Expanding e_k−c e_j gives(1−c)N+(c²−c)a_j+Ms, exactly the point identity displayed. For wrapped a_k=c²a_j−mw,v_k=c v_j+mT, expansion and division by m give precisely

    4wN+2c v_jT+mT²=0 modm².

T is generally a residue modulo m², not a bounded stride-M carry. All claims are correct and remain metadata acquisitions rather than H evaluations.

**Equality scope.** Exact integer exponent reuse above is sufficient for public scalar equality and supports the original exponent ledger. Scalar equality modulo a hidden prime may ALSO occur because an exponent difference is a multiple of its hidden local order. Thus “necessarily” in the report's reuse paragraph should be read as necessary for literal INTEGER-exponent identification up to the stated common stride, not necessary for every accidental local-order coincidence. Without that qualifier it would overstate the test. No unknown-order equality oracle is acquired by these congruences.

## Carry identity, signs, endpoints and full tree cost

For r'=2r modm, c=floor(2r/m), one has r'=2r−mc; since m is odd, c=0 iff r' even and c=1 iff r' odd. Hence A and Q^D H_e(X/Q;q²,K) supply n'=0,...,2K−1 in the even channel and1,...,2K in the odd channel. Adding the lower missing factor and multiplying the upper surplus factor gives exactly

    L(X) A(X) B(X)=U(X) H_e'(X;q,2K).

The Q^D scale is correct. The endpoint q^(r'+2mK) is indispensable. A length-one terminal block and an odd-length last block have degree d0=(m+1)/2 and are explicit. K=0 is the empty product. The source-squaring sign(-1)^D is also correct, and plus factors are units for odd-subgroup targets.

At level h, let b=2^h and K_h<=ceil(K_initial/b). There are at most Jb materialized target requests. Endpoint/one-block root catalogs have O(m) roots per palette and per length type; only O(1) different lengths occur at a level. Product trees and batched monic MPE therefore cost soft O(m+Jb) at that level, including every correction OUTPUT. Repeated targets are allowed but no unproved deduplication is credited. Through depth ceil(log2(max(1,K_initial))), the sum is

    soft O(m log(K_initial+1)+J K_initial),

and terminal constant-K values cost the same J*K_initial scale. For J,K_initial~m this is softm². This is a proved ledger for the displayed explicit tree, not a lower bound against compressed computation.

The coherent-root-direction formulation is also paid for original input chains by initial rebasing. But that does not pay its branching shifted origins. Native source/recovery remains easiest to state in the equivalent direct no-root formulation, avoiding any fractional gamma exponent interpretation.

## Nonunit correction localization over ALL levels

The complete tree need not be evaluated after a useful correction is found. At the current acquired node values take gcds with N. A proper gcd ends factoring. A saturated endpoint product can be descended through its degree-O(m) monic root tree; evaluating uncached children by Horner has a geometric degree sum O(m), so one such localization adds softm. It is invoked at most once, provided its scalar leaf has a certified nonzero original gamma exponent. This cost is in addition to the cumulative endpoint requests already charged above, not an unproved fixed-level-only screen.

The retained large native regime supplies a uniform ledger margin for all these endpoint leaves. Write the direct depth-h target gamma^(e_j−Mt),t<b and base q^b. A correction root has form(q^b)^(r+2mK_h), or its lower/odd-final-block analogues, where0<=r<m. After restoring y normalization, its original scalar index is

    I'=kappa_j+m t+b r+2m bK_h.

All are nonnegative. With b<=2K_initial and bK_h<=K_initial+b, this is less than

    m+4mb+2mK_initial<=m+10mK_initial.

Here mK_initial<=L<=4m² (or one harmless final ceil-block can be charged with the same enlarged constant). Thus a conservative bound I'<m+40m²<=41m² holds for the displayed floor-length recursion. Native E_j>N−3m²>256m⁴−3m² exceeds41m⁴, so E_j−m² I'>0. Lower and final-block corrections obey the same bound. Consequently every discovered saturated scalar leaf supplies a nonzero O(log N)-bit gamma annihilator for the original decoder. The general symbolic statements outside this regime must retain their explicit public ledger check; the source report correctly warns against treating integer-trivial zero leaves as useful.

## Norm collapse is a DIFFERENT fiber

The paid degree-J polynomial product_j(U−x_j^b) collapses the full root-of-unity fiber of each original x_j under T→T^b. Actual dyadic states are gamma^(e_j−Mt),t<b. Their ratios lie in an odd subgroup and are not the nontrivial b-power twists of a single point. Power b is injective on that subgroup, so taking bth powers does not merge these shifted-origin states. The norm collapse does not establish a degree-J representation of the actual recursive target family, and the repaired report now says so explicitly.

Likewise an arbitrary globally nonidentity element of a product etale algebra can specialize to1 in some components. The repaired norm report correctly uses nonzero LABELLED powers of a componentwise primitive bth root, or primitive cyclotomic strata; more simply, local support follows directly from injectivity of bth powering on each odd subgroup. No unsafe global-nonidentity-to-unit inference remains.

## Requested narrow clarification and outcome

One wording clarification is actionable: qualify native-multiplier-closure.md's “necessarily” reuse test as literal integer-exponent/stride reuse; it is not a test excluding local-order coincidences. The short root paragraph in multiplier-recursion.md predates the paid coherent-root report; its statement that h levels can be prepaid is correct, but no hidden-order extraction barrier remains for the ORIGINAL input chains. Neither clarification changes the explicit branching cost or proves an evaluator.

Only this new review and the requested repairs to this agent's own twist-norm-aggregation.md were written. No source-report edits, repository edits, finite examples, backend, or agents.
