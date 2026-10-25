# Shared centering, kinetic reuse, and saturated recovery

This follow-up supplies an exact reuse algorithm and a rigorous saturated-match lemma. It does not supply a bound forcing only soft O(m) reused blocks on every input.

## One giant per repeated relation, not per window

For the oriented-lattice relation from quotient-centering.md, direct substitution simplifies its giant exponent to

 E=C0*m^2+B*m*(1-j)+A*(1-j)^2 = KN+Bm+A(1-2j).            (1)

For any windows using the same j,A,K,B, acquire beta^E only ONCE. If their public centers subtract integers l_w, the normalized targets are beta^E*q^(-l_w), q=beta^(m^2). Equivalently retain the one target beta^E and query the union of their integer quotient intervals [l_w-W_w,l_w+W_w]. Merge overlapping intervals, preserving a public row/window witness for each covered integer. This is an actual sharing algorithm: exponentiation is charged once per distinct relation, and endpoints/labels once per remaining interval. It can avoid repeated giant exponentiation when a kinetic reduction returns the same relation.

The merged interval query still needs its startup acquisition. Either enumerate its retained quotient values explicitly and charge their total count, or use the established geometric-query consumer with that total length and number of intervals. A collection of shifted centers is not a free scalar batch. In particular adjacent windows do not authorize division by a collision-bearing product.

## Explicit validity intervals for a kinetic vector

Let |K|<=T and require |A-KN/P0^2|<=delta. For positive K and A>delta, the eligible positive centers satisfy exactly

 sqrt(KN/(A+delta)) <= P0 <= sqrt(KN/(A-delta)).          (2)

Sign variants can be treated directly from the same inequality; coefficients and comparisons use rational squared endpoints, without an uncharged real-number oracle. On a balanced positive-slope segment, (2)'s length is O(P0*delta/|K|), with the corresponding lower estimate when A,delta are appropriately separated.

At the successful one-window parameters T~m^(2/3), delta~m^(1/3), a relation with |K| comparable to T and A comparable to K has a validity scale comparable to m^(8/3), the same scale as the short-quotient window. This observation does not prove a lower bound on sharing. It does show why simply carrying the current vector forward while it remains valid supplies no theorem that the full factor range is handled by polylogarithmically many vectors per row. A kinetic algorithm must bound the TOTAL distinct relations and retained quotient intervals, not just update one basis cheaply.

The available public lattice bases for all j cost soft O(m). Formula (2) lets a candidate relation's whole validity interval be acquired cheaply. I have not proved an all-input soft O(m) cover by these relation intervals, nor a shared contraction over a larger implicit set. In particular a small interval selected separately for each residue j is not yet an every-factor cover.

## Saturated matches: no giant-exponent order assumption is necessary

Fix a TRUE row/window witness and its actual integer quotient sigma=g(h)/P. Suppose all retained/normalized quotient candidates lie in one interval of diameter D, and ord_P(q)>D. If beta^E=q^(sigma') modulo N for a retained candidate sigma', then it also holds modulo P. Source gives beta^E=q^sigma modulo P. Therefore

 q^(sigma-sigma')=1 modulo P, |sigma-sigma'|<=D,

and the local order promise forces sigma=sigma'. Solve

 A(P-j)^2+B*m*(P-j)+C0*m^2 = sigma*m^2*P                (3)

as an exact integer quadratic, and verify candidate divisors of N. A!=0 makes (3) a genuine quadratic. This handles a full-N collision on the true covered witness without assuming |E|<ord_N(beta), and without extracting an arbitrary large-exponent annihilator. The prepared local orders exceed16m^2, so the centered O(m) intervals easily satisfy this contract.

For a normalized target beta^E*q^(-l), the same proof uses sigma-l and the normalized candidate interval. If reused windows are merged into a wider interval, its diameter must be checked again. Alternatively keep bounded intervals with their separate source labels. A whole-N match for an unrelated row/window may fail quadratic recovery; it must not be promoted to a factor. Discarding all full-N-matched targets before the proper-factor batch is safe for coverage only after this lemma guarantees that any true covered target so discarded has already returned its factor.

Proper local-only matches use the standard guarded product/gcd localization. Any scalar leaf where the gcd is N belongs to the full-N case above, with its bounded quotient candidate and source labels. Same-side baby differences are units when the index span is below BOTH local orders. Saturated products require the usual recursive restriction controller; they are not proper factors by themselves. These conditions address recovery independently of the acquisition bound.

## Higher degree: exact source form, not an assumed improvement

A cubic g(x)=A x^3+B x^2+C x+D0 has

 m^3 g((P-j)/m)=A P^3+U P^2+V P+KN,
 U=Bm-3Aj,
 V=Cm^2-2Bjm+3Aj^2,
 KN=D0*m^3-C*j*m^2+B*j^2*m-A*j^3.

At a true modular-root relation its quotient is

 g(h)/P=[A P^2+U P+V+KQ]/m^3.

This offers two derivative cancellations around P0, but the public congruences defining U,V,K and the nontrivial K must be enforced by an actual acquired lattice family. Short vectors divisible as polynomials by mx+j yield identities for every candidate P and cannot be counted as informative factor relations. I have not constructed a higher-degree family with the necessary nontriviality, quotient-width and total row/window bounds. A formal Taylor cancellation alone is not such a theorem.

## Outcome

Paid positive refinements: exact relation reuse via (1), explicit kinetic eligibility intervals (2), and the full saturated recovery proof (3) using ONLY short quotient differences rather than giant exponent size. These strengthen the earlier centered consumer and remove a possible recovery gap. The all-input acquisition still needs a soft O(m) covering relation/interval family or a joint query on its larger implicit family. No such cover or higher-degree improvement is proved here. No lower-bound claim follows.
