# Natural channel Padé sequences see the nonhit factor, not the small hit locator

2026-10-16. Transfer of an ALREADY FROZEN moment obstruction to a particular channel-Pade interface, plus an elementary precision observation. No substantive acquisition advance, uniform nearlinear extractor or general lower bound is obtained. The nonhit denominator and Hankel argument were already proved in the compressed-query packet; their channel formulation here only changes known unit weights and uses the powered distinct nodes. The natural rational channel syndromes have minimal recurrence order J-h, whereas the desired hit gcd has degree h=o(J). Simultaneous ordinary Padé constraints at precision <=J-h are vacuous under their natural numerator bounds, even if proper channel remainders are granted for free. Cross-channel source identities or different nonlinear extraction remain open.

## 1. Actual input and rational sequence

Work first in either hidden field K. Publicly deduplicate the literal nodes z_j, use the balanced dyadic B, and put y_j=z_j^B. The retained odd-prime local-order promise makes both z_j and y_j pairwise distinct. Let

 D(Y)=prod_j(Y-y_j),  deg D=J,
 M_r(Y)=N_r(Y) mod D(Y),  deg M_r<J,
 H=gcd(D,N_0),  deg H=h.

Changing the frozen constant-one D_B to this monic D only scales known units. The paid polyphase identities give

 M_r(y_j)=z_j^(-r) N_0(y_j), 0<=r<B,
 N_0(y_j)=0 iff F(z_j)=0.

All multiplier factors in the latter equivalence are units on this branch. Therefore every channel has EXACTLY the same field-side gcd H with D. For d=J-h>0, each proper rational function

 R_r(Y)=M_r(Y)/D(Y)

has reduced denominator D/H of degree d. The actual row-density theorem gives h=o(J), so d=J-o(J), rather than an output-sensitive small denominator. This statement uses actual source identities, not generic coefficients. The all-hit case d=0 gives zero sequences and is excluded only when invoking the retained density qualification.

## 2. Transferred minimal recurrence and interleaving scope

The frozen source is semiprime-compressed-query-20261015/reports/sparse-intersection-interface.md, sections "A concrete Prony/Pade proposal fails on the actual source" and "What a genuinely collision-selective syndrome would require". The following reproduces that same mechanism for the present channel variables; it is not a new arithmetic obstruction.

Write the partial fractions at the NONHIT nodes as

 R_r(Y)=sum_(j nonhit) lambda_(r,j)/(Y-y_j),
 lambda_(r,j)=z_j^(-r)N_0(y_j)/D'(y_j) !=0.

Its expansion at infinity is sum_(k>=0) s_(r,k)Y^(-k-1), where

 s_(r,k)=sum_(j nonhit) lambda_(r,j)y_j^k.

The d-by-d leading Hankel matrix s_(r,a+b), 0<=a,b<d, factors as V diag(lambda_(r,j)) V^T, with V the square Vandermonde at the distinct nonhit y_j. Its determinant is nonzero. Thus each infinite scalar sequence has minimal constant-coefficient recurrence order EXACTLY d. The denominator D/H supplies a recurrence of that order; a smaller recurrence would make this Hankel matrix singular. Consequently the common minimal recurrence of any nonempty channel collection is also D/H, with order d. Increasing the number of these unmodified interleavings does not turn its true recurrence into the degree-h hit locator.

This does not assert that every useful multisequence transformation has order d. For example a new transformation could eliminate the dense nonhit residues or construct a genuinely hit-supported syndrome. No such transformation with paid inputs has been found here. Small h does not itself supply it.

## 3. Why tiny ordinary Padé precision gives no denominator constraints

Grant, favorably, the proper remainders M_r for free, choose the regular center Y=0, and consider the Taylor series of R_r there. All y_j are units, so D(0) is a unit; the reduced denominator can be normalized to constant one. Its natural numerator degree is <d.

At any precision nu<=d, EVERY polynomial lambda with lambda(0)=1 and deg lambda<=d satisfies the ordinary simultaneous Padé congruences with numerator bound <d: simply choose each numerator as (lambda R_r) mod Y^nu. It has degree <nu<=d. This is true for any number of channels and any supplied series coefficients. Therefore these congruences cannot single out the true denominator at such precision. At least one additional coefficient beyond d is necessary before this specified formulation imposes even one tail constraint. This is a concrete vacuity statement about that approximation problem, not an information lower bound for our structured source.

The raw quotients N_r/D also have polynomial parts. Removing those parts is not free, and allowing the larger raw numerator bounds does not repair the low-precision vacuity. Known special coefficient bounds, source-dependent numerator constraints, public cross-channel relations and different approximant problems may change the conclusion and require their own construction/uniqueness argument.

## 4. The syndrome data are not the paid point-vector oracle

The paid scalar-X SLP returns all N_r(X) in soft O(J). Lifting a size-s circuit routinely to precision nu costs O(s M(nu)) ring work up to logarithmic factors, with all B*nu output coefficients charged if materialized. For s,B,d=Theta(J), using nu=d+1=Theta(J) via that routine is softly quadratic work and quadratic explicit series output, not the desired nearlinear acquisition. This is the cost of that implementation, not an operation lower bound; a specialized jet routine remains possible. With O(log N)-bit residues the same routine has soft O(s*nu*log N) bit cost under fast integer/polynomial arithmetic; no hidden field or free inversion is supplied.

At infinity one must acquire the PROPER rational parts before using the moment formula. IF B>=J, its zeroth moments across r=0,...,J-1 are

 s_(r,0)=sum_j [N_0(y_j)/D'(y_j)] z_j^(-r),

including the hits as zero summands. This is an invertible known Vandermonde transform of the complete N_0 node-value list, followed by unit diagonal scalings. All transform/setup costs are softly O(J) under the stated unit-difference promises, so acquiring this complete moment vector would already acquire all original row values. It is a useful conditional target, not free input supplied by scalar evaluation at a center. When B<J there are only B available zeroth moments; the transform is rectangular and no full-row recovery is claimed. A balanced dyadic choice alone does not imply B>=J. Our denominator theorem is field-side; over Z/N all Padé pivots and candidate cancellations need factor-aware proper-factor/unit/saturation handling.

## 5. Focused primary interfaces

Rosenkilde and Storjohann, Algorithms for Simultaneous Padé Approximations (ISSAC2016), primary author PDF https://cs.uwaterloo.ca/~astorjoh/issac16.pdf . Inspected Problem1, the solution specification and algorithm bounds. The INPUT is a list of polynomial approximants S_i, moduli g_i and numerator/denominator degree bounds. Theorem20 (printed page411, PDF page7) says, "Algorithm 3 is correct. The cost of the algorithm is" followed by O(n^(omega-1) M(d) (log d) (log(d/n))^2), where d=max_i deg g_i. This is the maximum modulus degree, not a sum-degree parameter. As in the paper's abstract, soft notation gives O~(n^(omega-1)d), with its customary logarithm conventions and fast polynomial arithmetic. The output is a compact reduced solution specification. It does not acquire series coefficients from an SLP or prove that the desired common factor is selected by arbitrary bounds. At n~J and required precision~J its stated arithmetic bound is not nearlinear. Compact output is genuine but does not make unacquired input series available.

Yu and Loeliger, Simultaneous Partial Inverses and Decoding Interleaved Reed-Solomon Codes, primary https://arxiv.org/pdf/1612.07854 . Inspected the SPI formulation, key equations, partial-inverse condition and complexity propositions. Its small error locator is characterized under an error-pattern condition with supplied received/syndrome data. That condition is not implied by a small gcd of unrelated polynomial outputs. In the direct channel rational functions above, the poles occur on the dense NONHIT support, not on the sparse hit set. Importing an interleaved decoder would need a paid hit-supported syndrome or another proved coding-model reduction, including its success condition. No such reduction is supplied by the vector point oracle alone.

The two primary PDFs and exact extracted text are saved and hashed beside this report. This is a targeted interface audit, not a comprehensive new literature catalog and not a claim that all Padé/approximant algorithms fail.

## Outcome

No new soft O(J+sqrt L) locator or sufficient factor query has been acquired. This note does not close a new arithmetic route beyond the frozen moment obstruction. It transfers that obstruction to ordinary proper channel series and observes that their standard independent-numerator Padé constraints at tiny precision are vacuous. The denominator is nearly full degree and those specific tiny-precision congruences have no selecting power. Transformed cross-channel relations, the SPI partial-inverse condition when separately proved, tighter coupled numerators and specialized jet acquisition can evade the stated formulation. No general jet-precision or jet-computation lower bound is claimed. Other structured extractors, compressed approximant representations, nonlinear transforms, low-precision identities with additional source constraints and norm-only algorithms remain possible. No frozen artifact, native declaration or backend was changed; no numerical examples or broad builds were used.
