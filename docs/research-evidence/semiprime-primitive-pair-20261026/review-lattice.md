# Independent review of the lattice-product and finite Appell candidate

26 October 2026. Scratch paper review of `lattice-product.md`; no tests or repository changes. **The discriminant diagnosis and finite denominator controller are valid, with the nonprimitive-provenance and Laurent-chamber qualifications below.** Both were communicated to the author before finalization.

## Actual discriminant: all contents, not only primitive rows

The finite clock absorption l=ell−Hi and monomial specialization x=barpi,z=barpi^N,w=pi are exact, with physical signed index retained. At a good-field native exact hit, l=−(aR+bS), S=N/R. Consequently D=4abN−l²=−(aR−bS)².

For content g>1 it is NOT generally true that the hit's colour equals R modulo K. The needed divisibility nevertheless follows without that assertion: every actual stationary phase satisfies ell²=4abN modulo H; substituting the exact-hit equality gives H|(aR−bS)². Prime-by-prime valuation then gives K|(aR−bS). Thus D=−Hu² for every native good hit, including added valid colours, nonprimitive rows and axes. Nonzero u follows because aR=bS would force S|a and R|b, impossible for a nonzero native pair with |a|,|b|<=K<R,S. This proves the strong stated diagnosis without an invalid full-tag premise.

The primary Gritsenko–Nikulin PDF was opened independently: equation (1.9), PDF page 11 (printed page 11), explicitly defines the coefficient support and states f(0)=10, f(−1)=1, and f(D)=0 for D<−1. Hence its finite native factor assignment genuinely deletes all the exact native witnesses. The infinite product's chamber and analytic setting do not repair that absent multiplicity. The conclusion is source-specific, not a no-go for every denominator or for all arithmetic specializations.

## Appell algebra and the necessary chamber distinction

The primary DMZ PDF was opened independently at §8.2: equation (8.9), printed page 54, is the averaging operator used in the report. Its immediately following (8.13)–(8.15) explicitly distinguish the two Laurent chambers. For the report's own input F(T)=(1+T)/(1−T),

    F(T)=1+2*sum_(k>0)T^k       in the positive chamber,
    F(T)=−1−2*sum_(k<0)T^k      in the negative chamber.

The algebraic exponents n=ms²+sk, l=2ms+k and discriminant −k² hold for either sign of k, but the native k=aR−bS can be negative. Therefore s=−R,k=aR−bS is a valid finite polar parametrization; it is NOT proof that every native monomial occurs with nonzero coefficient in one fixed positive-power Appell expansion. Different signs/chambers and their coefficients must not be silently combined. Signed a,b sectors additionally need their own positive-index treatment. No full Appell-sum or modular-completion identity over B is established by this matching calculation.

The finite root filter (1/K)sum_r F(omega^r T)=(1+T^K)/(1−T^K) is an exact rational identity. K is a certified unit modulo N; its right side requires no implementation extension. It is not evaluated by inverting a singular denominator. Importantly the finite denominator cover 1−(pi*barpi^s)^K is independent of which Laurent chamber displays a proposed Fourier monomial. This preserves the useful finite arithmetic test despite the Fourier-scope qualification.

## Native units, winding controller, and readout

At the nonsplit field pi^R=barpi and pi^(R²)=pi, so s=−R makes that denominator zero. The rough local orders make K powering injective at every component, so the Kth power adds no extra component zeros. No hidden order is acquired. For a supplied winding interval of length B, the division-free scalar product engine and its bounded localization cost soft sqrt(B). A proper norm/coordinate gcd factors; a global torus equality supplies scalar beta^(2(1+s))=1 with an O(log N)-bit label. For s!=−1 the label is nonzero, licensing the existing once-only terminating extractor. The exceptional s=−1 is explicitly handled with the already supplied W-order exclusion. This is a finite denominator controller, not evaluation of a complete Appell sum.

Using only the unknown nonsplit R gives the uniform bound R<N/(16H), possibly length Theta(K^4). Thus the literal original winding controller can cost soft K². Any better interval, alternative winding/target, or either-factor completion must be explicitly charged; its existence is not inferred from the negative-square parametrization. The endpoint/pole target and any custom weighted residue must still preserve nonzero total weight at the good characteristic.

Primary sources checked: [Gritsenko–Nikulin](https://arxiv.org/pdf/alg-geom/9603010), equation (1.9); [Dabholkar–Murthy–Zagier](https://people.mpim-bonn.mpg.de/zagier/files/arxiv/1208.4074/1208.4074v1.pdf), §8.2 equations (8.9), (8.13)–(8.17). No analytic convergence or modular symmetry is imported as a finite-ring evaluation algorithm.

## Final stable-draft and alternative-winding review

I read the author's corrected §§2,5 and the new §6. **Final PASS; the nonprimitive and chamber corrections are integrated.** The actual conic now proves D=−Hu² for all contents. The text explicitly treats (s,k) as an algebraic polar parametrization and does not place both signs of k in one positive-power chamber.

The new alternative-winding equation is exact: eliminating k gives a s²−l s+bN=(s+R)(a s+bS). Thus the only candidates are −R and −bS/a, not freely −S. For an actual shortest row with g=1, any common divisor of a,b is coprime to K; dividing it preserves the lattice and strictly shortens the row, so gcd(a,b)=1. The monic exception is therefore correctly limited to |a|=1 (a=1 in the positive-index sector), with |a|<S. This assertion is not transferred to arbitrary admitted hyperbola pairs.

The changed target pi^N*barpi^s is correctly labelled a different finite arithmetic cover. At s=−S it vanishes at the good field, and combining it with the original target covers one exponent <=sqrt N. That gives the stated soft N^(1/4)=soft K^(3/2) controller, not a fast native Fourier identity.

Finally, the direct saturated-leaf decoder is sound. For s=−x in the stated hard factor range, K-power injectivity and Frobenius give x=R modulo ord(pi) for the original target and x=S modulo ord(pi) for the modified target. Both ranges are shorter than the good order, so these are literal integer equalities and gcd(x,N) factors. It avoids a terminating extractor but does not shorten the winding search. No global split-component short-unit guard is needed by this monic zero/nonunit controller. No additional substantive correction is required.
