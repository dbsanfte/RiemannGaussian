# Independent shared-triangle and affine-batching audit

24 October 2026. No repository changes or numerical examples. Exact reviewed versions:

| File | SHA-256 |
|---|---|
| shared-triangle-attempt.md | 2cec78cbbb96fe4a04ce5a2930294e55f4c25832f9d190ab4d589ce4d1850356 |
| affine-batching-literature.md | fd6aa51296c5a0ca5d5a39c02c015766aa9baa0e2980965392037d1f012ff089 |

Both files are in /tmp/semiprime-shared-triangles-20261024. Verdict: the exact identities and actual soft-m² batching ledger check. Neither report claims an acquired sub-m^(3/2) whole query.

## Transposition: verified indices and endpoints

Start with the alternative triangle form

    T=product_(1<=i<u) product_(1<=l<=qi)(z+v*i-u*l), v=qu+r.

Write l=q*t+s uniquely with 1<=s<=q and 0<=t<i. Put h=i-t. Then h>=1, t>=0, h+t<u, and the factor becomes

    z-u*s+v*h+r*t.

Thus the report's transposition has no missing diagonal or endpoint. Fixing s,t leaves h=1,...,u-1-t, with start z-u*s+r*t+v and length u-1-t. For first stages v=m this is genuinely a common physical step m. There are exactly q(u-1) such (s,t) starts, so this literal transpose emits at least the original u-1 starts, and does not yield fewer native first-stage requests.

## Reflection: verified sign, complement and lift shift

For the second factor T(-z-um+u), negate its leaves and relabel i by u-i. A leaf index t originally in [0,q(u-i)-1] becomes t'=qu-1-t, ranging over [qi,qu-1]. This complements the first triangle's [0,qi-1] exactly. Negating D=qu(u-1)/2 factors yields

    T(z)T(-z-um+u)
      =(-1)^D product_(1<=i<u)product_(0<=t<qu)(z+r*i+u*t).

The report's sign is correct. Its known-unit scale exponent after converting the rectangle to factorials is 2D=qu(u-1), also correct.

For native reflection, direct substitution gives b_(m-j)+b_j=2a modulo m. Centering puts the integer carry tau in {-2,-1,0}. Hence c_(m-j)=-c_j+ma+H*tau and Z_(m-j)(K')=-Z_j(K)+a+m(tau+K+K'). Equating this with -Z_j(K)-am+a requires exactly K+K'=-a-tau. No sign or factor m is missing. The example lifts 0 and -a-tau fit the stated public menu envelope.

For the affine-batching report's complete B_m factors, z'=1+tau*v-z and v=m/a imply

    1-m-(z'+vK)=z+v*(-K-tau-a).

Using B_m(x)=(-1)^m B_m(1-m-x) verifies its reflection sign and K map. Physical leaves are negatives with h reflected by m-1-h; safe support and original envelopes therefore transfer. Neither first-stage triangle pairing nor full-row reflection proves a smaller covered menu; both reports explicitly retain that gap.

## Initialized batching complexity

The common B_(2^k) degrees sum O(m). A supplied AP of length <=m decomposes into O(log m) acquired shifted evaluation targets; monic MPE in each degree layer has total soft(m+r) cost for r APs. No evaluated factor or node difference is inverted. All small normalization steps are certified units.

The Euclidean u entries sum O(a_j) per row. In the native first stage each a value has at most two preimages, so a positive fraction of rows have a_j>=m/4 and sum_j(a_j-1)=Theta(m²). The literal emitted target count is therefore quadratic, not merely an upper estimate. Common polynomial construction costs soft m while actual point acquisition and MPE cost soft m². Transposition and first-stage reflection preserve a quadratic explicit-start count. This is an implementation audit, not a lower bound for implicit product-only algorithms.

The affine-batching degree audits also check: one AP per row is soft(s+r); r length-L collections of B_m arguments explicitly contain rL targets. Forming their monic Q costs rL coefficient/root input before an ordinary resultant applies. Replacing Q by its remainder modulo B_m would suffice but is precisely an unacquired compressed-input primitive. Interpolation of O(m) row metadata is legal but does not remove the O(m²) bivariate coefficient array produced by the stated substitution.

## Narrow primary-source spot check

I freshly opened Neiger–Salvy–Schost–Villard's 2026 author PDF and the ESA 2025 trimmed-evaluation primary publication. The former indeed presents field arithmetic, genericity assumptions and the reported generic composition exponent; the latter evaluates on a specified trimmed point grid in time measured against its size. Neither critical claim supplies compressed affine-line norm acquisition. [2026 primary PDF](https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/comp2.pdf), [ESA primary publication](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2025.89).

Other bibliography entries were not independently re-audited here: the algebraic acquisition conclusions above do not rely on their strongest stated bounds. There is no claim that this review proves absence of an unlisted theorem.

## Reciprocal transport plus reflection: actionable scope

The native label maps j->-j and j->[N/j]_m commute and are involutions. Therefore their joint label orbits have size at most four; all such orbits and their exact carries can be acquired in soft m. Reciprocal transport changes the slope a to its modular inverse, while reflection keeps a. This groups slope classes into at most inverse pairs, not an unbounded collapse.

The corrected native-row-pairing.md supplies an exact map to the partner's normalizable lift class. Crucially its normalized leaf is the ORIGINAL L_j itself, not L_j divided by a small integer. In direct coordinates it is simply

    L_j=m*(d+a*h+m*k)-j*, d=(c_j+j*)/m.

Consequently composing that map with a sign reflection does not by itself shorten the original integer range: it preserves these leaves up to known units/signs and introduces the explicit carry shear. A putative menu reduction must prove coverage for the image domains, including their enlarged lift range, rather than reuse the partner's original short-menu screen.

An actionable safe algorithm is to form the <=4 exact image domains per label orbit, retain one copy of an explicitly acquired duplicate leaf, and evaluate the union with the existing AP/triangle engines. Reflected interval endpoints cost soft 1 per orbit; reciprocal carry-dependent intersections cost soft 1 per supplied h, hence Theta(m²) h targets in the literal full-family implementation. Formal quotient cancellation is unsafe until the canceled product is tested: it might contain the only hit. Keeping one copy preserves support without division. This gives a valid simplification and recovery rule but no proved smaller K covering menu or improved exponent.

No new root-gap reflection identity is developed here; that work is assigned separately. The precise positive missing statement remains a covered small union invariant under these integer carry maps, or a shared scalar acquisition that handles their full image domains without emitting the quadratic targets.
