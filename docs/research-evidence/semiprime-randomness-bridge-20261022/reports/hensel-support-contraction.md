# Native Hensel geometry: exact Morse mask and a paid critical-channel query

2026-10-22. Scratch-only constructive support attempt. Inspected the frozen colour-retention/composite-character README and palette contracts first. The first-level translated square palettes are inherited, not a new acquisition result. This report proves the all-precision form, then resolves exactly which part can be contracted. It does not acquire the remaining whole query.

## Exact Hensel normalization, retaining the index carry

For clarity choose the already-paid odd PRIME row modulus m. Every native unit tag j has a=N j^(-2) modm, centered b and ell=mb−2aj, with

 N=aj²−mbj+m²c,        E=N+a+ell.

There is a unique m-adic root R of aR²=N with

 R=j−mb/(2a) modm².

It is public: Hensel lifting uses inverse2aR, a unit modulo m, and coefficients N,a,j. Obtaining any fixed number of base-m digits costs polylogarithmic work per row. This is a root in the public m-adic ring, not a root in either hidden field and not a replacement for beta.

Since 2aR+ell=0 modm², put kappa=(2aR+ell)/m² in Z_m. For the true integer P≡j modm, the source quotient is I=(aP+N/P+ell)/m². The exact identity

 aP+N/P+ell = 2aR+ell + a(P−R)²/P

gives

 I=kappa+(a/R)u²,     u=((P−R)/m)/sqrt(P/R).                (1)

Here P/R=1 modm, so its unique square root congruent1 modm exists. It is a proof-side expression for unknown P, not an acquired hidden input. Formula(1) is an exact necessary mask at EVERY m-adic precision. To compute kappa modulo m^t, acquire R modulo m^(t+2), with the selected Hensel branch; this retains the actual higher carry. Replacing kappa by its first digit at higher precision would be incorrect.

The map h=(P−R)/m -> h/sqrt(1+mh/R) has unit derivative and reduces to h modulo m. It is therefore bijective modulo every m^t by ordinary unique lifting. Thus as P ranges through its entire m-adic residue class, the image is exactly kappa+(a/R)*Squares(Z/m^t). Restrictions to the actual finite integer factor window may only reduce this image.

Modulo m this recovers the inherited native mask kappa+(a/j)*Squares; its sign is Legendre(a/j)=Legendre(Nj). The original exponent congruence E=N(1−R^(-1))² modulo m² also follows from aR²=N and ell=−2aR modulo m², with every equality here understood at its stated precision.

## Which higher digits really constrain the source

For prime m, a UNIT is a square modulo m^t iff it is a square modulo m. Consequently every noncritical residue

 I−kappa !=0 modm

that passes the first quadratic-character test passes at every higher precision. No new higher-digit restriction on these unit classes follows from(1).

All extra restrictions occur in the critical residue I=kappa modm. For example at precision m², its allowed difference must be0 modulo m²; the other m−1 lifts of that residue have odd valuation and are forbidden. This is the precise source-specific limitation of iterating this Hensel mask. It is not a lower bound on a more coupled arithmetic construction. For composite odd m the analogous assertion holds independently on each unit local component; the already-frozen CRT palette accounting must be retained.

## A genuinely paid support query for ALL critical channels

Let the original query use ANY row subset and common interval [a0,a0+L), L=O(m²), within the original bounded decoder range. Retain every original delta_j and row label. Let k_j be the canonical first digit of kappa_j, and write

 n_j=ceil((a0−k_j)/m),
 c_j=k_j+mn_j,
 K=floor(L/m),           Q=q^m.

The critical indices in that interval are c_j+mr, r=0,...,K_j−1, with K_j either K or K+1. Both n_j and the extra-endpoint flag are computed exactly from integer endpoints. Define

 G_K(Z)=product_(0<=r<K)(Z−Q^r),
 x_j=Y_j q^(−c_j),      Y_j=beta^(N+delta_j).

The critical-channel product in row j is the known unit q^(c_j K_j), times G_K(x_j), times the single factor x_j−Q^K if K_j=K+1. Thus:

* acquire G_K in soft O(K), using a monic product tree;
* acquire every x_j and endpoint flag in soft O(J);
* evaluate G_K at all x_j by monic MPE in soft O(K+J);
* multiply optional endpoints and take gcds/products, charging soft O(J).

K=O(m), J<=m, so this is a deterministic soft-O(m) BIT support query, including original scalar carries. MPE does not require target differences to be units. No critical-channel difference is divided. Empty K and empty rows are handled by product1 and optional endpoints.

A nonunit output is localized by row restriction and the G_K product tree. Reconstructed i=c_j+mr is in the ORIGINAL supplied interval. A proper leaf gcd factors; a saturated leaf uses the existing canonical bounded factor-sum decoder with its retained delta_j and i. A false-tag hit is still a valid bounded canonical global leaf, so no unknown-own-tag oracle is used. Source preparation and bounded recovery are exactly those in the all-semiprime setup report; no QRH premise is added.

If every critical-channel product is a unit, then the true covered collision cannot lie in any critical channel. One may discard them while retaining the genuine own-factor witness in the noncritical unit-square palette. This is an exact restriction-preserving support decomposition, not a heuristic sieve.

## Outcome and unresolved contraction

The critical channel is now fully computed and can be removed at soft-m cost. This is compatible with, and likely already implicit in, the earlier translated-palette/common-product machinery; it is NOT advertised as a new whole-family acquisition win. It provides a concrete operation against which to test claims that higher Hensel precision would improve the full query.

After that paid removal, all remaining true indices lie in unit-square classes. Their higher Hensel digits are unrestricted by the quadratic geometry itself. The remaining long products on these classes are exactly the inherited nonzero quadratic palettes, whose simultaneous original-scalar acquisition remains unpaid. No finite examples, hidden factor, hidden field symbol or unenumerated CRT menu is used here.

A successful continuation must couple different rows, the integer factor window, or original q-carries beyond the separate m-adic square-image condition. This pass supplies the exact all-precision identity and an actual jointly paid component, but no such coupling and no sixth-rate factorization theorem.
