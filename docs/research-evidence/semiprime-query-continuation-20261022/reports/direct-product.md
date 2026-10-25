# Attempt to apply the acquired sparse norm directly to the original product

This pass keeps the ORIGINAL scalar differences and reads the frozen dyadic-shared packet as authoritative. No auxiliary H value is substituted for a collision. I did not obtain the desired soft-O(m) original query.

Let F(T)=product_(delta in A)(T−beta^(N+delta)), J=deg F<=m, and S_L(T)=product_(0<=i<L)(T−q^i), q=beta^(m²). Apart from the fixed resultant sign, the desired product is Res(F,S_L). Both orientations of this resultant below retain every original leaf and allow row/interval restriction. No root-of-unity fibre is substituted for the geometric seed set.

## Concrete candidate: a cyclic deformation of the ACTUAL seed polynomial

The newly paid primitive can compute a norm and a fixed-direction tangent, with output precision O(m), without expanding a quadratic rectangle. The natural direct use is to deform a cyclic polynomial into S_L, then take its norm on the ACTUAL target quotient. Write

 S_L(T)=T^L−Y+U(T),  deg U<L.

The polynomial

 D(epsilon)=Res_T(F(T),T^L−Y+epsilon U(T))

has epsilon-degree at most J. Consequently its ENTIRE epsilon polynomial is contained in a prefix of length J+1=O(m), and D(1) is the original resultant. This is an exact potentially favorable precision bound; it does not require the full epsilon degree L. It is also restriction stable: F is simply replaced by its restricted target polynomial.

However the norm is on the algebra R[T]/F, not on T^p−Y. Moreover U has degree L−1=Theta(m²), with the geometric q-binomial coefficients. The acquired theorem does not license the replacement of its cyclic algebra by R[T]/F, nor treat this direction as length m. The sparse cyclic norm's arbitrary-shift composition theorem would apply if the actual target multiplication operator could be represented by its bounded-width rational monomial base in a paid cyclic coordinate. I found no such coordinate for the acquired native targets. Their known exponents are short public integers, but are not root-of-unity phases.

## Two repairs attempted, with their exact unacquired inputs

1. Reduce U modulo F first. This leaves degree <J and gives a direction of the right size. But obtaining U mod F is precisely obtaining S_L mod F (up to a paid modular power T^L), the long geometric factorial remainder. Its norm immediately gives the original product. Thus this repair is not an algorithm until the remainder is actually acquired.

2. Keep the cyclic algebra and perturb its defining polynomial instead. Writing F=T^J−Y+epsilon V with degree V<J does provide an O(m)-size direction. But norming this polynomial over the geometric seed algebra gives epsilon-degree L, not J: it is product_(i<L)(q^(Ji)−Y+epsilon V(q^i)). At epsilon=1 it is again the original source. Retaining only O(m) epsilon coefficients is not justified in this orientation. The tangent theorem pays the first coefficient; that does not determine the full value at epsilon=1.

These two orientations explain why the favorable J-sized precision cannot presently be combined with the paid J-sized spatial direction and cyclic carrier in the SAME source-retaining construction. This is a concrete failure of this deformation implementation, not a lower bound or a claim that another deformation cannot work.

## What the stronger fixed-shift composition does supply

The tangent constructor/transposition genuinely pays composition and power projection for a fixed cyclic base X^s f(X)/g(X), with f,g of bounded degree, even when s is a large native integer. Thus it is stronger than merely computing one norm scalar.

If a paid representation of the actual target algebra mapped T to such a base while preserving all original y_j, one could attempt S_L(T) in that representation. But its seed polynomial S_L still has L coefficients; using transposition does not make an implicitly given degree-L q-binomial polynomial a degree-m input. A further short q-binomial composition rule would be necessary. The earlier packet's acquired O(m)-coefficient prefix is not the full polynomial and cannot be inserted into this composition as though it were.

The exact finite q-binomial expansion is

 S_L(T)=sum_(r=0)^L (−1)^r q^(r(r−1)/2) [L choose r]_q T^(L−r).

All denominators 1−q^r through the covered L are units by the local-order promise; this makes formulas safe, but does not remove their L entries. Evaluating a short prefix at T=1 or reducing it modulo F is not an exact replacement for S_L. The native ell and true seed index are already retained in y_j and q^i throughout this attempt; no further H-to-native integration is hidden here.

## Locality and recovery

D(1) is an original product, so a nonunit value would enter the existing bounded-leaf controller with no new character or QRH assumption. Binary row and seed-interval restriction uses the same deformation. This would be a valid full-query route if its determinant/remainder acquisition were paid. No saturated norm in a substituted cyclotomic component is accepted as an original collision.

## Current result

The direct deformation exposes a useful O(J)-precision target, but I did not construct its norm on the actual target quotient with total soft-O(m) input acquisition. The exact missing object is the original long geometric factorial remainder or an equivalent source-retaining deformation on that quotient. The newly acquired fixed-direction cyclic arithmetic does not yet provide it. No new all-input factoring algorithm, native coverage experiment, or generic impossibility statement is claimed.
