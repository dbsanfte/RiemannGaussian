# Paid square-alias certification and a uniform univariate recurrence barrier

2026-10-16. A classical composition with the newly paid setup. The product/multipoint acquisition method is classical. This is a barrier for a specified chirped recurrence format, not acquisition of the original long query or a general operation lower bound.

## 1. Input interface and output

Let N=P Q with distinct odd balanced primes, and let m>=3 be the intended sixth-root-scale integer. Use the separately proved paid coprime refinement: it either factors N or supplies a unit beta whose exact local orders are odd, coprime, and exceed B=16m²; its global order exceeds B²=256m⁴. With q=beta^(m²), the same refinement either factors or certifies both local q-orders>B. The orders need not be prime or known. These are proof-side guarantees, not factor/order inputs.

From that surviving setup, one further soft-O(m) bit procedure either returns a proper factor or certifies that

 beta^(m²s)-beta^t is a unit modulo N
 for every 1<=s<=m and -m<=t<=m, t!=0.                              (1)

Together with the setup, the total cost remains soft-O(m), including seed acquisition, powers, polynomial arithmetic and gcds. This statement uses the explicit balance/scale assumptions of the paid setup; it does not silently invoke them for arbitrary semiprimes.

Set d=m² and L=2d+2. In either hidden field define

 product_(i=0)^(L-1)(1-q^i x)=sum_(k=0)^L c_k x^k,
 A_k=c_k beta^(-binom(k,2)).

On the no-factor certified branch there is NO recurrence

 sum_(t=0)^r P_t(q^k) A_(k+t)=0 for every 0<=k<=L-r,                  (2)

where r>=1, the coefficient polynomials are not all zero, max deg(P_t)<=D for D>=0, and

 r+D<=m.                                                          (3)

Field coefficients may be fully advised and depend on the full input. No source-family deletion, prime-order hypothesis, or fixed low-digit plan is needed.

## 2. Acquire the whole square-alias certificate

Compute all beta^t for -m<=t<=m, t!=0, by successive powers of beta and its known unit inverse. Build the balanced product tree for the monic degree-2m polynomial

 H(X)=product_(-m<=t<=m,t!=0)(X-beta^t).

Generate q^s, 1<=s<=m, by successive multiplication and evaluate H at these m points by ordinary monic subproduct/remainder trees. No point differences are inverted; repeated global or local nodes would not invalidate evaluation. Compute gcd(H(q^s),N) for every row s until a factor is found.

A proper gcd is a factor. A gcd1 row certifies every leaf difference in that row is a unit, since a product is a unit if and only if all its factors are units. If a row gcd is N, descend its retained product tree. Evaluate a child at the fixed row point: a proper gcd returns a factor; a gcdN child can be descended into; a unit child is discarded and the other child has gcdN. At each step at least one of these alternatives applies, because the parent value has gcdN.

If descent were to reach a gcdN leaf, its difference would vanish modulo N. Since beta is a unit, this would give a NONZERO integer annihilator

 K=d s-t, 0<|K|<=m³+m.

Nonzeroness follows from d s>=m²>m>=|t|. But beta's global order is greater than256m⁴, and must divide K. This is impossible. Therefore a saturated row necessarily produces a proper factor before such a leaf. In every execution that does not factor, all row gcds are1 and (1) is proved simultaneously.

Power generation and polynomial setup use soft-O(m) ring work. Ordinary monic multipoint evaluation has the same bound. There are at most m row gcds and at most one localization path, whose sibling degrees sum to O(m). Fast residue/polynomial arithmetic gives soft-O(m log N) bits, which is soft-O(m) at the stated scale. No explicit m-by-2m array or list of all individual inverses is constructed. The certificate is a simultaneous theorem-level consequence of the computed row products, not an output of m² separate residues.

## 3. Consequence for all specified positive-order recurrences

Fix either hidden field. The certified q-order exceeds B>L, so all c_k,A_k are nonzero and all q-binomial denominator factors needed below are nonzero. For X=q^k the exact ratio is

 A_(k+t)/A_k=beta^(-tk-binom(t,2))(-1)^t
             * product_(a=0)^(t-1)(q^a X-q^L)
             / product_(a=1)^t(1-q^a X).

Divide (2) by A_k and clear the common denominator product_(a=1)^r(1-q^a X). It is nonzero on each required k since k+r<=L. This gives

 sum_(t=0)^r beta^(-tk) B_t(q^k)=0,

where

 B_t(X)=(-1)^t beta^(-binom(t,2)) P_t(X)
         * product_(a=0)^(t-1)(q^a X-q^L)
         * product_(a=t+1)^r(1-q^a X).

Every B_t has degree at most D+r<=m, and is zero exactly when P_t is zero, since its multiplier is a nonzero field polynomial. Expanding yields a linear combination of the bases

 beta^(du-t), 0<=t<=r, 0<=u<=D+r,

raised to the consecutive powers k.

All these bases are distinct in the chosen field. A collision would give beta^(ds-v)=1 for s=u-u', v=t-t'. If s=0 and v!=0, |v|<=m is smaller than the local beta-order. If v=0 and s!=0, |s|<=m is smaller than the local q-order. If both are nonzero, change signs to make s positive; then 1<=s<=m and 0<|v|<=m, so the unit certificate (1) forbids the collision. No assumption gcd(m,local-order)=1 is used.

There are n=(r+1)(D+r+1)<=(m+1)² bases. The number of consecutive equations is

 L-r+1>=2m²+3-m>=(m+1)² for m>=3.

Take the first n equations. Their coefficient matrix is a square Vandermonde on distinct field elements, so it is invertible. All coefficients of every B_t vanish, hence every P_t vanishes, a contradiction. This proves the barrier in BOTH hidden fields. Zero individual coefficient polynomials and arbitrary advice do not create an exception. Positive order is explicit; no unconstrained order-zero polynomial relation is being excluded.

## 4. Credit and exact limitations

The universal detector, monic product/multipoint trees and gcd localization are classical mechanisms already used in the paid setup. The new composition acquires this particular square alias catalog cheaply and converts it into the stated recurrence-format guarantee. It does not claim a new generic multipoint algorithm. Unlike the earlier majority/prime-order catalog arguments, this applies to the new certified arbitrary-odd-order beta and requires no additional source deletion.

The original query's literal projected base2 and its collision/source qualifications are NOT automatically replaced by beta. The theorem does not acquire the original J-by-L query, construct a factor on every no-factor branch, or transfer interval coverage. It does not rule out recurrences outside r+D<=m, another geometric base, multivariate coefficients, another transform, fast selected convolution, or scalar norm methods. Even a recurrence of order slightly larger than m is outside the stated barrier. No general q-holonomic operation lower bound, black-box lower bound, new native declaration or Lean bit theorem follows.
