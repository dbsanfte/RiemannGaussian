# Execute signed-weight palette acquisition with all bins paid

24 October 2026. Scratch research. This tests a broader constructor than positive native lifts: signed weights aP+cQ, with a public rank-two lattice and real variation control. It actually acquires a uniformly covering CONSTANT-size index palette, but only after acquiring soft N^(1/3)=soft k² rows. The better parameter choice recovers the known soft N^(1/5) weighted construction. Neither is a new whole-query advance; the precise cost of forcing the palette is exposed. No generic no-go statement follows.

## Input and prior boundary

Use the paid scalar beta: N=PQ<=k^6, even public k=Theta(N^(1/6)), 16H<P<Q, H=k², beta a unit with odd k-rough local orders>16H. Put q=beta^H, whose local orders are the same. The general nonzero global-annihilator extractor is the already reviewed source a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be. It costs soft k on this promised input, without assuming balanced factors or a factorization of the supplied annihilator.

Index-residue.md already acquires a conditional constant-palette consumer for the original repaired family; it does NOT acquire a uniform covering palette. Native-lift-sharing.md already gives the exact positive-lift formula and its enlarged horizon. The old journal's weighted Lehman/quotient-lattice constructions, rational-centre carries, and the known fifth-bound weighted cover are prior credit. The cubic-cover N^(2/9) alternative has a different determinant and is also already complete. This report does not reclassify any of those as new. It asks specifically whether SIGNED two-weight variation can force a cheap uniform palette, and executes that attempt including its row count.

## 1. Acquire a legal signed two-weight family

For every public unit tag 1<=j<k take the rank-two lattice

 Lambda_j={(a,c) in Z²: a j²-cN=0 modulo k}.

If v=[N j^-2]_k, the two columns (k,0),(v,1) are an actual basis of determinant k. For ANY nonzero pair in this lattice, including a=0 or c=0, acquire

 ell0=-a j-cN j^-1 modulo H.

Public inversion is modulo H. The quadratic f(X)=aX²+ell0 X+cN has f(j)=0 modulo H and f'(j)=0 modulo k. Its exact expansion at j therefore shows H divides f(j+kx) for every integer x. At the own tag j=P modulo k, P is a unit modulo H, giving

 H I0=aP+cQ+ell0.                               (1)

No coprimality of a or c with k is assumed. In particular the old at-most16 inverse-square fibers for the native UNIT leading coefficient cannot automatically be applied to these weights. A public gcd(c,k)>1 is not a factor of N and is not silently discarded.

The scalar target uses

 E=a+cN+ell, V=beta^E, q=beta^H.

Whenever Hi=aP+cQ+ell, direct subtraction gives

 E-Hi=(P-1)(cQ-a).                              (2)

Thus signed weights preserve genuine own-prime coverage without a colour assumption. Negative powers use the known beta inverse. The construction is not a Gaussian phase substitution or an acquired residue of the prime modulo H.

## 2. Finite-dimensional guaranteed small variation

Take a public interval |P-P0|<=Delta<=P0/2, P0>=S in a dyadic bin S<=P<2S. Let F(X)=aX+cN/X. Apply the exact rational map

 w1=Delta(a-cN/P0²),
 w2=Delta² cN/P0³.

Its determinant is N Delta³/P0³, and the image of Lambda_j has determinant kN Delta³/P0³. Clear the common rational denominator, run fixed-dimensional LLL, and rescale. A nonzero pair is acquired in polylogarithmic bit time per tag/centre, with

 max(|w1|,|w2|)<=2*sqrt(kN)*(Delta/P0)^(3/2).      (3)

The harmless factor2 exceeds the standard dimension-two LLL bound. The map is invertible, so the pair is nonzero. Exact integer square-root bounds give a PUBLIC common T>=the right side for every centre P0>=S; no numerical approximation oracle is used.

The variation identity is exact:

 F(P0+t)-F(P0)
  =(a-cN/P0²)t+cN t²/[P0²(P0+t)].               (4)

Its two terms are bounded by T and 2T, hence variation is <=3T. Heights are controlled by |c|<=T P0³/(N Delta²) and |a|<=T/Delta+T P0/Delta². At polynomially bounded parameters Delta>=1, all coefficients and exponents have O(log N) bits. This bound works for signed a,c and uses no favorable-vector independence or nonzero a promise.

## 3. Exact centering and complete recovery

Acquire nu=floor((ell0+F(P0))/H+1/2) by exact rational floor, including negative values. With

 U=ceil(1/2+3T/H), ell=ell0-Hnu+HU, h=2U+1,

(1) gives an actual own index i in [0,h). The entire signed width, not only U, is charged and guarded. Every row has an acquired integer E=a+cN+ell and retained (tag,bin,centre) labels.

Before removal of any row, test the integer roots of the NONZERO linear polynomial aX-cN for proper divisors of N. If a=0,c!=0 it is a nonzero constant; otherwise use exact rational-root divisibility. If the own exponent in (2) were zero, then aP=cN and the pretest would factor N. Next remove any row having a public integer-zero position E=Hz with 0<=z<h. Provided h<ord_P(q), an own collision and that position force i=z; the pretest already handled it. Thus this ordering retains coverage and ensures every remaining scalar leaf supplies a nonzero integer K=E-Hi.

Acquire P_h(Y)=product_(0<=i<h)(1-q^iY) and all retained V^-1 by actual product trees and signed binary powering. Monic MPE acquires every row value in soft(h+J) work. A proper gcd factors. Descend a saturated row through at most h actual leaf checks: a proper leaf gcd factors, while a saturated leaf supplies beta^K=1 modulo N with explicit nonzero O(log N)-bit K. The pinned general extractor then costs soft k. No near-N factor-sum bound is assumed for these signed weights.

This is a complete algorithm at every parameter choice below with h<16H. Publicly check the guard and use trial division on its finite exceptional range. Actual roughness preserves q orders; no new seed-order theorem or auxiliary pivot decoder is needed.

## 4. Count every choice when forcing a palette

Use O(log N) public factor bins, covering the smaller P. For each bin choose radius Delta=eta*S within constant factors and cover it by O(1+1/eta) actual integer centres >=S. Acquire every unit tag at every centre. For 0<eta<=1/4 the complete ledger is

 J=O(k/eta),
 h=O(1+sqrt(kN)*eta^(3/2)/k²).                  (5)

The public common T, centering U and h are uniform within each bin. The exact scalar query, zero pretests and one recovery call cost soft(J+h+k). No row or bin is advice about the unknown factor.

To FORCE a constant-size palette, choose eta within a fixed constant factor of

 eta_const=k/N^(1/3).

Then sqrt(kN)*eta_const^(3/2)/k²=1, so the actual own index belongs to the PUBLIC constant palette {0,...,h-1}; choose conservative fixed constants from (3) to make h one fixed integer for all bins. Yet

 J=O(N^(1/3))=O(k²).

All those rows must actually be acquired in this explicit construction, and their product/MPE clock is constant. The result is a complete conditional-controller factor algorithm with a constant index palette and soft k² cost, not a soft-k palette constructor for an O(k)-row family. A polylogarithmic h similarly leaves soft k² rows. Merely counting its constant terminal nodes would omit the dominant acquired input.

For comparison balancing J and h in (5) chooses

 eta_bal=k/N^(1/5), J,h=O(N^(1/5)).

This executes the known fifth-bound weighted tradeoff, including all rows and recovery, and is credited as such. The cap eta<=1/4 and Delta>=1 affect only a finite input range at fixed sixth-root scale. Both choices have h<16H for sufficiently large N, uniformly across bins. The finite fallback does not assume an effective analytic threshold.

If the original O(k) row budget is retained in this exact interval constructor, eta is bounded below by a constant. Its guaranteed h then has scale sqrt(N)/k^(3/2), which at k=N^(1/6) is N^(1/4), rather than a constant palette. This is the bound delivered by this specified LLL/Taylor certificate, not a lower bound on possible actual vectors or other constructors.

## 5. Additional congruence and Möbius checks

One might demand that the quadratic f vanish modulo k³ on EVERY integer P=j+kx, to make the own index automatically divisible by k. Its second finite difference is 2a k², so the universal identity forces k|2a. Since k is even, this only forces (k/2)|a: the integer-valued x(x-1)/2 parity exception must not be omitted. The first finite difference then gives k|ell, and f(j)=0 modulo k/2 forces (k/2)|c since N is a unit. Dividing the common factor k/2 reduces the purported k³ denominator to 2k², a constant-factor change rather than an acquired extra k-digit. No stronger k|a assertion is used. This rejects only that universal identity; it does not exclude a different cover that accepts selected actual roots, as the cubic construction does.

A public Möbius relabeling of P modulo H would similarly need an acquired small image catalog and valid unit denominators. Relabeling all unit residues permutes a size-Theta(H) set; it does not acquire a small subset containing the factor. No such subset or new valuation class is supplied by the signed-weight certificate. The source never asserts that all possible prime lifts occur, nor uses this count as a factoring lower bound.

The tested linear-weight freedom therefore supplies a real uniformly covering palette only by paying the larger family in (5). A new arithmetic selection capable of keeping both rows and palette soft k remains the missing step. The public index-palette consumer and precise smaller-nonsplit uniqueness theorem remain available ingredients, but neither provides that selection. No new all-input acquisition rate, sixth proof, sample campaign, shared-file edit or generic obstruction is claimed.
