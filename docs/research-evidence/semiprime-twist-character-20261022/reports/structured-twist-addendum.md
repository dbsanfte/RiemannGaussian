# Structured sign/twist computation addendum

22 October 2026. Continued with the user's priority on q-shift identities, reciprocal pairs and unsquared Jacobi values. No universal acquisition saving was obtained. The following are explicit computational identities and their charges, not new obstruction claims or selected semiprime families.

## A real q-shift update, and the exact geometry it needs

Put R_L(z)=product_(0<=i<L)(z−u q^i), and let chi be the Jacobi symbol modulo the odd semiprime N. Prepared q is a power of gamma and has local Legendre value +1 at both primes. The division-free polynomial identity is

    (z−u q^(L−1)) R_L(qz)
       = q^L (z−u/q) R_L(z).

Thus, after testing the two public boundary differences by gcd, either a useful nonunit leaf is already found, or both are units and

    chi(R_L(qz))
       =chi(z−u/q) chi(z−u q^(L−1)) chi(R_L(z)).

The initial scalar row can be tested/factored by the ordinary single-target baby/giant product method in soft O(sqrt L). If its aggregate is a unit, that certifies zero nonunit count on that row. The exact count also obeys the cheap update

    D_L(qz)=D_L(z)
             +1_(gcd(z−u/q,N)>1)
             −1_(gcd(z−u q^(L−1),N)>1).

This is an actual acquisition reduction when the acquired targets form a known q-chain of total integer shift span K: the whole chain can be processed in soft O(sqrt L+K+number of targets), factoring on a boundary hit. Saturated leaves retain their recorded nonzero-exponent recovery. No nonunit boundary is inverted.

For the **native** long query, q=gamma^(m^2), while targets are gamma^(N+delta_j). Their public integer offsets are not supplied as a q-chain of soft O(m) span. Multiplying every exponent by 2^k preserves this alignment issue. Replacing the seed step by gamma gives a much longer seed interval, roughly m^2 L, whose single-target square-root acquisition already costs m^2. No paid transform of the actual native targets into the short-chain geometry was constructed. Therefore the update above is not claimed as an all-input improvement or as acquired native data.

## Reflection: exactly which unsquared correlation survives

For h(e)=gamma^e−1 and epsilon=chi(−1), multiplicativity and the odd-local-order property give, including zeros,

    chi(h(−e))=epsilon chi(h(e)).

Consequently the reflection product is

    chi(h(e))chi(h(−e))=epsilon chi(h(e))^2.

It retains exactly the principal/nonunit mask, with known orientation epsilon. The signed reflection sum either doubles the original character or cancels identically, according to epsilon; its cancellation is not a factor certificate. The product h(e)h(−e)=−gamma^(−e)(gamma^e−1)^2 has the same nonunit source. Reciprocal Laurent/Dickson folding may exploit an actually symmetric source ledger, but merely introducing the reflected copy gives at most a constant-size folding and does not acquire the remaining masked product/count. No repeated factor-of-two speedup is inferred.

## Power-of-two twists and q-product norm identities

For t in the prepared odd-order subgroup,

    1−t^(2^k)=(1−t) product_(0<=h<k)(1+t^(2^h)),

and every displayed plus factor is a unit in both hidden fields. Thus each original leaf gcd and each restricted product's nonunit status is preserved by t->t^(2^k). Public repeated squaring constructs the transformed bases/targets in soft O((J+1)(k+1)).

At the product level the exact identity is

    F_L(t;q) F_L(−t;q)=F_L(t^2;q^2),
    F_L(t;q)=product_(0<=i<L)(1−t q^i).

The minus-t product is a unit at every original leaf, but its Jacobi symbol need not be +1. Since its symbol is ±1, the unsquared sign recurrence (valid also when the original product is nonunit) is

    chi(F_L(t;q))
       =chi(F_L(t^2;q^2)) chi(F_L(−t;q)).

This recurrence still requires an acquired long product/sign on its right side; both have length L. Unlike a true q-chain boundary update, it does not shorten the acquisition index. A numerical ratio at a nonunit original product is not used. The familiar telescoping product of plus factors along **doubling exponents** is cheap but consists entirely of units and cannot replace the original arithmetic-progression exponent ledger.

## Paid outcome

The q-shift boundary algorithm above is the strongest actual computational sharing found in this continuation. Its short-chain hypothesis has not been acquired for the original targets. Reflection and power-of-two twists keep the source exactly, but no accompanying length/degree reduction makes the native long query cheaper than the retained soft O(J+sqrt(JL)) method. The unsquared signs have not supplied a different guaranteed factor-producing observable at soft O(J+sqrt L).

No native files, backend lemmas or success-example campaign were added.
