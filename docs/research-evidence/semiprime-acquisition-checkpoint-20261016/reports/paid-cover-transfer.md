# What the QRH decoder changes in structured divisor covers

2026-10-16. No new acquisition cover was obtained. The positive result here is a fully charged transfer for a supplied, constructed group-order cover. It does not assume that an Umans--Wang conjectural cover has been constructed.

Primary source checked again: Umans--Wang, arXiv:2511.10851v1, Definitions 3.1, Conjectures 3.2--3.3, Lemma 4.2, Section 5 (especially Theorem 5.2 and Theorem 5.5), and Section 6. Primary URL: https://arxiv.org/html/2511.10851 .

## Two sufficient paid interfaces

Assume the parent's paid preparation supplies a unit gamma with odd local orders greater than B=16m^2, m=Theta(N^(1/6)), and accept the reviewed QRH long-annihilator decoder.

**Explicit product.** Given a constructed list of nonzero integers A_i whose total binary length is T, suppose one local order of gamma divides K=product A_i. Form the actual integer K using a product tree in soft O(T) bit work. Compute g=gcd(gamma^|K|-1,N). Coverage excludes g=1. A proper g factors N immediately; g=N gives a supplied global annihilator, which the QRH decoder handles in soft O(T+N^(1/12)). Thus T=soft O(m) is enough. The terms need not be prime, prefactored, pairwise coprime, or individually divisible by the whole local order. This interface is strictly a product-divisibility promise.

**Structured cross-difference cover.** Instead suppose a public, paid description produces the two lists gamma^s and gamma^t modulo N for finite S,T, at cost C, and can recover a selected pair's exact D-bit exponents at cost R. Require every cross-difference used to be nonzero (e.g. min S>max T), and require that at least one local order divides one cross-difference s-t. Put U=|S|+|T|.

Form F(X)=product_(t in T)(X-gamma^t) over Z/NZ, and evaluate it at every gamma^s by monic product/remainder trees. This costs soft O(U) ring operations. Scan the row gcds. Coverage guarantees some nonunit row. A proper gcd returns a factor. For a saturated row, descend the retained T product tree, evaluating sibling polynomials at gamma^s and taking gcds. Total degree along the descent is O(|T|), so localization also costs soft O(U), without inversions of point differences. Repeated residues and zero divisors are harmless because divisions are monic.

At a saturated leaf, N divides gamma^s-gamma^t. Since gamma is a unit, gamma^(s-t)=1 modulo N. Recover the exact nonzero K=s-t, at cost R; its bit length is at most D+O(1). Apply the QRH decoder. The total paid bound is

    soft O(C + U + R + D + N^(1/12)).

This removes prefactoring of the singleton for this **adapted group-order cover**. It is not the integer-difference leaf of UW Theorem 5.2. That original leaf yields N dividing s-t, which says nothing by itself about gamma^(s-t).

## When the exponent lists really cost only C

For a GAP given as a sum of c arithmetic progressions with D-bit starts and steps, let V be the product of the progression lengths (the actual parameter-box volume). Computing powers of the starts/steps costs soft O(cD), and enumerating powers for the parameter box costs soft O(V) ring operations by a mixed-radix traversal. A selected exponent is recovered from its parameter tuple in soft O(cD). Do not replace V by the cardinality of the sumset unless properness or another paid enumeration algorithm is supplied.

For two such descriptions the displayed transfer therefore fits soft O(m) if cD+V_S+V_T is soft O(m), the nonzero-difference condition is met, and the descriptions themselves have been deterministically constructed within that budget. No need exists to materialize U different D-bit integers; only their modular powers and parameter labels are enumerated, and one exponent difference is recovered at the end.

At n about sqrt(N), a supplied order cover with D=soft O(n^(1/3)), V_S+V_T=soft O(n^(1/3)), and polylogarithmic rank would meet the sixth-root budget. A full n-divisor cover would suffice because the smaller prime's local order is at most n. Only that one local order needs coverage.

## What was and was not supplied by existing constructions

UW's target point alpha=beta=1/3 is still a conjectured coverage construction. The paper explicitly says it does not know even the weaker improvement alpha<1-beta. Its prefactored requirement is additional; removing that requirement does not prove the underlying cover. The source's n^{o(1)} rank overhead also yields n^(1/3+o(1)), not automatically a soft O(n^(1/3)) bound. Finally, an infinitely-many-n existence statement does not on its own give a uniformly constructed cover at a suitable scale for every input N.

The proved ordinary interval cover is paid but has |S|+|T| about sqrt(n), so its adapted consumer has fourth-root rather than sixth-root cost. Partitioning an interval into large product blocks constructs explicit multiples, but the total explicit product length remains of order n. The smooth-multiple AP construction in UW Section 6 covers its stated restricted factorization class; the paper does not claim it covers every local order. No verified Wilson or subset-product construction supplied the missing every-input coverage with all arithmetic paid in soft O(m).

One further distinction matters when reusing Theorem 5.2: its general Property 1 only requires each integer d<=n to divide the PRODUCT of the A_i. For a composite local order, that does not imply d divides an individual A_i and therefore does not justify a local zero among gamma^(A_i)-1. The explicit-product interface above accepts this weaker promise only when its actual total length is paid. The structured Strong divisor promise is an individual-difference promise, so it does support the cross-difference algorithm.

## Outcome

There is a useful positive removal of singleton prefactoring for **a supplied and paid group-order cover**, with the full cost displayed above. No actual existing target-scale cover was found whose only remaining missing part had been prefactored singleton recovery. The outstanding arithmetic task is still constructing a cover of a hidden prepared local order within the stated C+U+R+D budget; a conjectured cover is not counted as free input.
