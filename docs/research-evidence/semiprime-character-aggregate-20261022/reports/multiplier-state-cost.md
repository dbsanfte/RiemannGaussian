# Doubling the Legendre mask: carry states and their acquisition cost

22 October 2026. Independent constructive cost attempt. No soft-m simultaneous evaluator was obtained. This note tracks actual products and query counts, not a generic automata obstruction. No tests, examples, backend or repository edits.

Let S_eta={0} union nonzero residues of Legendre sign eta, Q=q^m, and H_eta,K(X)=product_(r in S_eta,n<K)(X-q^(r+mn)). Work on the actual prepared odd-order scalar subgroup, with J~m native points and K~m. The original q is not specialized to an mth root of unity.

## Exact first doubling and source preservation

Set r'=2r modm and c(r)=floor(2r/m). Then

    2(r+mn)=r'+m(2n+c(r)).

Multiplication by two sends S_eta bijectively onto S_(eta*Legendre(2,m)), with zero retained. However the new quotient index is parity-constrained separately for each residue: it is c(r) modulo two. Thus the powered-root polynomial is

    H_eta,K^[2](Z)=product_(r in S_eta,n<K)
                      (Z-q^(r'+m(2n+c(r)))).

Every original scalar collision is preserved, and conversely a collision after squaring implies the original one at either hidden prime because the local order is odd. This exact useful source property does not itself compute the product.

The ordinary factorization

    H_eta,K(X) H_eta,K(-X)=(-1)^(K|S_eta|) H_eta,K^[2](X²)

has the stated sign. At actual subgroup X, every factor in H_eta,K(-X) is a unit, since a ratio of subgroup elements cannot be -1. But acquiring this WHOLE J-target unit companion still asks for a long geometric product of degree-|S_eta| blocks. Its being a unit does not supply its residue. The previously paid Cayley companion was a SINGLE scalar seed norm shared by all targets, not this target-dependent collection. This route therefore cannot divide by an unacquired companion and declare an evaluator.

## Iterated carries can be described cheaply

After h doublings,

    r_h=2^h r modm,
    c_h(r)=floor(2^h r/m),
    2^h(r+mn)=r_h+m(2^h n+c_h(r)).

The carry satisfies c_(h+1)=2c_h+floor(2r_h/m). Its word is computable from the public r in O(h) small operations. There are at most min(2^h,m) nonempty carry classes, and their residue lists partition the original O(m) roots. All residue/carry metadata through h=O(log K) therefore costs soft O(m). This confirms that a finite-depth descriptive state construction is affordable; no uniform finite-kernel hypothesis is required.

For one level, each carry class can also have its degree-e_c polynomial acquired by a monic root product tree, with sum_c e_c=|S_eta|=O(m). Generating q^(r_h+m c_h) and these polynomials is soft O(m) per level. These are ACTUAL acquired block polynomials, stronger than a descriptor count.

## The product evaluation charge that remains

Inside class c, the remaining seed index is still n=0,...,K-1 with stride q^(m*2^h). Thus the associated product is a length-K product of degree-e_c blocks at the transformed target X^(2^h), not an acquired scalar value. Splitting residues by carry does not shorten this n interval.

If instead a proposed recursion splits a FULL quotient-index interval into even/odd children to shorten K, the selected child parity depends on r's carry. Distinct carry classes must retain their own products; both required children cannot simply be discarded. For a class polynomial A_c of degree e_c and a horizon K_c, the ordinary shared block method has explicit cost

    soft O(e_c B_c + J_c K_c/B_c + J_c),

where J_c is the number of requested target points for that class, not its number of root descriptors. Since the final H value is a product over all nonempty residue classes, every original target generally requests EVERY such class. Without a new product-aggregation identity J_c=J; summing only e_c and omitting those target requests undercounts the computation. At terminal depth with K_c=O(1), acquiring J values for C separate class polynomials through ordinary multipoint calls pays soft O(m+JC), potentially m². A special batched AGGREGATE can conceivably avoid this count, but is precisely an additional algorithm, not a consequence of the carry recursion.

Power-of-two K removes irregular endpoint lengths and helps organize a balanced product circuit. It does not remove residue-dependent parity or establish that the product of its many class evaluations has a soft-m acquisition algorithm. Sequential scalar powering of the J native points through O(log K) depths is itself soft m and not the cost issue. The missing data are the class-dependent long products, not their arguments or binary state descriptors.

## Native cubic colour and exact completion target

Native normalized exponents satisfy v_j²=4a_jN modm³. Doubling preserves the small auxiliary congruence with a known factor four; it does not force the high-order scalar q^(m*2^h) to have short period or put all powered targets into a common short orbit. Carry words of the PUBLIC mask roots depend on r, whereas the target's carried phase depends on the actual v_j. No identity relating those two ledgers so as to cancel all interior class products was found.

A successful completion would supply one exact transform acquiring, for all J native targets, the PRODUCT over the carry-class evaluation outputs in soft O(m), with its normalization/unit companion and restrictions paid. It could also give a collision-preserving terminal observable avoiding that entire collection. The sparse per-level root polynomials, their power-of-two arguments, and the whole state descriptors are already affordable; the required shared product aggregate is not yet acquired.

Outcome: this attempt validates an affordable finite-depth carry representation and block-polynomial construction. It supplies no new simultaneous H evaluator, sufficient factor query, lower bound or rate gain. Any proposed recursion should be checked against the displayed J_c and K_c charges before treating O(m) states as O(m) computation.
