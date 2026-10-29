# Group-valued polynomial evaluation and the aggregated projection cost

26 October2026. Scratch research/audit. The smaller-component unchanged-order theorem is valid and appended to `native-inversion.md`. This pass audits the proposed polynomial projection using actual integer heights, generic batch exponentiation, and unknown-order polynomial-commitment techniques. No soft-k complete aggregate is obtained; no helper-vector result is counted as a query advance.

## 1. Sharpened native order fact

After familiar k-roughening, every prime divisor of the smaller-component order r_P exceeds k, while r_P<P<=sqrtN<=k³. If powering by any integer removes a nontrivial order factor, the new order is at most r_P/(k+1)<k²<16H. For an acquired schedule of short supplied labels, the paid first-drop separator therefore returns a factor. A huge aggregate exponent alone is not a licensed short-annihilator input: localization to one short factor must also be paid, as in Section 5. Continuing short-label cleaning cannot leave a prime order above threshold after an actual smaller-side reduction. On the continuing branch all arbitrary-label cleaning is AUTOMORPHIC at the smaller component, whether its unchanged order is prime or has two large prime factors. This sharpens the earlier conditional prime-order remark; it does not identify the order or prove larger-component invariance.

## 2. Initialized polynomial and its actual heights

Set d=ceil sqrtk (called b in the proposal), and

    P_d(X)=product_(n=1)^d(X−Hn), H=k².

Its d+1 integer coefficients have bitlength O(d log(Hd)), hence total soft O(d²)=soft k bits. A product tree acquires them at that scale. Binary exponentiation acquires all beta raised to these coefficients in soft k ring/bit cost. Negative coefficients use beta^-1, already a unit. This initialization is correct.

For a native nonaxis label E=a+bN+lambda, b!=0 and |a|<=k,0<=lambda<H. Thus |E|>=N−H−k. On the prepared N>256k^4,k>16 branch, all 1<=n<=d obey

    N/4 < |E−Hn| < 3kN.

In particular each P_d(E) is nonzero and has Theta(d logN) bits. This is an actual native height calculation, not merely a generic dense-polynomial bound. The original public integer-zero deletion also excludes zeros for every tested n within the physical window. Axis/special rows may have smaller values and can be handled separately; they do not erase the nonaxis contribution.

For J_nonaxis such rows the literal aggregate

    A=product_j P_d(E_j)

has Theta(J_nonaxis d logN) bits, with no additive cancellation in this product. An integer resultant Res(product_j(X−E_j),P_d(X)) is this same integer up to a conventional sign, not a smaller exponent. Constructing it and then powering beta costs soft O(Jd) bits/group steps at the native J=soft k scale, about k^1.5 rather than k. Fast integer multipoint/resultant arithmetic can avoid quadratic arithmetic overhead, but cannot avoid writing this explicit long integer if that is the chosen output interface.

## 3. Homomorphic multipoint interface: what it supplies and costs

The desired vector is beta^(P_d(E_j)). With coefficient images g_r=beta^c_r, evaluation is the group-module expression product_r g_r^(E_j^r). It is linear in coefficient images; a group multiplication adds their exponents, and scalar multiplication raises to an explicitly acquired integer. There is no operation multiplying two hidden exponents.

An ordinary polynomial subproduct/remainder algorithm over Z can be transposed into such a module computation only after charging its INTEGER scalar coefficients and group scalar powers. For a degree-d block, point-product coefficients have O(d logN) bits. Splitting the J points into degree-d blocks gives about J/d blocks and soft O(d²) integer coefficient bit volume per block: soft O(Jd) overall. Merely counting O(J) coefficient-ring operations treats these long scalar powers as unit-cost. A degree-J global point tree can have still larger coefficient volume; it is not a better initialized construction automatically.

There may be more sophisticated module-convolution methods, but no primary result inspected here gives this particular unknown-order output vector in soft J with its long integer scalar work included. The already acquired common-base provenance allows ordinary shared exponentiation techniques; it does not turn integer polynomial multiplication into multiplication of hidden group exponents.

Most importantly, even a cheap vector is insufficient for the proposed partial-order screen. Multiplying its group outputs gives beta^(sum_j P_d(E_j)), not beta^A. It does not aggregate the primary divisibility of all P_d(E_j). Testing each projected base separately would require J small-order separator calls, outside the target. The useful aggregate is beta^A, and that exponent multiplication must be paid or replaced by a proved native relation.

## 4. Primary batch-exponentiation and unknown-order-source check

Pippenger, *On the Evaluation of Powers and Monomials*, SIAM J.Comput.9(1980),230–250, https://doi.org/10.1137/0209022, studies simultaneous monomial evaluation through multiplication/addition chains. Bernstein's author exposition, https://cr.yp.to/papers/pippenger-20020118-retypeset20220327.pdf, explicitly distinguishes one power, a sequence of powers, products of powers, and sequences of products. These techniques improve generic batch powering by logarithmic factors; they do not convert a product of known exponent values into a product of their group images. Applying them to J exponents of O(d logN) bits retains that exponent-length parameter.

Bunz–Fisch–Szepieniec, *Transparent SNARKs from DARK Compilers*, primary author paper https://eprint.iacr.org/2019/1229, also available https://core.ac.uk/download/pdf/579864042.pdf, technical overview and integer-encoding/commitment construction, uses unknown-order groups to commit to long integer encodings of polynomials. Its succinct evaluation proof is a verification interface; the honest prover still acquires the integer polynomial/exponent data and computes the claimed values. Bounded homomorphism retains the integer coefficient-height requirements. No succinct verifier is an algorithm producing beta^A or all these evaluations from coefficient images at verifier cost. No cryptographic security assumption or trusted group setup is imported here.

For the literal generic straight-line exponentiation implementation, an unreduced exponent of bitlength Theta(Jd logN) also needs that height to be reached by group multiplication; each multiplication can at most double the maximum absolute formal exponent already available. Previously acquired coefficient/shared-root powers have only their charged heights. This observation is scoped to the exact formal-exponent implementation: native order relations, early gcd factors, non-generic arithmetic algorithms, or a different collision predicate can evade it. It is not a group-operation lower bound for the original factoring problem.

## 5. Correct possible screen and what is still missing

If beta^A were acquired cheaply, a low-order separator could detect any smaller-side partial order loss. A first-drop localization among the actual short factors E_j−Hn would then give a previous high-order base and a nonzero O(logN)-bit annihilator, rather than passing A or P_d(E_j) to the short-annihilator extractor. The factor list has Jd entries; its acquisition/localization cannot simply be assumed soft k. Additionally, a complete solution needs a theorem that some tested short factor catches a relevant order prime. The native cover guarantees E_j=HI modulo the witnessed order at an unknown |I|<M, not n<=d. This pass supplies neither that short partial-order coverage nor its cheap aggregate.

The focused route therefore leaves a precise arithmetic task: compute a coverage-safe projection equivalent to the primary incidence of all E_j−Hn, with soft-k acquisition and short-gap recovery, without materializing their Jd-bit product exponent. Existing integer MPE, batch exponentiation and unknown-order commitment identities do not initialize it. The sharpened smaller-order automorphism theorem is retained as an independent structural result; no new preparation helper, vector evaluation, or formal resultant is claimed as full-goal progress. No numerical campaign or repository edits.
