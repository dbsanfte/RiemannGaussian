# Independent implementation review: packed Gauss acquisition and support extractor

22 October 2026. Reviewed `implementation/packed_gauss.py` and `implementation/test_packed_gauss.py`, together with the packed quotient proof and support-controller report. Verdict: no correctness repair requested. The implementation acquires C_E and the implemented all-divisor support controller as specified. It does not implement the separately proposed fast polynomial-gcd controller or establish universal auxiliary selection.

## Actual quotient and exceptional components

The public log table is generated from a certified public auxiliary prime ell and a primitive root found using the known factorization of ell-1. It contains logs modulo k, exactly what every histogram needs. The histogram loop t=2,...,ell-1 enumerates all t≠0,1, including the correct value of 1-t modulo ell; neither log lookup is undefined.

`projector(a)` is the required subgroup average E_a. Its h distinct exponent positions receive h^(-1), with h=k/gcd(a,k); a=0 gives the constant one. The input gcd guard makes each inverse legitimate. `product_constant` implements precisely

    J_ab+(ell-1)[(E_(a+b)-E_aE_b)J_ab-E_aE_b].

This corrects BOTH-trivial J=ell-2 to -1, leaves exactly-one-trivial J=-1 unchanged, multiplies the nontrivial cancellation case by ell, and retains ordinary J in every other component. The binary scan starts at C_1=1 and grade 1 modk, updates doubling BEFORE using the new grade for the optional add-one step, and handles E=0 separately as C_0=-1. Therefore its output is the actual full k-coefficient C_E, not an assumed Gauss quotient.

The edge ell=2 forces k=1. Primitive-root search returns g=1, the log table has its single required entry, the histogram is empty, the correction is -1, and the recurrence correctly computes the trivial-character quotient. General k=1 also works. The normalization sum(C_E)=(-1)^(E+1) is consistent with extraction only for odd E, including its default E=N.

## Kronecker convolution

After reducing every input coefficient to [0,N-1], each ordinary convolution digit is at most k(N-1)^2. The byte width is ceil(bit_length(bound)/8), so base 256^width is STRICTLY larger than that bound, even at exact byte boundaries. There are no carries between digits. The product occupies at most 2k-1 digits, so the fixed `to_bytes` length is sufficient. Extraction reads every ordinary digit once and folds position i into i modk; no wrapped contribution is omitted. k=1 and all-zero products have valid lengths. This reasoning is identical for mpz and Python-int packing.

The packed implementation uses full byte conversion and a single big-integer multiplication, rather than quadratic convolution followed by a claimed fast bound. The documented caveat remains appropriate: the paper bit bound uses fast integer multiplication; these controls certify exact arithmetic, not the runtime exponent of a particular Python/GMP release. The quadratic backend is a transparent oracle/fallback, not a soft-linear performance claim.

## All-divisor folds and the exact support guarantee

Divisors are processed in decreasing order. For each proper d, the selected prime p divides k/d, so dp is a divisor of k larger than d and its vector is already available. Folding V[dp] modulo X^d-1 therefore gives the exact V[d]. k=1 takes the direct normalized monomial branch.

For each d, prefix/suffix gcds initialized at N compute precisely gcd(N,{c_s:s!=r}) at every position r, including zeros. If the local P vector is X^r, P divides all excluded coefficients. Unless the Q vector is the SAME X^r, at least one excluded coefficient is nonzero modulo Q, so the result is exactly P. If both local vectors are that monomial, CRT and normalization make the public vector exactly X^r, caught by `GLOBAL_MONOMIAL`. If neither local vector is monomial, each excluded-position set retains a nonzero coefficient at both primes, so every such gcd is one. Thus the reported `BOTH_LOCALLY_NONMONOMIAL` status is justified under the documented odd squarefree semiprime assumption. A returned proper gcd is a factor regardless; no hidden P,Q are passed to production.

For all-divisor cost, group the folds by the prime p removed from their parent. For fixed p the parent map d→dp is injective, hence the sum of parent lengths is at most sigma(k). Summing over p gives at most omega(k)*sigma(k) additions. Since sigma(k)≤k H_k, this is soft O(k), including stored vectors and divisor/position gcd work. Parent selection and divisor enumeration use only public k. The current file already precomputes `prime_factors(k)` for parent selection; `divisors(k)` factors k once more. Both trial factorizations cost O(sqrt k), within the bound. Even a per-divisor trial factorization would have the bound mentioned by the parent, but it is unnecessary to justify the present code.

The test's numerical `3*sum(divisors(k))` assertion is only its k=60 control, not a claimed universal constant bound; the omega(k)*sigma(k) proof is the general charge.

## Input and acquisition limits

Odd modulus, auxiliary primality, k|ell-1, gcd(N,ell*k)=1, nonnegative E and extractor normalization are checked. The combined gcd may equal N, in which case the implementation rejects the coprime contract rather than fabricating a factor or inverse. The semantic extractor statuses require the stated squarefree semiprime promise; accepting other odd moduli does not claim that interpretation there. Native soft-O(m) use additionally requires polynomial-size descriptors and an affordable auxiliary ell/order k. The code does not assert a theorem supplying such an ell universally or making the support condition succeed.

## Verification run

Ran ONLY the existing scoped suite, with the repository's GMP-enabled environment:

    .lake/plot-venv/bin/python -m unittest -v test_packed_gauss.py

All eight tests passed. They include direct full Phi_ell-carrier identities for every character pair in the listed small rings (67 product-constant comparisons), 54 direct quotient exponent checks, ell=2/k=1, proper-order/trivial/canceling components, packed versus quadratic convolution with carry-bound inputs, larger-exponent cocycle/backend agreement, public input rejection, every-divisor parent folding and all support-separation cases. No extra success examples, broad benchmarks, factor-coverage inference, repository edits or implementation changes were made.
