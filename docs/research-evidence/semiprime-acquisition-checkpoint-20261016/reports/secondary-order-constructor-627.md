# An explicit secondary-order acquisition row

This is scratch research, not a universal factoring algorithm or a compiled theorem. No repository file was edited. The safe-prime case remains open.

Let N=(2d+1)(2e+1), where d,e are distinct odd primes, and let the supplied unit gamma have local orders d,e. Put A=N-1. Then

    A = 2(d+e+2de),   A mod d = 2e,   A mod e = 2d.

In particular A is coprime to de. There is an actual deterministic N-dependent acquisition algorithm with an explicit restricted coverage guarantee:

1. Set x_0=gamma.
2. For r=1,...,R compute x_r=x_(r-1)^A modulo N and g_r=gcd(x_r-gamma,N).
3. Return a proper g_r immediately. If g_r=N, construct K=A^r-1 and invoke the accepted nonzero-annihilator decoder. If every g_r=1, return uncovered.

The exact local hit equivalence is

    x_r=gamma mod (2d+1)
    iff d divides A^r-1
    iff ord_d(2e) divides r.

The analogous condition at the other factor is ord_e(2d)|r. Hence the row is guaranteed to hit if either of these two secondary orders is at most R. A saturated hit gives the positive integer K=(N-1)^r-1, with at most r*ceil(log2(N-1))+1 bits; no hidden order or prefactorization is used. The explicit iteration costs soft O(R), and constructing and decoding its one selected K costs soft O(R log N+N^(1/12)). Taking R=floor(m/log(2N)) therefore respects the soft O(m) budget. Increasing R by logarithmic factors does not affect the soft exponent, but the selected integer's full bit length must still be charged.

The missing universal coverage statement is substantial: the safe-prime promise alone has not been shown to force either ord_d(2e) or ord_e(2d) below this R. I do not assert that statement, nor infer it from primality. This row is a concrete N-dependent exponent constructor with a proved conditional hit, not the requested all-input constructor. I found no proved way to combine such rows within total soft O(m) work to cover every safe pair.

## Discarded coefficient direction

The huge central coefficient C=binom(N-1,(N-1)/2) separates the factors when P<Q<2P: C=0 modulo P and C is nonzero modulo Q. The correct latter residue is

    C = (-1)^((Q-1)/2) binom(P-1,(P-1)/2) mod Q,

and is generally NOT 1. An earlier intermediate message claiming 1 applied a mod-P identity modulo Q; it was corrected during review.

This central coefficient adds no useful target beyond the repository's existing stronger coefficient binom(N-1,floor(sqrt(2N))) and sparse Frobenius-prefix factor-sum formula. I found no cheaper coefficient evaluator. Periodically folding the full polynomial includes its unwanted tail, and the final sparse truncation is not acquired by ordinary scalar exponentiation. Consequently no coefficient-computation saving is claimed here.

The coefficient reasoning uses Lucas congruences; primary-source survey consulted: Romeo Mestrovic, *Lucas' theorem: its generalizations, extensions and applications (1878--2014)*, https://arxiv.org/abs/1409.3820. The secondary-order identities above are elementary derivations and do not use that source.
