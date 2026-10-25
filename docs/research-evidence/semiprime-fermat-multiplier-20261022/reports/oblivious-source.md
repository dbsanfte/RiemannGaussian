# Constructive stack-source work, 22 October 2026

This investigation produced two legal source constructions and a precise checkpoint obstruction. Neither construction presently proves the required success probability for every semiprime. The remaining obstacle is now explicit: either supply a suitable one-forward/one-reverse consumer for full Dixon relations, or prove nontrivial smooth relations in the explicit short candidate family below. No generic reusable random tape is being hidden in the stack.

## 1. Exact fresh-coin batch sampler with one reverse replay

Fix n, a deterministic trial budget K, and a forward transducer F and backward transducer G. Each transducer uses s bits. For one trial, F reads n coin bits in order, and its final s-bit state is passed to G, which reads those *same* bits in reverse order. Both machines have fixed padded step counts per bit. G ends with an s-bit summary. There is an auxiliary-stack source that runs this experiment independently for all K trials using

    work O(s + log n + log K),
    stack height K(n+s+O(1)),
    time O(Kn * padded per-bit time + Ks).

Construction:

    for i = 1,...,K:
        initialize F
        for j = 1,...,n:
            draw fresh b; update F; push b
        push the fixed-width s-bit final F state
    for i = K,...,1:
        pop the F state into work
        initialize G with that state
        for j = n,...,1:
            b = pop(); update G using b and j
        use or emit G's final summary

The push/pop/idle schedule depends only on n,K,s, not on coins. Each fresh bit is sampled once, and its one subsequent reuse is the legal pop of its stored value. Trials are exactly independent. The proof is direct from the stack layout. Summary output is write-only; it does NOT become a readable matrix or a second stack. A bounded number of summaries can be combined in work if their combined width fits.

For example, a fixed collection m_1,...,m_t with sum log m_i <=s can be handled exactly. Reading X in most-significant-bit order, F updates a_i <-2a_i+b mod m_i. Reading reverse bits, G can update a second collection c_i <-c_i+b*2^j mod m_i using counters for powers of two. This gives exact modular projections and polynomial expressions in those projections. In particular, X^2 modulo each *small* m_i is available. It does not supply (X^2 mod N) mod m_i: the unknown reduction quotient is essential in that expression.

This is a fully legal fresh-coin source with sublinear work and subexponential time whenever s+logK=o(n). Padding its running time gives the hypothesis format required by Cheng–Wu's oblivious-stack result. What it lacks is a full-relation consumer and a subsequent legal matrix consumer, not a sampler.

## 2. A checkpoint lemma rules out naive restoration of the popped word

Here is a limited but rigorous obstruction for the proposed 'scan the stack and restore it' implementation.

Suppose an initially stored uniform word X in {0,1}^ell occupies one contiguous stack segment, the stack below it is independent of X, and no independent copy of X is stored below that segment. Consider the first time that this segment has been completely popped. Assume this time is fixed by the oblivious operation schedule. At this checkpoint, every bit of information about X available to future computation is in the non-stack configuration C: the lower stack has not been exposed before and is independent of X, and popped symbols no longer exist. Previously written output is not readable; future fresh coins are independent.

If the subsequent computation must reproduce X exactly with probability one, then H(X|C)=0, and therefore the number of possible C must be at least 2^ell. For writable space S and time T, ordinary head positions and finite control contribute only O(log(n+T)) additional bits. Thus

    ell <= O(S + log(n+T)).

The same counting argument bounds exact restoration of the stack segment. For ell=Theta(n), S=o(n), logT=o(n), restoration after a complete destructive scan is impossible in this layout. This does not prove a lower bound for every conceivable redundant encoding, every arithmetic predicate, or every factoring algorithm. It does show precisely why the naive single-stack multiple-pass implementation is invalid. A sorting network is a circuit with many stored wires; it does not by itself implement those wires using one LIFO stack.

## 3. A complete short-candidate deterministic Dixon extractor

The following removes random-input reuse completely and carries the construction through kernel finding and factor extraction. Its unresolved premise is a number-theoretic success statement, rather than a machine-model premise.

Choose fixed 0<alpha,beta<1/2, let B=ceil(exp(n^alpha)) and H=ceil(exp(n^beta)), and put a=ceil(sqrt(N)). Define the explicit roots

    x_h = a+h,       0<=h<H.

For sufficiently large n, all x_h^2<2N, so their residues are the explicit positive integers

    y_h = x_h^2-N.

Use the primes up to B as a factor base, after first testing whether any divides N. Keep the columns h for which y_h is B-smooth, and form their prime-exponent parity matrix A. Every quantity here is a deterministic function of N and the O(logH)-bit h. Thus any bit can be recomputed without remembering n-bit random data. Standard uniform shallow integer arithmetic plus binary linear algebra gives the same kind of deterministic shallow circuit proposed for Dixon; there is no random input to replay.

Compute a basis c^(1),...,c^(d) of ker(A), extending each vector by zeros at nonsmooth columns. For each basis vector, compute

    U_j = product_h x_h^(c_h^(j)) mod N,
    V_j = product_p p^((sum_h c_h^(j) v_p(y_h))/2) mod N,
    g_j = gcd(U_j-V_j,N).

Also test gcd(x_h,N), since a nonunit root can immediately factor N. Return any proper factor found, or failure.

The kernel basis really suffices. Assume no root or factor-base prime divides N. For c in ker(A), define r(c)=U(c)/V(c) modulo N. Because c is a parity dependency, r(c)^2=1. Furthermore r is a group homomorphism from the binary kernel to the square roots of unity: for c,d, the integer product correction from positions where c_h=d_h=1 is the same on U and V, because y_h=x_h^2 modulo N and the positive smooth square roots used for V multiply exactly. Hence r(c+d)=r(c)r(d).

For an odd squarefree semiprime N=pq, the trivial roots {1,-1} form a subgroup. If *some* kernel vector has r(c) outside this subgroup, some basis vector does too; otherwise the subgroup would contain the image of the entire kernel. For that basis vector, gcd(U-V,N) is a proper factor. Even semiprimes and prime squares are separately recognizable by elementary arithmetic.

Consequently this is a proved extractor with this exact behavior:

    It returns a proper factor if and only if the explicit candidate set
    contains a nontrivial congruence obtainable from its smooth relations
    (or a candidate/factor-base prime already exposes a divisor).

All products can be taken as full virtual integer products before modular reduction. Their bit lengths are at most H*O(n), which is exp(o(n)). **Up to the final integer gcd**, a uniform bounded-fan-in circuit has size exp(O(n^alpha+n^beta+polylog n)) and depth O(n^(2alpha)+n^(2beta)+polylog n), subject to the same standard integer-arithmetic and GF(2)-kernel uniformity details already used in the parent circuit construction. Its deterministic path-based evaluator has o(n) writable space and exp(o(n)) time. No assertion that integer gcd is NC is needed or intended.

The gcd can instead be wrapped using Williams's time-to-space theorem. Fast integer gcd has multitape time n^(log_2(3)+o(1)), already using Karatsuba multiplication and the half-gcd method; quasi-linear multiplication gives an even stronger bound. Apply Williams's TIME[t] subset SPACE[O(sqrt(t log t))] to the language asking for one specified output bit of gcd(a,b). This yields a deterministic O(n^((log_2 3)/2+o(1)))=o(n)-space bit algorithm. Its halting time is exp(o(n)) by configuration counting. Supply its a,b inputs virtually, recomputing a requested U_j,V_j input bit with the preceding circuit evaluator. The two workspaces add, so remain o(n), and the times multiply, so remain exp(o(n)). Loop through the at most H basis vectors using an O(logH)-bit index; find the first proper gcd and emit its bits by repeating the bit procedure. The same wrapper handles candidate gcds. The complete extractor therefore has deterministic o(n) work and exp(o(n)) time under the stated arithmetic/kernel circuit bounds, without any auxiliary stack or reusable random tape.

Primary references for the gcd wrapper: R. T. Moenck, *Fast computation of GCDs*, STOC 1973, https://doi.org/10.1145/800125.804045 ; R. R. Williams, *Simulating Time With Square-Root Space*, STOC 2025, https://people.csail.mit.edu/rrw/time-vs-space.pdf . These establish the fast-gcd/time-to-space ingredients; the virtual-input composition argument above is elementary.

The unproved next stage is now one explicit statement: for every sufficiently large squarefree semiprime, does this H-term short interval contain a smooth-relation dependency whose root ratio is nontrivial? Standard uniform-root Dixon analysis does not prove this. Merely counting smooth y_h, even if it supplied more columns than rows, would guarantee a dependency but would not guarantee that its root ratio splits N. The construction is useful as a rigorous experimental target and certificate extractor, but does not justify an all-semiprime factoring claim.

## 4. Why the smallest-root substitute fails outright

A tempting source is to use an o(n)-bit seed h directly as x_h=h. For balanced semiprimes with both prime factors exceeding H=exp(o(n)), every x_h<H<sqrt(N) has y_h=x_h^2 as an ordinary integer. Every smooth relation then has all exponent parities zero and positive square root exactly x_h. Every combined congruence has U=V modulo N, and candidate gcds are one. This family never produces a proper factor on that regime. Moving roots to ceil(sqrt(N))+h avoids this elementary obstruction, but returns us to the explicit unproved short-interval statement above.

## Primary theorem used

Cheng–Wu, v3, Section 10.5, Corollary 7 uses fresh random blocks and requires the push/pop/idle schedule to be independent of randomness. The batch construction in Section 1 meets those access requirements literally. It does not turn the circuit extractor's arbitrary input queries into stack operations.

https://arxiv.org/html/2609.23603v3#S10.SS5
