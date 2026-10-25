# A uniform small-multiple cover, with its acquisition cost paid

22 October 2026. This establishes a new **whole-family small-multiple
cover** in deterministic soft O(r) bit work. It does **not** establish a
soft O(r) factoring query, or improve the guaranteed factoring exponent.
The catalog covers a bounded multiple of an unknown factor; recovering
the missing multiplier during the collision search remains unpaid.

The [constructor](../../../scripts/probe_semiprime_fermat_multiplier_cover.py)
implements exact integer convolution, the greedy cover, its witness table,
and the residue catalog. Its optional checks validate the arithmetic.
The uniform guarantee comes from the theorem and proof below, not from
successful semiprime examples. The three Sol 6.1 investigations are retained
in [the cover report](reports/fermat-multiplier-cover.md),
[the independent consumer review](reports/fermat-consumer-independent.md),
and [the structured-multiplier investigation](reports/fermat-structured-cover.md).

## 1. Precise acquired object

Let r be an odd prime, H=r^2, and

    q_r(x) = (x^(r-1)-1)/r modulo r,       r does not divide x.

There is a deterministic algorithm using soft O(r) bit work and storage
that constructs A subset F_r, |A|=O(log^3 r), and

    S = {j^r(1-r*tau) modulo H : 1<=j<r, tau in A}.

This catalog has exactly (r-1)|A| entries. For **every integer x coprime
to r**, some 1<=c<r satisfies c*x modulo H in S. The algorithm also
constructs a table giving such c from q_r(x). This is not an algorithm
for finding q_r(P) when P is an unknown factor of N.

For factoring, choose r=Theta(N^(1/6)) publicly; a sieve and prime search
within a factor of two cost soft O(r), and gcd(r,N) handles r dividing N.
The cover itself has no balance, primality-of-x, or distribution premise.

## 2. Arithmetic proof of coverage and the bit bound

Put Q={q_r(c):1<=c<r}, d=|Q|, and pi=pi(r-1). The proof of
Ostafe--Shparlinski, *Pseudorandomness and Dynamics of Fermat Quotients*,
[Theorem 10 in arXiv v2](https://arxiv.org/pdf/1001.1504v2), gives the
finite bound

    d >= max(1, ceil(pi^2/(pi+r-2))).

To see the exact denominator, count ordered pairs of primes c,e<r
with q_r(c)=q_r(e). Their ratio modulo r^2 belongs to the kernel of
q_r, a group of size r-1. Its identity accounts for pi pairs. Each
nonidentity element accounts for at most one pair: two representations
would give c1*e2=c2*e1 as integers, since their products are below r^2;
unique factorization of these primes forces the pairs equal. Thus the
second moment is at most pi+r-2, and Cauchy proves the bound. The prime
number theorem gives d >= (1+o(1))*r/log^2 r. The source's artificial
q_r(0)=0 adds no image value because q_r(1)=0.

Compute Q and a representative multiplier for each of its values by
r-1 modular powers modulo r^2, costing soft O(r). Start with all quotient
values U=F_r uncovered. For each possible tau compute

    score(tau) = sum_(q in Q) 1_U(tau-q).

The average is d|U|/r. Choose a maximizing tau, append it to A, and
remove tau-Q. After k rounds at most r(1-d/r)^k points remain. The
explicit integer bound

    k <= ceil(r/d)*(bit_length(r)+1)

suffices, and is O(log^3 r). The procedure stops when U is empty;
there is no unproved finite threshold in its stopping condition.

All scores in a round are one cyclic convolution of two binary arrays.
Pack their coefficients in radix 256^w>r. An ordinary integer product
has no coefficient carries, because every convolution coefficient is
at most r. Extract its coefficients and add coefficient i+r to i.
The packed operands have O(r log r) bits, so fast integer multiplication
and linear scans cost soft O(r) per round. The actual implementation
uses byte packing with GMP multiplication, avoiding repeated shifts of
growing integers. The polylogarithmic number of rounds preserves the
soft O(r) bit bound. No floating-point FFT or rounding assumption enters.

When t is first covered, store (tau,c) with t=tau-q_r(c). The homomorphism
q_r(cx)=q_r(c)+q_r(x) then gives q_r(cx)=tau for t=q_r(x).
The element j^r has quotient zero and residue j modulo r, while
q_r(1-r*tau)=tau. These two coordinates determine a unit modulo r^2
uniquely, proving that c*x modulo H is in S. All entries of S are
acquired explicitly in soft O(r); their pair of coordinates also proves
that they are distinct.

## 3. What remains hidden in the catalog

Partition F_r by the chosen shift tau. For each tau let C_tau contain
the chosen multipliers for its assigned quotient values. They are
distinct within that part, and

    sum_tau |C_tau| = r.

For every catalog residue s in the tau layer, allow c in C_tau.
There are exactly r(r-1) such labeled pairs. The map (s,c) -> s/c
modulo H is a bijection onto all units modulo H. This is the precise
distinction between acquiring the small catalog and acquiring all its
collision targets. It is an output count for an explicit expansion,
not a lower bound on a possible shared algorithm.

## 4. A simpler balanced collision query

Suppose N=P*Q for distinct odd primes P<=Q, gcd(N,r)=1, N<=r^6,
and P,Q<=2r^3. For each s in S, acquire

    b_s = centered(-N/s modulo H),       |b_s| <= H/2,
    d_s = (N+s*b_s)/H,
    g_s(h) = b_s*h+d_s.

If cP=s+Hh is the guaranteed covered multiple, direct substitution gives

    g_s(h) = sigma*P,
    H*sigma = b_s*c+Q,
    |sigma| <= Q/H+(r-1)/2 < 3r.

Consequently any unit beta modulo N has the local collision

    beta^(N+b_s*c) = (beta^H)^sigma modulo P.

All row coefficients are paid in soft O(r). The b_s form another
explicit union of quotient layers, since
q_r(b_s)=q_r(N)-q_r(s); q_r(-1)=0 for odd r. For one row, allowing
all 1<=c<r gives a geometric progression, and C_tau selects a subset.
Across rows the bases beta^b_s vary. This is the remaining shared
bilinear-exponent query, with O(r) seed indices but r(r-1) labeled
row/multiplier pairs. No soft O(r) evaluator for it has been constructed.
The expanded giant offsets b_s*c have width O(r^3), so the original
short-offset proof does not certify their pairwise differences as units.
A proposed evaluator must handle that fact; ordinary monic product and
remainder arithmetic does not require those differences to be invertible.

Recovery needs no new conjecture. Use the inherited
[strong-order setup](../semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md)
with m=r. A proper gcd at any leaf factors N. At a globally equal leaf,
write D=ord_N(beta)>256r^4. Both D|phi(N) and
D|(N+b_s*c-H*sigma), so

    D divides P+Q-1+b_s*c-H*sigma.

For the searched |sigma|<=3r this integer has magnitude below 8r^3<D.
It is zero; hence P+Q=1+H*sigma-b_s*c, and an integer square root
recovers the factors. This works at any globally equal leaf, including
one unrelated to the private coverage witness. It is an application of
the existing bounded factor-sum decoder. Restriction-safe evaluation
would permit binary localization with only logarithmic overhead.

The cover remains uniform for unbalanced factors, but the linear bound
there is |sigma|<=Q/H+(r-1)/2. It must not be advertised as O(r) for
the entire unbalanced range. The original all-semiprime query remains
the primary complete target.

## 5. A fully paid consumer, at the older one-quarter rate

There is already an exact consumer for this cover at a larger cost.
Put J=|S| and L=floor((r-1)*floor(sqrt N)/H)+1=O(r^2). The product

    product_(s in S) product_(0<=h<L) (s+Hh) modulo N

contains the covered multiple cP. A block polynomial of degree
d approximately sqrt(JL), evaluated at J*floor(L/d) shifted starts,
computes it in soft O(d+JL/d+J)=soft O(r^(3/2)) bit work. Monic
product/remainder trees require no inversion of point differences.
Handle the common final partial block separately.

All leaf integers are positive and below N whenever the public bound
(r-1)*floor(sqrt N)+H<N holds. A saturated product therefore localizes
to a proper factor by descending block products and then their integer
leaves; no saturated leaf can be divisible by N. The fixed finite range
outside that public bound can be handled directly. The
[independent consumer report](reports/fermat-consumer-independent.md)
gives the details. This is N^(1/4) up to logarithms, and does not improve
the project's existing one-fifth algorithm.

## 6. Validation and retained parallel work

Run the optional constructor checks with:

    ../.venv/bin/python scripts/probe_semiprime_fermat_multiplier_cover.py --self-test

They check exact convolution against an independent ordinary convolution,
including byte boundaries; the witness bijection and catalog identities;
linear-row identities; and invalid-modulus rejection. These are
implementation checks, not asymptotic timing or a finite substitute for
the uniform proof. Independent review also checked the next byte boundary.

The earlier parallel source investigations are retained in
[short-seed-source.md](reports/short-seed-source.md),
[oblivious-source.md](reports/oblivious-source.md), and
[native-shared.md](reports/native-shared.md). They supplied no source
with a proved all-semiprime success guarantee and the required resources.
In particular, the short-interval Dixon extractor is conditional on
splitting relations and its stated circuit interfaces; it is not a
completed uniform factorizer. These exploratory reports do not strengthen
the cover theorem or certify the outstanding machine-model constructions.

No Lean backend, broad build, native coverage campaign, commit, or push
is part of this pass. The full soft-N^(1/6) theorem remains open. The
next mathematical task is a shared consumer that actually extracts the
collision from the acquired structure within the whole-family budget.
