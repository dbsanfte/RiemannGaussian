# Independent verification: input-dependent high-digit folding probes

2026-10-15. Verdict: **the root's proposed counting argument is sound**, conditional on the frozen balanced supply, local-order and selector-menu inputs. This is a new classical obstruction for a specific N-dependent probe rule, not a universal lower bound for input-dependent algorithms. No repository changes.

## Rule and inherited assumptions

Write d=m² and E_j=N+delta_j with -3d<=delta_j<=d. Define

    i_j(N)=floor(E_j/d) mod d,  0<=i_j<d.

Probe original residuals gamma^(E_j)-gamma^(d(i_j+s)) for every tag and every integer |s|<=S. Use the historical actual ordered prime supply P,Q~M³, m~M, N=PQ~M⁶, projected gamma of exact prime local orders R_P,R_Q with R_P>P^.677 and R_Q>Q^.677. Uniformly R_P,R_Q>=c M^2.031, and P-1=v_P R_P with v_P<=C M^.969, similarly for Q. The proof uses the frozen necessary selector envelope

    p_(-K_*)(m)^6<N<=m^6,
    G_m=m-p_(-K_*)(m),
    sum_m(G_m+1)=O(K_* M),  K_*=O(M^.020).

The scope is this prescribed high-digit folding rule and bounded shifts, not arbitrary N-dependent indices.

## Exact identity and common quotient

Euclidean division gives for every tag

    E_j=m⁴ t_j+d i_j+r_j,
    t_j=floor(E_j/m⁴),  0<=r_j<d.

Thus the residual exponent difference at shift s is

    E_j-d(i_j+s)=m⁴t_j+r_j-ds.              (1)

Delete inputs whose N is within C d of any multiple of m⁴, with a fixed C>3. For every remaining N all offsets delta_j in [-3d,d] keep E_j in the SAME width-m⁴ cell as N. Hence every t_j equals the common

    t=floor(N/m⁴).

The same common t works for all tags and for both hidden-field counts. No source congruence beyond the uniform offset range is needed.

## Boundary deletion cost

The selector makes the possible t values lie in a common interval, independent of P, of cardinality

    O((m⁶-p_(-K_*)(m)^6)/m⁴+1)=O(mG_m+1).

Only O(1) adjacent cell boundaries need be added when counting near-boundary N; this does not change the bound. Fix P and one such boundary. A width-O(m²) window for N induces a Q interval of width O(m²/P)=O(1/M), hence contains O(1) integer Q. There are O(M³) possible first primes. Summing yields

    O(M³ sum_m(mG_m+1))=O(K_* M⁵).

The estimate overcounts all integers Q and therefore bounds prime Q as well. It is independent of the number of tags because the whole input is discarded at once.

## Nonboundary bad-input count

For each possible m,t and freely granted integers r in [0,d), |s|<=S, define

    n=m⁴t+r-ds.                              (2)

On the actual scale t~M². If S=o(M⁴), then n=Theta(M⁶) and in particular n is a POSITIVE NONZERO integer, uniformly over these parameters. For the proposed S<=M^.004 this is immediate. This condition is essential: n=0 would be divisible by every prime and destroy the prime-divisor count.

If any tag has a local zero in the P-field, equation (1), the common quotient, and the exact order imply R_P|n for the corresponding r_j and shift. We grant every r in [0,d) for free, thereby removing all j, slope, carry and offset details from the remaining upper bound. This legitimately enlarges the event set and does not introduce an extra tag factor.

Each n of size O(M⁶) has O(1) distinct prime divisors R>=cM^2.031; in fact at most two for all sufficiently large M, because three such primes have product Omega(M^6.093)>n. The exact divisor count, rather than an enumeration algorithm, is all that is used.

For each such R, the actual first prime must have the form

    P=1+vR,  1<=v<=V,  V=O(M^.969).

There are O(V) possible integers P, and retaining only admissible primes decreases this. Once P,t are fixed, the cell condition m⁴t<=PQ<m⁴(t+1) gives a Q interval of width m⁴/P=O(m), hence O(m) integer partner values. Again this grants all integers and requires no prime-distribution theorem in a short interval.

Multiplying the state budgets and summing yields

    O(V(S+1) sum_m[m² * m * (mG_m+1)])
      = O(K_* V(S+1) M⁵).

The sum uses m~M and sum_m(G_m+1)=O(K_*M); no additional first-prime M³ factor is present in this part, because P was already enumerated as 1+vR. Adding such a factor would double-count P. No extra sum over cofactors is needed beyond V, and the possible actual orders are counted among the O(1) divisors of n.

Swapping P,Q costs only a factor two. The index rule remains the same function of N,m,j, and the common t and free-r enlargement remain valid. Thus the estimate controls all local zeros in either hidden field.

## Quantitative consequence and scope

The nonboundary loss is O(M^5.989(S+1)). For S=O(M^.004) it is O(M^5.993); the boundary O(K_*M⁵) is smaller. Union with the frozen soft O(M^5.994) deletions remains o(M⁶/log²M). Thus an Omega(M⁶/log²M) majority of the original actual inputs has every specified digit-folding shifted residual a unit in BOTH fields, while the full canonical query retains its existing coverage witness.

Polylogarithmic S gives soft O(m) scalar probes per candidate, provided the actual enumeration, source construction and O(log N)-bit exponentiation costs are paid. Polynomial S is granted only for coverage. A polynomial candidate menu likewise does not acquire a nearlinear whole-menu implementation for free. Arbitrary additions, new residuals, different N-dependent folding rules, and a genuinely implicit long-query evaluator remain outside this result.

The argument is stronger than an input-independent sparse-library obstruction because the floor(E_j/d) digit genuinely depends on N and on the source offset. Its strength still comes from a very specific algebraic cancellation: the high quotient becomes common after one small boundary deletion, and all remaining input dependence is confined to a freely granted r range of cardinality m².
