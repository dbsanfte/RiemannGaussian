# Independent bounds inside the joined local Vaughan remainder

2026-10-23. Follow-up investigation of the signed ordinary-prime bound.
The finite shared-prime coefficient identity is compiled in
[SuzukiLocalCancellationSharedPrime.lean](../RiemannGaussian/SuzukiLocalCancellationSharedPrime.lean).
The actual density integral and a coarser uniform lattice bound
`53/sqrtX` are compiled in
[Physical](../RiemannGaussian/SuzukiLocalCancellationPhysical.lean) and
[Sampling](../RiemannGaussian/SuzukiLocalCancellationSampling.lean).
The sharper variation constants, complete Vaughan rearrangement, and
sector estimates below are paper derivations, not Lean theorems.
No bound on the complete joined signed prime remainder or RH is asserted.

The main result of this calculation is section 3: all proper-power and
shared-prime terms can be bounded by a prescribed `O(X^epsilon)` allowance
using exponent-dependent cutoffs. What remains is one specific coprime
prime/Möbius expression, including its harmonic head. Existing norms and
the semiprime operator identities do not bound that joined expression.

Write h=log2, c=sqrt2, K_X(y)=y^(-1/2)W(log(y/X)),
Q=8X, and K0=(c+1)h. Use exactly the original W and its zero endpoints.
For X>=2 and integer 1<=U<=X^(1/4), the previously checked calculation gives

    G(X)=J sqrtX M_harm(U)+B_(U,U)(X)+E,
    J=-4hc(c-1)^2,
    M_harm(U)=sum_(d<=U)mu(d)/d,
    |E|<=(3hU/(2sqrtX))[log(8X)+h+6U].

The supremum of this error over that whole cutoff range is <=15h+6h^2.
The required input is the actual zero-density sampling bound

    |sum_(m>=1)K_X(qm)|<=3h/(2sqrtX), uniformly q>0.       (L)

It follows from integral K_X=0 and TV(K_X)=3h/sqrtX. No phase or sign is
discarded between the two original prime packets to obtain (L).

## 1. Exact shared-prime collapse and its bounded whole-sector cost

Let B_sh retain exactly l=p^k>U and p|d in B. The identity

    mu(pa)=-mu(a) if p does not divide a, and 0 otherwise

keeps all square-factor zeros. Completing a>U/p to all a gives exactly

    B_sh=-P_sh+C_sh,
    P_sh=sum_(p prime,k>=1:p^k>U,j>=0) logp K_X(p^(k+1+j)),
    C_sh=sum_(p prime,k>=1:p^k>U) logp
          sum_(a>=1:pa<=U,p∤a) mu(a) sum_(m>=1)K_X(p^(k+1)am).

Every displayed sum is finite by support. The full completed divisor
coefficient is

    sum_(a|r,p∤a)mu(a)=1 if r is a power of p (including r=1), else0.

The compiled form uses r=p^s*b with p∤b, with no supplied hidden divisor:

    sharedTailCoefficient U p (p^s*b)
      =-1_(b=1)+sum_(a|p^s*b,pa<=U,p∤a)mu(a).

This is `sharedTailCoefficient_eq_completed_head`. For p>U its correction
is empty, as checked by `sharedTailCoefficient_eq_of_cutoff_lt_prime`.
Both retain strict original cutoff U<pa; s=0 is included.

In P_sh, a given p^r,r>=2 has multiplicity
#{k:1<=k<r,p^k>U}<=r-1. The squares therefore cost at most
K0 theta(sqrt(8X))/sqrtX <=18 K0 using theta(y)<=6y and sqrt8<3.
All higher powers have one absolutely summable global majorant:

    sum_(r>=3)(r-1)p^(-r/2)
      <=20 p^(-3/2), p>=2,

because p^(-1/2)<=3/4 and sum_(j>=0)(j+2)(3/4)^j=20.
The series sum_p logp/p^(3/2) is finite; Chebyshev partial summation bounds
it by18. Hence |P_sh|<=378 K0 is one deliberately coarse uniform bound.
No growing prime exponent can be discarded without this majorant.

For C_sh only p<=U occurs, and k has at most log(8X)/logp possible values.
Use (L), sum_(a<=U/p)|mu(a)|<=U/p, and
sum_(p<=U)1/p<=logU (also valid at U=1, with an empty prime sum). Then

    |C_sh|<=(3hU/(2sqrtX))log(8X)logU
            =O(X^(-1/4)log^2X)

throughout U<=X^(1/4). In particular |C_sh|<=12h+(9/2)h^2 follows by
putting t=logX/4 and using t exp(-t)<=1, t^2 exp(-t)<=2.
Thus the ENTIRE original shared-prime sector is uniformly O(1).
It is not bounded by taking absolute values before divisor completion.

For the final ordinary-prime reduction below there is a simpler route:
first remove the proper-l sector, then in the ordinary-l shared sector
p=l>U automatically. Its correction is empty and its pure-power sum has
no r-1 multiplicity. The existing proper-power packet majorant suffices.

## 2. Entire proper-l sector: O(1+sqrtU), and cubes/higher individually O(1)

Let a_l=Lambda(l) if l is a PROPER prime power, else0. For any specified
subset A of these l (in particular l>U), completing d>U via mu*1=epsilon
gives exactly

    B_A=sum_(l in A) a_l K_X(l)
          -sum_(d<=U)mu(d)sum_(l in A)a_l sum_m K_X(dlm).

The first term has the existing uniform proper-power packet bound. The
second term is NOT that packet and cannot be deleted for free.
By (L), support, and the divisor cutoff,

    |correction|<=3h/(2sqrtX) sum_(l in A)a_l min(U,Q/l).

Let A(y)=sum_(l<=y)a_l<=psi(y)-theta(y)<=18sqrt y for y>=1.
At Y=Q/U>=1, the low-l part is <=18U sqrtY. Partial summation gives
sum_(l>Y)a_l/l<=36/sqrtY. Therefore the ENTIRE weighted sum is

    <=54sqrt(UQ),
    |correction|<=81h sqrt8 sqrtU <=243h sqrtU.

This proves O(1+sqrtU) for all proper-l powers together, retaining both
large-factor cutoffs and all shared-prime intersections. It immediately
gives O(X^(1/8)) at U=floor X^(1/4). The square-l part has this scale in
the absolute completion method; it is not a bounded deletion at that fixed U.

There is a stronger component bound for l=p^k,k>=3. For each k>=3,
Chebyshev splitting at Y_k=(Q/U)^(1/k) yields

    sum_p logp min(U,Q/p^k)
      <=6(1+k/(k-1)) U^(1-1/k)Q^(1/k)
      <=15 U^(1-1/k)Q^(1/k).

After multiplication by X^(-1/2), k=3 costs
O(U^(2/3)X^(-1/6))=O(1). For k>=4, each is at most
O(U^(3/4)X^(-1/4))=O(X^(-1/16)); there are O(logX) supported k.
Hence the whole cubic-and-higher-l sector has O(1) cost when U<=X^(1/4).
This does not turn the square-l sector into O(1).

## 3. Exponent-dependent cutoffs remove the square obstacle legitimately

Define the exact distinct-prime bilinear sector

    B_dist(U;X)=sum_(p>U prime,d>U,p∤d,m>=1)
                   mu(d)logp K_X(dpm).

Do NOT assume d prime, d coprime to m, or p coprime to m. The only removed
intersection is p|d, paid as above. All squarefree and square-factor zeros
of mu(d) remain exact. The preceding estimates give uniformly for
1<=U<=X^(1/4), X>=2,

    G(X)=J sqrtX M_harm(U)+B_dist(U;X)+O(1+sqrtU).

More explicitly, the absolute error is at most

    108 K0 + 81h sqrt8 sqrtU
      +(3hU/(2sqrtX))[log(8X)+h+6U]
    <=108 K0+81h sqrt8 sqrtU+15h+6h^2.

The two `54K0` contributions pay the pure proper-l packet and the
ordinary-l shared-prime packet separately. These constants have been
independently checked on paper; they are not the coarser compiled lattice
constant substituted into a claimed formal Vaughan theorem.

The implicit constant is absolute for this fixed W. This is the sharpest
useful current reduction; it is more flexible than fixing U=X^(1/4).
Given target epsilon>0, set

    delta=min(1/4,2epsilon), U_epsilon(X)=floor(X^delta).

Then U>=1 even for2<=X<16, U<=X^(1/4), and sqrtU<=X^epsilon.
Thus (T) is EQUIVALENT to the all-epsilon one-sided bound for

    R_dist,epsilon(X)=J sqrtX M_harm(U_epsilon(X))
                       +B_dist(U_epsilon(X);X).

The complete error is at most
`[108K0+81h sqrt8+15h+6h^2]X^epsilon`, with a constant independent of
epsilon. Each direction absorbs this allowance, plus the
already paid O(1) ordinary-prime/full-G difference. Constants and starting
cutoffs may depend on epsilon; U is intentionally allowed that dependence.
This does not prove the lower bound for R_dist,epsilon. It identifies the
actual remaining signed ordinary-prime/Möbius interaction after independently
paying all proper-l powers and all shared-prime sectors at the desired scale.

## 4. Quantitative Möbius tests and why their separate norms do not close it

The compiled repository estimate is
`exists_moebiusFinitePrefix_exponential_remainder` in
`MoebiusFiniteQuantitativeCancellation.lean`, with

    |M(t)|<=C exp(-h/2)t+exp(C0 h^3), C0=10^15,

for all real scale h above one threshold and all integer t. Ordered
harmonic cancellation and its cubic-log rate are compiled in
`MoebiusHarmonicCancellation.lean`. No fixed7/8-power Mertens theorem
was located compiled in this search. The imported seven-eighths nonvanishing
is a distinct theorem; it does not license silently inserting an unproved
quantitative Mertens adapter into Lean.

For a precise strength comparison, ASSUME |M(t)|<=A t^alpha,
1/2<alpha<1, for all t>=1. Partial summation, using the existing ordered
harmonic limit0, gives

    |M_harm(U)|<=A(1+1/(1-alpha))U^(alpha-1).

Summing the full B by parts in d, including its strict lower boundary,
gives only

    |B_(U,U)(X)| << A sqrtX U^(alpha-1)log(8X).

At U=X^(1/4), alpha=7/8, both separate norm budgets have exponent15/32
(the B budget also has logX), WORSE than the existing-baseline full-G
3/8 baseline. At U=X^delta the head exponent is1/2-delta/8, becoming
even closer to1/2 for small target epsilon. The actual head/B cancellation
is therefore necessary; tuning U does not make it available by norms.
Even optimizing the elementary mu*log hyperbola cutoff alone gives
alpha/[2(2-alpha)]=7/18 at alpha7/8, still weaker than3/8.

One can improve the proper-l component with signed mu. Let

    S_X(d)=sum_(l proper,l>U)a_l sum_m K_X(dlm).

The grid estimate gives |S_X(d)|<<d^(-1/2). Differentiate on the finite
smooth pieces in real d: S'_X(d)=d^-1 sum_l a_l sum_m L_X(dlm), with
L_X(y)=y K'_X(y). Here integral L_X=−integral K_X=0 and
TV(L_X)=O(X^(-1/2)), so |S'_X(d)|<<d^(-3/2) almost everywhere.
The finite piecewise-smooth function is absolutely continuous; knot values
are not discarded. Abel summation then gives

    |sum_(d<=U)mu(d)S_X(d)| << A U^(alpha-1/2).

At alpha7/8 this is O(U^(3/8)), or O(X^(3/32)) for the fixed quarter-power
cutoff. This remains conditional on the stated Mertens hypothesis.
The COMPILED cubic-scale remainder instead gives the genuine adapter bound

    <<exp(-h/2)sqrtU+exp(C0h^3),

and hence <<sqrtU exp(-h/2) if U>=exp(4C0h^3), h sufficiently large.
This strengthens the square-l component to o(sqrtU) with a cubic-log saving,
but does not control the joined distinct-prime/harmonic term.

## 5. Remaining operation and source check

The next arithmetic estimate must retain R_dist,epsilon as ONE signed
quantity. Completing its ordinary-prime fibre all the way simply returns
the original prime packet plus finite heads; that is not a new bound.
The special W cancels the density mean and makes every completed lattice
fibre small. Its Mellin multiplier is nevertheless NONZERO at every
rho-1/2 with Re(rho)>1/2, so no further automatic suppression of those
source exponents is available from this fixed filter alone.

The semiprime unitary/commutator quadratic-form inequalities require their
actual Hilbert-space adjoint and positive measure. The present remaining
linear signed sum has mu(d) coefficients on integer product fibres; it has
not been identified with such a positive form. No operator-positivity
claim supplies the missing distinct-prime bound.
