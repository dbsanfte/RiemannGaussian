# A uniform factor-or-large-odd-order supplier for the quadratic torus

24 October 2026. Root construction. This closes a point/order supply
obligation within soft O(k), not the long collision-query obligation.
The output has BOTH local odd orders, including after H powering, above
16k^2. No local-order coprimality is claimed. In particular projection by
N+1 is not included or assumed safe. The original scalar beta and the
quadratic norm-leaf recovery remain available.

## 1. Actual input and theorem

Use the prepared hard branch of `frobenius-pairing.md`, SHA256
`215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`:

    N=P Q, distinct odd primes, P<Q,
    N<=k^6, k=Theta(N^(1/6)), P,Q>16k^2,
    H=k^2, C=16k^2,
    D<0 fundamental, c=|D|<=k/2, gcd(D,N)=1,
    Jacobi(D,N)=-1,
    B=(Z/N)[tau]/(tau^2-D).

The conductor may use either the predecessor's synchronized k or the
new controlled-prime-factor k; this algorithm needs only these bounds.
All public k factors are acquired by trial division in soft sqrt(k),
well within budget. Write bar(tau)=-tau and Norm(U)=U*bar(U).

**Claim.** Deterministically, in soft k BIT operations, return a proper
factor of N or an actually acquired W in B with Norm(W)=1 such that
both local orders of W are odd and

    ord_P(W^H)>C, ord_Q(W^H)>C.                  (1)

The local order means order as a unit of the entire local quadratic
algebra. In a split norm-one algebra both coordinates have the same
order. This claim does not say that these two orders are coprime.

## 2. Norm-one zero tests really test the whole local element

At a prime p|N put epsilon_p=(D/p). The norm-one group T_p is cyclic
of order p-epsilon_p. If epsilon_p=-1 this is the norm-one subgroup
of F_(p^2)^*; if epsilon_p=+1 it is {(u,u^-1):u in F_p^*}.

For EVERY norm-one R and integer n,

    Norm(R^n-1)=0 mod p  iff  R^n=1 in B modulo p. (2)

In the nonsplit case use that B_p is a field. In the split case its
norm is (u^n-1)(u^-n-1)=-(u^n-1)^2/u^n, proving the same assertion.
This is stronger than the corresponding implication for an arbitrary
beta-coupled element; norm-one is essential here.

All gcd tests below use the scalar norm. A proper gcd factors N. A
saturated gcd in (2) means whole-algebra identity at BOTH primes, not
unpaired split support. The algorithm never invokes the bounded beta
leaf decoder on an auxiliary torus value.

## 3. A cheap point outside a supplied small common kernel

Maintain a known positive integer M<k dividing BOTH p-epsilon_p,
p=P,Q. Initially M=1. No factor or sign is supplied. For
1<=a<=2M+1 acquire the actual norm-one Cayley points

    R_a=(a+tau)/(a-tau)
        =(a^2+D+2a*tau)/(a^2-D).                (3)

The scalar denominator a^2+c is positive and less than 16k^2,
because M<k, c<=k/2 and the continuing k>16. It is therefore a unit
at both primes; an explicit gcd/inverse computes it. All parameters
and numerators have O(log N) bits. The points are pairwise distinct
locally: R_a-R_b=2(b-a)tau/((a-tau)(b-tau)), a unit for a!=b in
this range. In particular no hidden square root of D is requested.

Each cyclic group T_p has at most M points killed by M. Among these
2M+1 locally distinct points, at most 2M are killed at either prime.
Scan gcd(Norm(R_a^M-1),N). A proper gcd factors; a saturated value
is discarded; a unit value selects a point R that is outside the
M-kernel at BOTH primes. The count proves that such a selection or
factor occurs. Actual binary powers and gcds give soft M total work.
There is no separate order screen for every palette entry.

## 4. One actual short-order screen per selected point

Set v=ceil(log2(N+1)) and acquire

    W=R^(2^v), q_W=W^H.

Every 2-primary divisor of p-epsilon_p divides 2^v, so both W orders
are odd. This may kill W altogether; the next branch handles that
case and does not assume survival. Computing the power takes O(log N)
constant-rank ring steps.

Run an ACTUAL order screen for q_W through C=(4k)^2. Put b=4k,
acquire A(X)=prod_(s=1)^b(X-q_W^s), and evaluate it at q_W^(-bu)
for 0<=u<b by monic multipoint evaluation. The values, up to units,
are products of q_W^(bu+s)-1 over disjoint consecutive blocks covering
EXACTLY 1,...,C. Coefficient acquisition, all nodes, evaluations,
norms and gcds cost soft k. Monic arithmetic needs no prior separation
of the geometric nodes.

If every block norm is a unit, (2) proves (1), and return W. If a
proper block gcd occurs, return the factor. Otherwise take the FIRST
nonunit block and descend its actual factor tree, always checking the
earlier child first. A proper child gcd factors. A saturated leaf at
index r means q_W^r=1 at both primes, while all earlier indices were
unit by the first-block and earliest-child rule. Thus

    ord_P(q_W)=ord_Q(q_W)=r<=C.                 (4)

This descent costs soft k: the sum of polynomial degrees along its
path is O(b). A globally zero block is not mistaken for an order;
the exact leaf and all earlier exclusions are required.

## 5. Extract the RAW common order using an actually factored multiple

From (4) the RAW point R is killed globally by

    K=2^v H r.

K has O(log N) bits. Its prime factorization is actually acquired:
merge the factors of k, the known power of two, and a trial
factorization of r<=16k^2. The latter uses at most 4k trial divisors,
so costs soft k. No factorization of N+1 or another large unknown
annihilator is requested.

Start T=K, known to kill R at both primes. For each prime ell dividing
T, test gcd(Norm(R^(T/ell)-1),N). A proper gcd factors. A saturated
gcd permits replacing T by T/ell and repeating. A unit gcd says that
NEITHER local order divides T/ell, so both orders have exactly the
current ell-adic valuation of T; retain that power and move to the
next prime. Removing other primes cannot change that valuation.

After O(log K) such tests, either a factor has been found or the
remaining d=T is the EXACT order of R at BOTH primes. In particular
d divides both P-epsilon_P and Q-epsilon_Q. This extraction handles
unequal raw orders: a first differing prime valuation must produce
a proper gcd. It is not inferred from equality of the projected
orders alone. All powering and norm work is polylog N beyond the
paid factorization of r.

## 6. A common divisor at least k gives a factor within budget

For any known d>=k dividing both p-epsilon_p, the smaller prime P
satisfies P=+1 mod d or P=-1 mod d. Search BOTH progressions, using
only positive integers in the exact interval

    2<=d i+epsilon<=floor(sqrt N), epsilon in {+1,-1}.

This includes P even when d=P+1 exceeds sqrt N: the minus progression
then contains its single relevant term d-1. Every listed integer is
less than Q, so a nonunit gcd of any product of these terms is
necessarily the proper factor P; it cannot be N.

The AP product is actually acquired by the usual monic baby/giant
product. If a progression has n terms, take b0=ceil(sqrt n), form
prod_(s=1)^b0(X+d*s+epsilon) with its real starting offset, evaluate
at the corresponding d*b0 multiples for all FULL blocks, and multiply
the remaining fewer than b0 literal terms. Empty lists are skipped.
Using exact final partial blocks avoids overhang beyond floor(sqrt N).
All coefficients, nodes and labels cost soft(b0+1), not soft n.

The number of terms is O(sqrt N/d+1). Since N<=k^6 and d>=k,

    b0=O(sqrt(sqrt N/d)+1)=O(k).

Hence the complete AP search costs soft k BIT operations, including
integer square root and gcds. This is a concrete factor consumer for
the common divisor; it does not require its local signs or the exact
orders of any other element.

## 7. Progress and termination of the supplier

If the common raw order d from Section 5 is at least k, use Section 6.
Otherwise d<k. The chosen R was outside the old M-kernel at both
primes, so d does NOT divide M. Set M'=lcm(M,d). It still divides
both p-epsilon_p, and M'/M is an integer at least two.

If M'>=k, the same AP search factors N. Otherwise replace M by M'
and repeat the small-kernel palette step. This invariant does not
require a single stored element to have order M; M is an acquired
common divisor of the two group orders, sufficient for the kernel
count and the AP search. Lcm updates are exact public integer work.

There are at most O(log k) such iterations. The palette costs sum
soft k because their M values at least double and remain below k.
Each selected-point order screen and small-r factorization costs
soft k; O(log k) repetitions are still soft k. Every iteration
returns a factor, returns W satisfying (1), or increases M. Thus
the total deterministic supplier cost is soft k, with no unproved
palette-survival or point-order premise.

## 8. Consumer and limits

Use the returned W in the actual native targets

    V_j=beta^E_j W^[ell_j+chi_D(j)(N+a_j)].

All targets are still acquired in soft k and their own coverage is
unchanged: norm-one W has local order dividing p-chi_D(p). Their
norms remain beta^(2E_j). The previous same-leaf field-side pairing
therefore supplies exactly the same factor/original-beta consumer.
RERUN the actual short screen for the CHANGED COUPLED seed
z=(beta W)^H. Although q_W has large odd orders, cancellation with
beta could change a split coordinate of z; its old unit certificate
is not reused. The original beta norm argument pays this screen in
soft k, or factors N.

The new supplier rules out the old fixed-Cayley small-torsion collapse
on its continuing branch. It also gives a useful proof-side fact:
at the nonsplit prime, the odd orders of beta^H and W^H divide p-1
and p+1 and are coprime. Hence z there has order equal to their
product, exceeding C^2. This fact requires that nonsplit local field;
no such coprimality is assigned to a split coordinate or to the two
different primes.

This result does NOT supply a balanced point-ideal degree profile,
does NOT make the two local torus orders coprime, and does NOT
certify survival under an additional N+1 projection. The actual
long product still has its prior soft(J+sqrt(JL)) completion.
It is a uniform order-supply improvement within the target budget,
not a proof of the one-sixth factoring exponent or its full Lean
bit-cost composition.
