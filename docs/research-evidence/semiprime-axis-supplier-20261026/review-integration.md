# Primary-agent integration review

26 October 2026. Paper arithmetic and source review; no experimental claim.

## Restricted lattice search

Re-read Harvey–Hittmeir Proposition 3.3, Algorithm 4.3 and the recovery
interfaces from the primary PDF extraction and HTML. The modulus-squared
congruence uses the acquired inverse of sigma modulo n^2, not a presumed
lift of the unknown P. The lattice congruence on (a,b) cancels the unknown
first-order lift. Restricting the residue loop retains the proof whenever
the supplied menu contains P mod n.

The integer centre loop has no uncovered integers: the next start is
ceil((1+1/r)*sigma0). Every intervening integer lies in the current
half-open real interval. Inclusive rectangle endpoints require retaining
starts through U, rather than stopping at U. True P is strictly below
sqrt N because P<Q.

For S candidates at n|k, r=ceil(16k/S) and n>=S*k^(1/3) give
Sr<=16k+S, nr>=16k^(4/3), and kappa<=k/8+3<k. The identity
q=(beta^(n^2))^(H/n^2) supplies BOTH local orders. This divisibility
argument does not need the separate 3-coprimality gate. The exact
coefficient heights and integer parameters satisfy the primary polynomial
size assumptions. Bit arithmetic is absorbed only in logarithmic factors.

The source's informal bound on the number of global matches is unnecessary:
there can be one per giant, and that count is already paid. Before deleting
any globally matched giant, test its exact u. If it is the true giant,
local baby distinctness forces the true i. For nonzero b the equation
bX^2-uX+aN=0 has P as a root; when b=0 recover Q from u/a, and when
a=0 recover P from u/b. Both coefficients zero is excluded. Test all
integer candidate factors, including when the discriminant is zero.

After global matches are removed, Algorithm 4.1 needs no annihilator:
if an evaluation is zero modulo N, one of its individual differences has
a nontrivial gcd, since no individual difference is zero modulo N.
Literal global equalities are handled by the arithmetic recovery test,
not sent to a nonexistent nonzero-exponent extractor. A wrong input
palette is allowed to fail, not to declare primality.

## Joint interval and residue information

The native divisor-modulus order argument also applies to arbitrary
supplied factor rectangles. For positive-width integer intervals,
delta=(U-L)/L>=1/sqrt N. Choose dyadic d with delta<=d<2delta.
The common binary denominator, all d and their sum have O(log N) bits
when A=O(k). If Delta=sum delta and Dhat=sum d, then
Delta<=Dhat<2Delta. Put r=ceil(32k/Dhat).

Under Delta<=n/k^(1/3), nr>=16k^(4/3), while
r*Dhat<=32k+Dhat. Since U<=2L, Dhat<2A=O(k). All starts therefore
cost O(A+k), and the old kappa<k guard applies unchanged. If any interval
has positive width, Dhat>=1/sqrt N, so r=O(k*sqrt N)=O(N^(2/3)); this
meets the primary r=O(N) hypothesis at the native scale. Point intervals
are tested first. A=0 or an incorrect list returns bounded failure.

The general optimized formula has the r>=1 ceiling term. It is valid
only with the corresponding local order guard; the explicit target-scale
parameters above prove that guard, rather than treating it as free at
every formal optimum. Pairing a residue modulus k^(1/6) with relative
width k^(-1/6) is a true combined-input regime. No such rectangle list
has been acquired from the native row data by this packet.

## Axis recurrence and phase gate

For n=k/2, t odd and r=(t+1)/2, h=r-nI tiles [1-nM,n(M+1)] exactly.
Deleting h=0 and reflecting negative exponents gives a known unit times
Q_(nM-1)(u)*Q_(n(M+1))(u), u=beta^(2k). Since the shorter prefix is
contained in the longer, their product has the same local nonunit
predicate as the longer prefix. This uses containment, not numerical
division by the shorter product. Positive reflected hits are original
axis leaves. Their integer residue, not an assumed stationary label,
is what transports to the kernel.

The cleared recurrence shifts r by m, so P_1,...,P_m remain the initial
values. Their certified short denominators do not compute those values.
The soft(m+sqrt B) initialized cost is an upper bound for this attempt,
not a lower bound on all phase suppliers or faster recurrences.

The paired AP argument was independently checked. A fixed-rho norm must
remain a fixed-rho filter; the source report's earlier whole-query wording
has been corrected in the archived version. Combining all rho channels,
not taking the norm of one channel, restores the whole nonunit predicate.
All full-cap exclusions are factor-or-certificate implications. Neither
the complement relation N/sigma nor faithful external phases identify an
arbitrary collision tag with the actual P residue.

## Scope

The new costed consumer and its combined-information version are useful
progress in the required input specification. They do not improve the
whole-family query, prove a covered small palette, prove a general
algorithmic obstruction, or complete the all-semiprime sixth-exponent
bit bound. The original prepared branch and its costs remain inherited
obligations. The rank-three preprint's general correctness is not certified
here and is not needed for either positive consumer.
