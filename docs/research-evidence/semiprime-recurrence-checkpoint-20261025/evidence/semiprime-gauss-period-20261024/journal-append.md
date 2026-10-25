
## Quadratic Gauss-period product: paid character rows, 2026-10-24

This pass acquires a nontrivial character-sensitive row representation in
soft O(m), including every native row. It does not acquire the long covered
query in that time: the initialized query remains soft O(m^(3/2)), and the
period-point controller has a separate separator-survival gap. The target
remains deterministic, worst-case soft O(N^(1/6)) for every semiprime, with
full bit-cost and Lean composition unfinished.

Let h=(m-1)/2, chi be the quadratic character modulo the public prime m,
D=chi(-1)m, and B=(Z/N)[tau]/(tau^2-D). In the nontrivial cyclotomic
component, tau maps injectively to the Gauss sum G=sum chi(r)zeta^r,
G^2=D and sigma_j(G)=chi(j)G. The injection is valid after base change
to rings with zero divisors; no hidden square root or residue field is
an input. In the FULL cyclic algebra G_full^2=D(1-e0), and the invariant
algebra has rank THREE, with the extra augmentation component.

For C(T)=prod_(r in QR)(1+T*zeta^r), its first h power sums are
p_k=(-1+chi(k)tau)/2. Fast series exponential of
sum_(k=1)^h (-1)^(k-1)p_k*T^k/k acquires the ENTIRE degree-h C in soft m.
All divisions are by certified small units. Reversal and evaluation give
U(beta)=A(beta)+tau*B(beta)=prod_(r in QR)(beta+zeta^r), with exact norm
(beta^m+1)/(beta+1), a unit from beta's prepared odd local orders. Thus U,
its inverse, and every native row
U^ell_j*(sigma_j U)^a_j*sigma_(j^-1)(U^N) are acquired in soft m total
rank-two arithmetic. The full cyclic relative norm has augmentation
(beta+1)^h; all its rank-three rows are also acquired in soft m. This is
stronger than the preceding rank-one augmentation-only constructor.

There is a uniform RAW point supplier. The tau coefficient polynomial
B(Z) has degree h-1 and unit leading coefficient 1/2. Evaluate A,B at
the m-2=2h-1 locally distinct points beta^t by monic multipoint evaluation.
The two fields together have at most 2h-2 bad B roots. Gcd guards therefore
return a proper factor or a point whose W0=U/bar(U) is nonidentity at
BOTH primes, in soft m. This degree argument does not show survival of
W1=W0^(N-s), where s=Jacobi(D,N). Projection may kill the whole supplied
palette. No all-input short generator theorem is claimed.

Conditional on a projected survivor, the controller is paid and complete.
Local norm-one group orders divide p-chi(p); the public separator N-s
makes the projected orders coprime. A norm(W1-1) gcd gives a factor, a
survivor at both primes, or the explicitly unresolved global identity.
On the survivor branch guarded removal of the 2-part cannot kill both
coprime nontrivial orders. Nor can raising both to H=m^2. One complete
q=W^H short-order screen through 16H costs soft m and gives a factor or
coprime local q-orders >16H. A saturated leaf in an order block is not
an early stopping rule: complete descent in the first nonunit block
finds a proper witness when a short order exists. Scanning O(m) candidate
points is cheap; running O(m) separate order screens would cost soft m^2.

For norm-one x,y, Norm(x-y)=0 mod p iff x=y in the entire local algebra,
INCLUDING the split case. Native targets are Y_j=W^(ell_j+e(N+a_j)),
e=chi(j), and retain the own-index collision. The ordinary monic blocked
query and localization cost soft(J+sqrt(JL))=soft m^(3/2). Saturated global
collisions have a valid new decoder: putting
C0=ell_j+e*a_j-H*i-e*s, the large coprime-order margin implies
abs(C0)=P+Q if s=1, and abs(C0)=Q-P if s=-1. Verified integer square roots
recover the factors. No decoder specific to the original scalar beta is
silently transferred to this period point.

Two concrete recurrence shortcuts were tested. For m=3 mod 4, antipodal
rows have product q^t with t in {-2,-1,0}. A guarded Hilbert-90 gauge folds
each pair into a scalar Dickson recurrence with conditional recovery of
the original period rows. Halving the target count doubles the polynomial
degree in geometric evaluation, leaving the same query exponent. The
period-specific identity U(b)U(-b)=U_chi(2)(-b^2) gives
W(b)W(-b)=W(-b^2)^chi(2). The same COMMON public projection power preserves
it. Its exponentiated residual vanishes for EVERY row, so that tested
residual is not a collision selector. Signed dyadic point values cost
soft(m+K); their K independent order screens or K full row families are
not included in that bound. Neither exact identity yet shortens the long
terminal acquisition.

Exact reports and independent reviews are preserved in
`/tmp/semiprime-gauss-period-20261024`: `period-constructor.md`,
`period-recovery.md`, `period-query-attempt.md`, and their three reviews.
The algebra uses classical Gauss-period and norm-one constructions; no
absolute novelty claim is made. The substantive positive result is a paid
nontrivial character-row constructor and raw point supplier. A soft-m
whole-family query, unconditional projected-point supply, and final bit/Lean
composition remain open. Prior prefixes, all 270 frozen evidence entries,
and concurrent RH work are preserved by the continuation validator.
