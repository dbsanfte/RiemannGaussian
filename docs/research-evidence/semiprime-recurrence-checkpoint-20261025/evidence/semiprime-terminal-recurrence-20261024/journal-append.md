
## 2026-10-24: terminal Toda test and scalar-circuit recovery contracts

This pass did NOT acquire the guaranteed query in soft O(m). It executed
two candidate terminal updates on the original covered family and found
the specific scalar information they still require. The derivative and
padding results below improve the recovery contract; they are supporting
results, not the whole-family acquisition advance requested by the user.
The complete query remains soft(J+sqrt(JL)), J~m,L~m^2. The sixth-rate
theorem and full executable/Lean bit proof remain open.

For a balanced inner block n=J, form the actual rational series

    F*(Zu)/A_n*(u)=sum_r c_r(Z)u^r,
    tau_k^r=det(c_(r+i+j))_(0<=i,j<k).

One full compatible moment vector at a scalar Z costs soft n. Partial
fractions over the unit-separated q grid prove, including zeros,
tau_n^1(Y^-1)=(-1)^(n(n-1)/2)Y^(-n^2) product_(a<n)F(q^aY).
Thus its outer norm is exactly the desired scalar up to a known unit.
The executed condensation step is

    c3*tau_3^1=(c1*c3-c2^2)*(c3*c5-c4^2)
                         -(c2*c4-c3^2)^2.

The entire degree-at-most-nine tau_3 polynomial is acquired without
inverting c3. Normalizing by the paid q-hook constants leaves the norm
of an ADDITIVE mixed-minor expression. Its scalar norm is not determined
by the separate factors' norms. At full support tau_(n+1)=0 and adjacent
tau_n values differ only by known scalar powers: that Toda boundary
eliminates the terminal amplitude rather than acquiring it.

The alternative moment transport is also initialized and executed:

    q^r*c_r(Z/q)-q^(n+r-1)*c_(r-1)(Z/q)=c_r(Z)-c_(r-1)(Z).

Writing g=q^n, its first nontrivial determinant update is

    q^4*tau_2^1(Z/q)=tau_2^1(Z)+(g-1)*Omega,
    Omega=c3-c1*c2+c1^2+g*c1-(g+1)*c2.

The mixed polynomial Omega is acquired at this fixed stage; no rule was
found to obtain every later scalar mixed norm within the target budget.
The full original-grid transport is E1*F(1)=E0*F(q^(nt)). Unit endpoints
give a cheap multiplier c with E1=c*E0, including at E0=0. They do NOT
license division by E0 or initialize its absolute zero mask. Boundary
recovery stays within the original <4H index guard.

The auxiliary cleanup can be extended to K=O(log n) complete pivots at
soft(n+t) cost: compute each entire degree-k^2 polynomial from its 2k
coefficient minor, using only unit integer divisions in trace/Newton
determinants; evaluate their monic reversed product on outer nodes;
handle every exceptional node by an ORIGINAL inner slice. The actual
head/cofactor matrix and next doubled block are acquired too. The tail
still has degree n-O(log n); growing explicit cofactor state costs kt,
and the next norm is not obtained from earlier unit phases. This helper
does not supply an acquisition bound for the entire pivot family.

A separate precise recovery result applies to an ACTUAL size-C circuit
for E(F)=product_i F(x_i), x_i=q^(u+i), as an identity in independent
monic coefficients f_0,...,f_(J-1). Reverse differentiation over Z/N
uses only the original certified unit inverses, never E^-1. It gives
D_k=sum_i x_i^k product_(v!=i)F(x_v). At one local hit this is a nonzero
geometric vector; with two or more hits the whole first gradient is zero.
A native-beta-only program or a Boolean/Jacobi mask is not such a circuit.

Adaptive Hasse evaluation of E(F+z) finds the first coefficient a_h that
is not globally zero. A proper gcd factors when local hit counts differ;
otherwise a_h is a unit and their common count h is known. The actual
cost of lifting/reverse differentiation is soft(C(h+1)), not soft C for
unbounded h. Root's subsequent simplification avoids Newton recovery:

    [z^(h-1)] partial_(Y_j) E(F+z)
       =-a_h*F'(Y_j)*1_(row j hits), in each local field.

The coefficient gradient converts to all these root statistics by one
short convolution and MPE. Since F'(Y_j) is a unit, individual gcds
give a factor when hit sets differ or identify a common hit row when
they agree. No factorial division, hit-polynomial construction or
inversion of a collision is necessary. The selected ORIGINAL row is
localized by its existing soft-sqrt(L) routine. The Hasse acquisition
multiplier h remains; this is not a new fast scalar circuit.

Under the STRONGER contract of a uniform circuit valid on all relevant
degree-J coefficient inputs, multiplicity need not incur that factor:
pad a chosen row subset to degree J and bisect using O(log J) scalar
calls. Zero roots suffice for an unrestricted division-free circuit.
If unit, separated roots are required, acquire J safe dummy roots from
q^(u-s),1<=s<=3J. Evaluate the original F at all candidates; return a
proper gcd, discard globally zero values (at most J), and select J
remaining units. Short q guards separate the dummies from each other
and all seed nodes; the gcd test separates them from all original rows.
Their long product contribution is known UNIT without computing it.
Thus bisection costs soft(C+J+sqrt L), using only original hit rows at
recovery. A pointwise unit trace does not imply this stronger uniform
contract, and padding may destroy properties of a native-only circuit.
This is a paid specialization of the old restriction strategy, not a
claimed new endpoint algorithm or a universal derivative lower bound.

Exact reports and independent reviews are in
/tmp/semiprime-terminal-recurrence-20261024. Reviews corrected a literal
quotient at a possibly zero endpoint and two head/denominator bounds
before acceptance. No successful-example campaign or broad Lean build
was run. Preserve all prior prefixes,270 frozen entries and concurrent
RH work. No commit or push was performed.
