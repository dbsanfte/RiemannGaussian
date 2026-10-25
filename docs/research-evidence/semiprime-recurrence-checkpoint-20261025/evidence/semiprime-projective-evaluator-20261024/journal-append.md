
## Direct evaluator attempts and an acquired scalar circuit, 2026-10-24

This continuation found NO cheaper whole-family acquisition. It tested
projective block pruning, truncated rational reconstruction, the native
antipodal pairing, and compact-circuit factor extraction. The actual query
still costs soft sqrt(JL)=soft k^(3/2); the full deterministic all-semiprime
sixth-rate and executable Lean bit proof remain open. These are scoped
attempts, not general lower bounds. Scratch evidence and primary sources:
`/tmp/semiprime-projective-evaluator-20261024/`.

The positive input fact is now explicit: G_L(X)=prod_(i<L)(X-q^i) has an
ACTUALLY constructed ordinary arithmetic circuit of size soft sqrt L,
uniform in X and with no X-dependent inverses. Choose b=ceil sqrt L,
t=floor(L/b), Q=q^b, and acquire d_s from prod_(r<b)(1-q^r T). The short
polynomial

    B_b(T;X)=sum_(s=0)^b d_s X^(b-s) T^s

is evaluated in T at the FIXED nodes Q^a, a<t, by a monic product/remainder
tree. Multiply those t outputs and the fewer than b actual tail factors.
All powers, coefficients, fixed-node data and scalar gates cost soft(b+t).
The result is G_L(X), through zeros as well as at units. This compiles the
old one-point baby/giant evaluator; it is not a new one-point speedup.
F is also supplied in soft J work. Running the long-product circuit in
B[X]/F costs soft(J sqrt L)=soft k², so this literal batch execution is
worse than the existing shared-block query. The unacquired operation is
uniform selection of the collision factor or weak ratio from these inputs.

The tempting output-degree-sensitive theorem does not provide that
selection. Kaltofen's STOC 1987 Theorems 3/4 bound the LENGTH of a circuit
for a degree-d factor/GCD by O(l M(d³)+d² M(d²)), under their field and
coprimality conditions. At d=1 this is small, but the theorem does not
give a uniform construction at that cost. Its lifting input includes the
selected factor image g0 and associated local data; here the degree-one
image already contains the unknown root/tag. The printed sufficiently
large-field condition is also retained, not inferred from local order
bounds. Kaltofen's 1988 constructive GCD algorithm is different: it needs
no supplied gcd root, but explicitly extracts coefficient vectors up to
the INPUT degree bound d, a unary parameter. That paper sends its
output-degree refinement back to the 1987 result. Neither is promoted
to a deterministic composite-ring collision selector.

Two recent primary algorithms were checked on their actual interfaces.
Van der Hoeven--Lecerf's few-point MPE includes a degree/size term d^n
for fixed variable count n; the univariate degree-L input still costs
soft L. Their 2026 spiroid composition theorem DOES cover arbitrary scalar
Z/rZ deterministically, with bit cost
D^[5/sqrt(log D)] soft(D log r). The extra factor is not polylogarithmic.
It takes supplied coefficient arrays P,Q of degree <D and monic modulus
of degree D. At D=J the required outer G_L mod F is not supplied; padding
to D=L+1 requires dense degree-L input and costs k^[2+o(1)]. Its scalar
composite-ring theorem is not rejected for an imaginary known-prime or
random-pivot premise. An extension to the quadratic coefficient algebra
would still require its own explicit reduction. No short-circuit outer
input contract is claimed from either theorem.

The direct projective pruning attempt returns to the old scalar query.
A block maps (Z,A,B) to (PZ, PA+S0 Z, PB+Sw Z). Certified unit blocks
before a later reset can be skipped, and those after it preserve the
local ratio. Acquiring that unit/nonunit certificate is itself the block
product query. Its bisection costs sum_d soft sqrt(JL/2^d), still
soft sqrt(JL). The short cyclic boundary data do not supply this test.

The tested short Padé route also has an exact unpaid boundary. At any
supplied unit root alpha=V_j, put Q_alpha=F/(X-alpha). For H=G_L/F as a
series at zero, Q_alpha H=G_L/(X-alpha) at EVERY finite precision, whether
alpha is a hit or not. The first coefficient that tests whether the
numerator is a degree-(L-1) polynomial is

    [X^L] G_L(X)/(X-alpha)=-alpha^(-L-1) G_L(alpha).

Thus these particular early-window constraints cannot select the hit;
their first discriminating boundary is the original endpoint value.
The same issue at infinity is the long polynomial part. This does not
rule out other implicit-GCD algorithms. The full-colour antipodal attempt
was checked against the already frozen colour-fusion construction and
adds no new transfer or rate claim, so no duplicate report was created.

The new literature source is `literature.md`, exact SHA256
`83184aa38af9e438ffa27207cef4eeda6bfc347e8b8fa2fa00eaa505e475c1a3`.
Its independent review, primary PDF hashes, integration review and
preservation validator are retained with the scratch packet. No numerical
sample campaign or backend implementation was substituted for a faster
algorithm. Further circuit-based work may use the genuinely supplied
circuit, but must acquire the collision output uniformly; short answer
circuits and low output degree do not perform that selection.
