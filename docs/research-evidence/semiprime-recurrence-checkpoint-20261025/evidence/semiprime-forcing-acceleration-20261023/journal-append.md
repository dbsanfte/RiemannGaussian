
## Fast fixed-matrix core and joint correction identities, 2026-10-23

Continuing the user's request for a better recurrence algorithm, this pass
constructs a fast auxiliary operation and simplifies the coupled correction.
Neither supplies a faster ORIGINAL covered query. Its best acquired bound
remains soft(J+sqrt(JL)), with J~m, L~m². The sixth-rate objective remains
open, as does full executable/Lean bit integration after query acquisition.

**An actually acquired fixed-matrix power.** Normalize the source to
P_n(X)=product_(i<n)(1-q^i X), with target polynomial F of degree J.
Let C multiply by X modulo F, D=diag(1,q,...,q^(J-1)), M=(I-C)D.
Coefficient scaling D is applied to the proper representative; arbitrary
substitution is not assumed to descend through the quotient.

For 0<=k<=J, M^k e0=P_k(C)e0: the representative has degree<J before
the last multiplication. Put kappa_k=(-1)^k q^(k(k-1)/2), and acquire
F=sum_(k<=J) nu_k P_k. The coefficient columns P_0,...,P_(J-1) form a
triangular Krylov basis K with certified unit diagonal entries kappa_k.
Consequently the ACTUAL characteristic
polynomial over Z/N, including zero divisors, is

    mu_M(T)=kappa_J*sum_(k<=J) nu_k T^k.

This follows from the reduced expansion of F and invertible cyclic K;
it is not merely a field-only scalar annihilator. The basis conversion is
explicitly cheap. With Q_i=product_(1<=h<=i)(1-q^h),

    [X^i]F*Q_i/kappa_i=sum_(k>=i) nu_k*Q_k/Q_(k-i).

After index reversal this is Toeplitz convolution. The inverse kernel of
1/Q_n is kappa_n/Q_n through J: their nth convolution is P_n(1)/Q_n,
zero for n>0. Thus both conversions cost soft J using only the already
certified q-factorial units. Modular powering T^L mod mu_M, then K,
acquires M^L e0 in soft(J log L); the same holds for a supplied vector.
All divisions of polynomials use monic divisors. This positive operation
does not require an endpoint or collision-bearing value to be invertible.

**The exact initialized correction is still necessary.** Write
F=X^J+sum_(i<J) f_i X^i, v=e_(J-1), w_i=f_i(q^J-q^i), u=(I-C)w.
Then DC-qCD=w v^t and MC-qCM=u v^t. If P_n=F Q_n+R_n, define
s_n=Q_n(qC)u only as the invariant; the algorithm need not be supplied Q_n.
It has the fully initialized finite recurrence

    R_0=e0, s_0=0,
    R_(n+1)=M R_n-s_n,
    s_(n+1)=(I-q^(n+1)C)s_n-q^n*u*(v^t R_n).

The first equation retains F(qC)e0=-w; the second follows from
Q_(n+1)=(1-q^n X)Q_n-q^n(v^t R_n). Its direct cost is soft JL,
and its exact final correction is

    R_L=M^L e0-sum_(n<L) M^(L-1-n)s_n.

Fast supplied-vector powers do NOT acquire these jointly dependent s_n.
Indeed the tested shear eta_n=s_n-(M-I+q^n C)R_n gives
R_(n+1)=(I-q^n C)R_n-eta_n, eta_(n+1)=M eta_n, eta_0=0.
It exposes the unchanged variable-coefficient product; it is not a new
solver. The fast core is a concrete auxiliary gain, not a query exponent
gain or a proof that some other feedback algorithm must fail.

**A fresh joint boundary state.** In the q-Newton basis, multiplication
modulo F is a rank-one perturbation of multiplication modulo P_J/kappa_J.
Evaluation at lambda_r=q^(-r) diagonalizes the latter by a paid transform:
C=diag(lambda)+alpha beta^t. The actual states obey
y_(n+1,r)=(1-q^(n-r))y_(n,r)-q^n alpha_r tau_n, tau_n=beta^t y_n.
Startup is explicit: tau_n=0 for n<J-1 and tau_(J-1)=1. Define

    H_s(n)=sum_(k<n) q^((s+1)k)*tau_k/Q_k,
    A_r(Z)=product_(j<r)(1-q^(-j)Z)=sum_(s<=r) A_(r,s)Z^s.

For n>=J, exact variation of constants gives
y_(n,r)=-alpha_r Q_(n-1-r) sum_(s<=r) A_(r,s)H_s(n).
The triangular A transform is one scaled convolution; all terminal
factorials and inverse interpolation cost soft(J+sqrt L). Thus ALL output
coordinates are decoded jointly from H(L) at the desired clock. These
moments have acquired nonzero startup
H_s(J)=q^((s+1)(J-1))/Q_(J-1), and update by
H_s(n+1)=H_s(n)+q^((s+1)n)tau_n/Q_n with tau_n from the decoded state.
The remaining operation is a fast solve of THIS initialized feedback.
Geometric evaluation of the formal series sum tau_k Z^k/Q_k is not a
solution while its coefficients are unacquired. This is a new candidate
state with cheap joint decoding, not a whole-query improvement.

**All dyadic corrections can be kept together algebraically.** In the
previous padded square construction let Y=Z^B, E_B=QY-q^(-B)YQ,
E1=QZ-q^(-1)ZQ, and let T divide entries by
Sigma_B(z_i,q*z_j)=sum_(s<B) z_i^s(q*z_j)^(B-1-s).
Its dyadic factors are all units in the prepared odd-order groups.
Using A_s(V)=q^s VZ^s-Z^sV, the polynomial identity T A_B=A_1 and
the product rule A_s(SV)=S A_s(V)+[S,Z^s]V give exactly

    T(S E_B)=S T(E_B)+q^(-B)[S,Z]Q-q^(-B)T([S,Y]Q),
    T(E_B)=q^(1-B)E1.

Thus the recursive hierarchy telescopes to TWO commutator terms. No
inverse of a singular q-shift difference is used. On a supplied rank-k
matrix, T has paid soft(kB) Cauchy actions, with known q-adjacencies handled
by regular parts. The matrix [S,Y]Q in the remaining term is not supplied
with such a short generator. Fast ordinary actions do not pay its entrywise
transform. Reciprocal kernels also cancel for a diagonal middle matrix,
but retaining the actual middle S leaves an explicit commutator contraction.
The corresponding adjoint attempt retains a residual trace. Neither is
silently erased, and neither has yet been evaluated at the desired cost.

The executed split-pair norm keeps the product JL unchanged; extending the
old coefficient-block circuit to the J-dimensional quotient costs
soft(sqrt L+J(B+L/B)+J), hence soft(J sqrt L) at its best split. These are
costs of those implementations, not general lower bounds. A bounded primary
interval-DLP search found no transferable deterministic improvement; its
unknown-order theorem uses global equality and the actual global order,
while the inspected subexponential field algorithm is randomized and needs
the supplied prime. No new coverage family, example campaign or backend
was substituted for the original query.

Detailed finite-ring derivations and independent reviews are in
`/tmp/semiprime-forcing-acceleration-20261023/`, particularly
`constant-power-correction.md` and `joint-hadamard-recurrence.md`.
The fresh common-moment construction is `fresh-boundary-algorithm.md`.
The next constructive target remains a joint evaluator for the initialized
boundary forcing or its equivalent one-shot native remainder, with complete
input acquisition and bit costs. Neither the fast core nor fewer symbolic
correction terms should be presented as achieving that target.
