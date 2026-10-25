
## Acquired fixed-power core; coupled correction still open, 2026-10-23

New finite-ring auxiliary operation: C=multiplication by X mod monic F,
D=diag(q^i), M=(I-C)D. For k<=J, M^k e0=P_k(C)e0. Expanding
F=sum nu_k P_k in the q-Newton basis gives ACTUAL charM=kappa_J sum nu_k T^k.
Both basis conversions are softJ finite Toeplitz convolutions: Q_i=(q;q)_i,
forward kernel1/Q_n, inverse kappa_n/Q_n, with all Q_<=J certified units.
Thus M^L on supplied vectors costs soft(J logL), without collision inverses.
This is a fast auxiliary core, NOT the original R_L once L>J.

Exact initialized correction: w_i=f_i(q^J-q^i),u=(I-C)w,v=e_(J-1),
R0=e0,s0=0; R'=MR-s; s'=(I-q^(n+1)C)s-q^n*u*(v^tR).
Its direct cost is JL. R_L=M^L e0-sum M^(L-1-n)s_n still needs joint forcing.
The shear eta=s-(M-I+q^nC)R gives R'=(I-q^nC)R-eta,eta'=Meta,eta0=0;
this tested gauge restores the original product, not a cheap correction.

Fresh common-moment state: in paid q-grid gauge C=diag(q^-r)+alpha beta^t,
tau_n=beta^t y_n has startup0 through J-2, then1. H_s(n)=sum_(k<n)
q^((s+1)k)tau_k/(q;q)_k decodes ALL y_L via one scaled q-binomial
convolution plus adjacent factorials in soft(J+sqrtL). H_s(J) is explicit
and nonzero. Acquiring H(L) from its coupled rank-one feedback is still
unpaid; geometric MPE on unknown tau coefficients does not initialize it.

Dyadic masks telescope jointly: T(S E_B)=S T(E_B)+q^-B[S,Z]Q
-q^-B T([S,Y]Q), T(E_B)=q^(1-B)E1. No exponential symbolic correction tree
is needed. Supplied rank-k masks have paid Cauchy actions, but the product
contraction remains unpaid. Reciprocal cancellation with diagonal middle
does not erase the actual middle S or the adjoint residual.

Details/reviews/validation: /tmp/semiprime-forcing-acceleration-20261023 and
latest journal. Whole-query bound unchanged at soft m^1.5; sixth-rate goal
and executable/Lean integration remain open. Pursue a jointly initialized
boundary evaluator, not repeated block actions, supplied forcing vectors,
uncovered cheap families or finite examples. Preserve all prior prefixes
and all270 frozen entries. No new backend or factoring-rate claim.
