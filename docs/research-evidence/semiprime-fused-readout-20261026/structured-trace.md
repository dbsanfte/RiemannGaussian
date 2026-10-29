# Execute Cauchy diagonalization, a dual Sylvester trace, and finite kernel cancellation

26 October 2026. Paper-only direct scalar attempt from the frozen [direct-contraction packet](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-direct-contraction-20261026/README.md). No repository edits, tests, numerical campaign, implementation or Lean.

**Result.** There is an explicit soft-B change of basis that diagonalizes the actual triangular displacement operator: no generic eigenvector algorithm is needed. It turns the coefficient matrix into a Cauchy matrix with certified unit denominators. A dual Sylvester equation and a linked-displacement trace algorithm are then executed below. Their current exact completion costs soft(J(B+M)) or a full coefficient stream, not target cost. The finite Christoffel–Darboux-type cancellation works, but produces the original q-shift relation on a shifted row alphabet, not an endpoint value or a new scalar equation. No full-query speedup or general lower bound follows.

## 1. Actual finite matrix and optional aspect ratio

Initially use h=2K²+1, B=K, M=2K, A=rho^h, rho=q^-1 and

    C_(s,e)=a_(Bs+e),    0<=s<M, 0<=e<B,
    a_(t+1)/a_t=(A-rho^t)/(1-rho^(t+1)).

The two final coefficients h-1,h are retained separately. More generally h=BM+r, 0<=r<B, gives r+1 tails starting at BM. The supplied native short-unit range contains all exponents through h and the chosen B-1. All formulas below retain that actual endpoint. For the weighted-family clock one can choose B near sqrt(h); nothing requires h=2K²+1.

The frozen kernel construction acquires all coefficient-block starts, C and C^t actions in soft(B+M), and the full tail in soft(J+B+M). For general h this uses factorial block evaluations at the two residue offsets 0 and r; shifted rational-recurrence functional extension supplies the tail b-values. This generalization is a paid-input extension, not a new trace evaluator.

Let S be the lower shift, Q=diag(rho^e), Z=diag(Z_s), Z_s=rho^(Bs), and

    R=(rho S-I)Q, L=S-AI, T=L R^-1,
    v^t=e_last^t R^-1,
    d_s=-(1-rho^(B(s+1)))*a_(B(s+1)).

The already proved finite displacement is

    C T-Z C=d v^t.                                (1)

The last a_(BM) is the first retained tail. Neither its sign nor this boundary is omitted.

## 2. Explicit Toeplitz Cauchy diagonalization, fully paid

Define coefficients

    s_0=1,
    s_r=A^-r*(A*rho;rho)_r/(rho;rho)_r, 1<=r<B,

and the lower triangular Toeplitz matrix V with V_(e,k)=s_(e-k) for e>=k. Put P=R V. Then

    T P=P diag(eta_k),       eta_k=A*rho^-k.       (2)

Direct proof: the kth column of V vanishes before k and has successive nonzero entries s_r. The generalized eigenvector equation L V=R V diag(eta) reduces for r>=1 to

    s_r/s_(r-1)=(1-A*rho^r)/(A*(1-rho^r)),

which is exactly the supplied recurrence. No spectral genericity is invoked.

All denominator factors 1-rho^r are certified units. V has diagonal one; its inverse is ordinary constant-one series inversion. R and R^-1 are bidiagonal solve operators with unit diagonal. Thus P,P^-1 and their transposes are acquired/applied in soft B over the actual composite algebra. Some numerator s_r could vanish outside the preferred native size range; that would not invalidate V's unit diagonal or the argument.

Multiplying (1) by P gives the exact Cauchy representation

    (C P)_(s,k)=d_s*w_k/(eta_k-Z_s),
    w_k=s_(B-1-k).                                (3)

Indeed v^t P=e_last^t V. Every cross difference is a certified unit: its exponent h-k-Bs ranges from r+1 to h in the general h=BM+r case. The diagonal eta differences use only exponents <B. Thus no collision factor or arbitrary field pivot is inverted. This is a genuinely acquired Cauchy representation, stronger than merely naming a possible diagonalization.

## 3. Transform the ACTUAL moment right-hand side

On the paid native separated branch write

    b_t=sum_j lambda_j y_j^t,
    H_(e,s)=b_(Bs+e)=sum_j lambda_j y_j^e U_j^s,
    U_j=y_j^B.

The lambda_j are acquired from the supplied quotient functional and F in soft J, with the actual derivative-unit guards. If lambda_j are instead directly supplied row weights (for example 1 or w_j), the formulas below apply to repeated roots without this interpolation step or any F-prime inverse. This extension covers linear weighted polynomial sums; it does not acquire the nonlinear hit residues of the pure weighted bank. The desired full-block scalar is tr(C H). No uniqueness of powered roots is needed for forward power-sum actions here; the native pure-K graph/separation remains available when needed.

For u(y)=(1,y,...,y^(B-1))^t define Psi(y)=P^-1 u(y). Its entire coefficient-side description is explicit. If S0(z)=sum_(r<B)s_r z^r, then

    sum_(k<B) Psi_k(y)z^k
      = -1/[S0(z)*(1-z)*(1-y*z/rho)] mod z^B.      (4)

This follows by the actual bidiagonal solve R^-1 u(y), whose eth entry is -sum_(t=0)^e(y/rho)^t, followed by Toeplitz convolution V^-1. Coefficients of [S0(z)(1-z)]^-1 cost soft B; (4) needs no y-dependent inverse.

For clarity the short multiplier in (4) agrees, through degree B-1, with

    product_(r=1)^h(1-rho^(-r) z).

This finite formal identity follows by comparing its q-shift relation and the unit coefficient recurrence; no infinite product or analytic q-limit is imported. Its short coefficients are already acquired from S0, not by expanding h factors.

## 4. Execute the dual Sylvester trace algorithm

The natural dual equation is

    T Y-Y Z=H.                                    (5)

It is uniquely solvable: all eta_k-Z_s are certified units. Cyclicity of the finite rectangular trace and (1) give exactly

    tr(C H)=v^t Y d.                              (6)

After setting Ytilde=P^-1Y, equation (5) is entrywise

    Ytilde_(k,s)=sum_j lambda_j Psi_k(y_j) U_j^s
                   /(eta_k-Z_s).

Therefore the requested trace is

    sum_(j,k,s) lambda_j*w_k*d_s*Psi_k(y_j)*U_j^s
                         /(eta_k-Z_s).           (7)

This is the actual transformed RHS; no fictitious low-rank or constant right-hand side is substituted.

**Fully initialized execution:** for each j, acquire the B coefficients Psi_k(y_j) from (4), multiply by w_k, construct its Cauchy rational sum over the common eta_k, and evaluate at all Z_s using product trees/MPE. Pair with d_s U_j^s, multiply by lambda_j and sum. Each j costs soft(B+M); the exact tails were already paid. Total

    soft O(J*(B+M)+J+B+M).                        (8)

The same bound follows by solving the rank-J RHS in (5) columnwise in its known root decomposition. For B about sqrt h this is soft J sqrt h; for the monic scale it is K². This is worse than the old shared product engine. It is a lawful Cauchy/Sylvester completion, not a hypothetical oracle.

## 5. Try the source's fast structured-product trace formula directly

Primary indexed-text reading (not a retained full-PDF download): Olshevsky–Oseledets–Tyrtyshnikov, [*Superfast inversion of two-level Toeplitz matrices using Newton iteration and tensor-displacement structure*](https://www2.math.uconn.edu/~olshevsky/papers/tyrtyshnikovIWOTA2005.pdf), 2007 author manuscript, §3.3, Lemma 3.1. It computes a matrix Frobenius product by obtaining the linked product's displacement generators and then a generator trace formula. The primary search excerpt exposed this section and lemma; the metadata/early text were opened, but a later full-PDF retrieval timed out. Its approximate low-tensor-rank inversion and numerical recompression are not transferred to this exact finite ring. The exact generator identity requires its actual supplied linked generators; it does not infer them from a single factor's fast action.

Here is an exact ring-safe execution of that strategy. Choose sigma=rho^B, so 1-sigma is a certified unit. Let Z'=sigma Z and

    E=T H-H Z'.

Write H=U Lambda W^t, where U_(e,j)=y_j^e and W_(s,j)=U_j^s. An explicit linked generator is

    E=[T U Lambda, -U Lambda] * [W^t; W^t Z'],     (9)

of width at most 2J. This is a decomposition, not a claim that its minimal rank is 2J or large on the native input. Acquiring its columns or applying C to them costs soft J(B+M). The product displacement is

    Z*(C H)-(C H)*Z'=C E-d*(v^t H).               (10)

Every diagonal entry of C H can now be read from (10) by division by Z_s(1-sigma), a known unit. The rank-one term uses one H^t action and is soft(B+M+J); the first term uses the linked generator (9), with the bill above. The source's trace formula is therefore executable, but this instantiation gives (8), not a nearlinear scalar.

Trying to eliminate E algebraically is a tautology: insert E=T H-sigma H Z and use C T=Z C+d v^t; its diagonal is exactly (1-sigma)Z_s(C H)_(s,s) plus the same rank-one term. No new scalar equation remains after cancelling that term. A cheaper **special** linked-generator recompression or direct evaluation of the paired generator contractions could still work. Neither a low-rank lower bound nor a black-box trace lower bound is asserted here.

## 6. Execute the finite Christoffel–Darboux-type cancellation

For a single coefficient row define

    R_s(y)=sum_(e<B) a_(Bs+e)y^e, alpha_s=a_(Bs).

Its coefficient ratio gives the exact finite two-argument kernel identity

    (1-Ay)R_s(y)-Z_s(1-y)R_s(rho*y)
       =alpha_s*(1-Z_s)+d_s*y^B.                 (11)

This is derived by shifting the finite e-sum; the last coefficient d_s is retained. Multiply by y^(Bs), sum over s and use Z_s=rho^(Bs). The RHS telescopes to

    -(1-rho^(BM))*a_(BM)*y^(BM).

Adding all r+1 actual tail terms yields precisely

    (1-Ay)G_h(y)=(1-y)G_h(rho*y).                 (12)

Thus a genuine kernel cancellation occurs, but it supplies G_h on a SHIFTED row alphabet rather than a value determined at short endpoints. Summing (12) with lambda_j similarly couples the sought weighted readout to a weighted readout on rho*y_j. The current good-family one-step separation makes that shifted alphabet disjoint from the original rows; no known permutation of the supplied values closes this trace. This does not preclude another finite recurrence or an algorithm acquiring both simultaneously. It shows exactly what this executed kernel cancellation produces.

At a collision, dividing by the factors of (12) without classifying them would discard the event. All identities (1)–(12) were kept polynomial or used only the explicit certified Cauchy/unit factors, so no such division is part of the completed algorithm.

## 7. Aspect ratio and target scope

For arbitrary native h=BM+r the start/tail cost is soft(J+B+M), the explicit diagonalization is soft B, and completion (8) is minimized at B about sqrt h. A full coefficient-stream dot product also costs soft(h+J); neither beats soft(J+sqrt(Jh)) in the regime h>J. For the shorter weighted horizon h~K^(3/2), merely changing aspect ratio therefore supplies no new exponent. A new rank-width or correlated-generator contraction is required; it is not ruled out by this cost ledger.

This investigation concerns an exact linear quotient pairing. A uniform linear-circuit nearlinear algorithm for it would transpose to acquire the full remainder, as previously proved. It does not follow that a direct nonlinear weak norm pair must acquire that remainder. The original selected norm/first-jet target and its valid HH decoder remain open.

**Next precise operation:** exploit the special transformed moment RHS in (7), or compress/evaluate its linked generator (9) jointly, without expanding its J root components. The explicit Cauchy eigenbasis and all finite boundary data are now paid inputs for that effort. No cheaper matched trace, directional norm pair or all-semiprime sixth-rate algorithm is claimed in this report.
