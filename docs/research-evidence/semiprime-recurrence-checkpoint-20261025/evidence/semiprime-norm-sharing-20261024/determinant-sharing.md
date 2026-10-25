# Formal-unit determinant condensation and the fused norm homotopy

24 October 2026. Scratch only. This executes an all-pivot regularization of the actual resultant batch and follows its rank-one companion perturbation through the determinant lemma. The whole batch fuses into one explicitly normalized homotopy polynomial. Its first polylogarithmically many coefficients are genuinely acquired in soft k. Its value at one, however, is still the covered long query. The completed joint acquisition below costs soft k², and the retained blocked query remains soft k^(3/2). No formal-unit pivot is evaluated as an inverse at a covered zero.

## Input, primary check and duplicate boundary

Use `/tmp/semiprime-native-terminal-20261024/composed-terminal.md`, SHA256 `6ad4b2e3206dec95673013b34f9a0ee52d77f134b89af9f21bd450902ad264e8`, and its exact initialized norm batch. Select the canonical one-representative-per-tag family of degree J0<=k, retaining original labels. After optional reciprocal augmentation the actual monic F has degree J<=2J0<=2k. All root values and their native/reciprocal flags are acquired units in the constant-rank quadratic ring B. Actual beta,W roughening and the q screen through C=16H are paid. Here H=k², main length L0=2H, m=k, G=2k, Q=q^m, t_i=q^(-i), 0<=i<m. The two ORIGINAL tail factors are acquired separately. The 3H main variant has G=3k and the corresponding same-margin tail construction; the formulas below use L0=mG.

Acquire Gamma_G(Z)=prod_(g<G)(Z-Q^g)=sum gamma_d Z^d, cost soft G. For each supplied unit t,

    H_t(X)=X^G Gamma_G(t/X)=sum_(l=0)^G h_l(t)X^l,
    h_l(t)=gamma_(G-l)t^(G-l), h_0=t^G,
    R(t)=Res_X(F,H_t).                               (1)

The monic-normalized resultant and every original row/index phase are those proved in the source. Auxiliary scalar pivots have only the B factor/unit/global-zero classifier; they do not inherit an original collision decoder.

Duplicate check: christoffel-terminal.md SHA256 `c523fc8a1a7a23d667f32714e1671c6eb782b52d423984681402eb8deea01008` already identifies the unpaid full-support determinant. terminal-toda.md SHA256 `937018c6ee61730a90df1ee9f05bea37cd1bc0a9d2a4addbb3701ec670aa0e3c` already executes q-contiguous determinant transport and its missing amplitude. Neither is counted as a solution here. The new tested normalization is a rank-one companion homotopy, not another endpoint ratio.

Primary integrable-system check: Maeda–Tsujimoto, [Direct Connection between the RII Chain and the Nonautonomous Discrete Modified KdV Lattice](https://sigma-journal.com/2013/073/sigma13-073.pdf), Section 2, expresses nonautonomous Toda variables using moment dispersion and ratios of neighboring Hankel determinants. Those identities require compatible moments and legal denominator values; they do not assert a fast implicit norm batch. All condensation used below is proved directly over the actual finite ring rather than importing those ratios at singular pivots.

## 1. All principal pivots become ACTUAL formal units

Write F(X)=X^J+sum_(r<J) f_r X^r and set

    F_e(X)=X^J+e(F(X)-X^J),
    C_e=C_0+e u e_(J-1)^t,
    u=-(f_0,...,f_(J-1))^t.                        (2)

Here C_0 is the lower nilpotent shift, and C_e is the ACTUAL multiplication-by-X matrix in B[e][X]/F_e, in basis 1,X,...,X^(J-1). This free algebra and polynomial matrix require no etaleness or hidden diagonalization. Let

    M_e(t)=H_t(C_e), Delta(e,t)=det M_e(t).

The determinant is the resultant Res(F_e,H_t). At e=0, M_0(t)=H_t(C_0) is lower triangular Toeplitz, with diagonal d=t^G, a known unit. Therefore its leading r-by-r principal determinant has constant coefficient d^r for every r. Every corresponding principal Gaussian/Schur pivot is a unit in B[[e]] with constant d; the leading minors and fraction-free Bareiss pivots instead have the corresponding powers d^r as constants. All are known units. This statement is about principal pivots, NOT about arbitrary off-diagonal minors.

It initializes legitimate Schur condensation at every order:

    M^(r+1)_(a,b)=M^(r)_(a,b)
       -M^(r)_(a,r) [M^(r)_(r,r)]^(-1) M^(r)_(r,b).

Formal inverse acquisition uses the actual unit constant and finite series multiplication. No leading-principal unit is assumed from a generic rank profile. Nonunit coefficients of positive e powers remain unchanged; they are not classified as original hits.

### Execute the first mixed Schur numerator

Take J>=2; bounded smaller dimensions are direct. Write M_e=M_0+e M_1+O(e²), and set h_l=0 outside 0<=l<=G. Differentiating H_t(C_e) in its rank-one perturbation gives the initialized formula

    (M_1)_(r,s)=sum_(a=0)^r h_(J-s+a) u_(r-a).

This is a short convolution identity, obtained by inserting u e_(J-1)^t once among the powers of C_0. In particular

    M_1[0,0]=h_J u_0,
    M_1[0,1]=h_(J-1)u_0,
    M_1[1,0]=h_J u_1+h_(J+1)u_0,
    M_1[1,1]=h_(J-1)u_1+h_Ju_0.

The ACTUAL two-by-two numerator is

    det M_e[0:2,0:2]
      =d²+e{d[2h_Ju_0+h_(J-1)u_1]
                              -h_1 h_(J-1)u_0}+O(e²). (3)

The off-diagonal mixed term is retained. No native or q-binomial identity is assumed to erase it. All displayed coefficients at every t_i are acquired in soft(J+G+m): the h_l(t_i) are known gamma coefficients times explicit geometric powers. The first actual Schur pivot is this numerator divided by M_e[0,0], a formal unit. Thus this is an initialized nontrivial condensation step, not merely an existence statement for regular pivots.

## 2. Rank-one determinant lemma: fuse the ENTIRE batch exactly

The base matrix tI-Q^g C_0 has the acquired finite Toeplitz inverse

    (tI-Q^g C_0)^(-1)
       =t^(-1) sum_(s=0)^(J-1)(Q^g/t)^s C_0^s.

Its determinant is t^J. Applying the rank-one determinant lemma to C_e, with this actual inverse, yields

    det(tI-Q^g C_e)=t^J[1+e P(Q^g/t)],
    P(Z)=sum_(d=1)^J f_(J-d) Z^d.                  (4)

There are no denominators except powers of the supplied unit t. P is acquired in soft J and satisfies 1+P(Z)=Z^J F(1/Z). Its degree is J because f_0 is a unit.

Since H_t(C_e)=prod_(g<G)(tI-Q^g C_e), determinant multiplicativity gives

    Delta(e,t)=prod_(g<G)[t^J+e d_g(t)],
    d_g(t)=Q^(gJ)F(tQ^(-g))-t^J.                    (5)

This proves degree_e Delta<=G and its constant t^(JG), without expanding a Sylvester or multiplication matrix. It also executes a different way to evaluate all regularized determinants, including all zero branches, as follows.

Acquire F(t_i Q^(-g)) at all mG ACTUAL points by one monic MPE; cost soft(J+mG). Acquire all powers/scalings in (5) explicitly. For every i multiply its G linear e factors by a product tree, cost soft G. Thus ALL m actual degree-at-most-G polynomials Delta(e,t_i) are acquired in soft(J+mG)=soft k², including normalizations and outputs. Evaluating their polynomial representatives at e=1 is now lawful and gives the whole resultant batch. No auxiliary polynomial inverse is evaluated at one.

A literal dense condensation instead pays for the M_e entries and their series: a conservative bound is soft m*G*(J+G+J³), using monic reduction, the multiplication matrix, and dense principal elimination over B[e]/e^(G+1). This is much worse. The factorized joint completion above avoids that dense array, but still emits mG coefficient slots. Neither cost is disguised as soft k.

Most importantly, (4) fuses the whole matched batch. With

    U_t=prod_(i<m)t_i^(JG)=q^(-JG*m(m-1)/2),
    Xi(e)=U_t^(-1) prod_(i<m) Delta(e,t_i),

we have the EXACT acquired-input formula

    Xi(e)=prod_(n=0)^(L0-1)[1+e P(q^n)].            (6)

The pairs n=mg+i partition the actual main interval. This contraction retains all labels. No ordinary determinant of unmatched paired values replaces it.

For the unaugmented original family put U_V=prod_j V_j^L0, an acquired unit. Its original main product is E_main=U_V Xi(1). The full product is E_main times the separately acquired original tail product. For reciprocal augmentation, put a0=q^(1-L0), c0=(-1)^L0 q^(L0(L0-1)/2), and retain J0 native roots. Then

    E_main²=c0^J0 U_V Xi_aug(1).                    (7)

This follows from Pochhammer reciprocity P_L0(a0/y)=c0^(-1)y^(-L0)P_L0(y). Multiply the ACTUAL original tail squared to obtain the full-query square. All phases in (7) are units acquired by products and binary powering; no square root or output inverse is requested. Main reciprocal leaves map n to L0-1-n; the two original tail indices retain their separate labels.

## 3. Execute shared first-s coefficients, and test power projection

Set S_r=sum_(n<L0) P(q^n)^r. Formal logarithms give the finite identity

    log Xi(e)=sum_(r>=1)(-1)^(r-1)S_r e^r/r.        (8)

For a requested s with Js<=C and s<P,Q, acquire P^r for 1<=r<=s by repeated polynomial multiplication. Its degree is Jr. Acquire the actual geometric moment weights

    Lambda_0=L0,
    Lambda_d=S_L0(q^d)=(1-q^(L0*d))/(1-q^d), d>=1,

for d<=Js, using only the already guarded denominators. Numerator powers need no new order promise. Pair each acquired coefficient vector of P^r with those weights to obtain S_r. Exponentiating (8) through s then gives all first-s coefficients of Xi. This is an initialized joint scalar contraction, not per-node Taylor sampling.

Its work is soft(J s²+s²), with all powers, weights and unit integer divisions paid. Therefore any fixed or polylogarithmic s gives soft k work. In particular the nontrivial first two global coefficients are

    [e]Xi=S_1,
    [e²]Xi=(S_1²-S_2)/2,
    S_1=sum_d P_d Lambda_d,
    S_2=sum_d [P²]_d Lambda_d.                      (9)

At s=Theta(k), the literal repeated-powers procedure is not soft k; it costs up to soft k³. This is a ledger, not a lower bound on first-s projection.

The precise transposed-composition attempt uses the algebra B[Z]/Z^(Js+1), supplied inner polynomial P, and functional L(Z^d)=Lambda_d. Since deg P^r<=Js, no power alias occurs for r<=s. A standard modular power projection returns these S_r after its full coefficient functional has been acquired. Its explicit functional vector has Js+1 entries, not s entries. Kedlaya–Umans Theorem 7.7 (primary copy in the preceding packet) is valid over the stipulated monic finite-ring extensions subject to its interpolation-point supply, but operates on that explicitly sized input and does not provide implicit rational-weight projection in soft(J+s). Even granting its additional points, s=Theta(k) has an explicitly acquired Theta(k²) functional in this invocation. We do not assert that a new algorithm must use that array.

The special weights satisfy a genuine short q-difference identity:

    L(f(Z)-f(qZ))=f(1)-f(q^L0).

For f=P^r this identity alone does not evaluate L(P^r); computing its polynomial q-antidifference divides each of the Jr coefficients by 1-q^d. That executes the previous explicit polynomial procedure, not a short recurrence in r. No common small recurrence for P^r or its antiderivative is inferred merely from the acquired native F. The exact open improvement is a short-output power projection accepting THIS implicit geometric-weight functional and actual P, or an equally initialized nonlinear terminal contraction. No such soft-k implementation was obtained here.

## 4. Why few local collisions do not finish this homotopy

Over every local field component, q^n for n<L0 are distinct by the ACTUAL q screen. Since 1+P has degree J, the multiplicity of e=1 as a root of Xi is at most J: each seed with P(q^n)=-1 contributes one linear factor. This includes the unknown nonsplit own side, but it supplies neither its actual multiplicity nor a local field oracle.

The same source data show the homotopy is not secretly degree J. P itself has degree J with unit leading coefficient, so P(q^n)=0 at at most J of those seeds. Thus over each component

    degree_e Xi >= L0-J.

This is an exact degree statement about this PARTICULAR polynomial homotopy, not an operation lower bound. Few zeros at e=1 do not supply its value or derivatives there from a short jet at e=0. A logarithmic derivative centered at e=1 would divide by the very factors 1+P(q^n) that vanish at the covered collision; no such inverse is used. The remaining nonhit linear factors are not discarded from (8).

For one Delta(e,t), precision G+1 suffices to recover its actual polynomial by (5), then evaluate at one. A bounded shorter precision does not provide that evaluation in this implementation. For the fused Xi the corresponding safe polynomial precision is L0+1. The substitution e->1 is NOT a ring homomorphism from B[e]/e^r: e is nilpotent there, while 1 is not. Formal pivot inverses cannot simply be numerically specialized after dropping their tails. No generic lower bound on a different scalar-only evaluation follows.

## Cost and zero-safe outcome

| Executed object | Paid cost | What is actually supplied |
|---|---:|---|
| F, Gamma_G, homotopy and Toeplitz base inverse circuit | soft(J+G+m) | actual short coefficients, not all matrix entries |
| First mixed Schur coefficient at all t_i | soft k | cross term (3) retained |
| Formal principal pivots at every size | unit proof; coefficients cost extra | actual constants t^G, no singular-target inversions |
| Full joint Delta polynomial array via (5) | soft(J+mG)=soft k² | all per-node e coefficients and exact values at one |
| First-s fused Xi coefficients | soft(J s²+s²) | all starts/weights paid; polylog s gives soft k |
| Explicit standard power-projection functional | Theta(Js) entries | no implicit-weight acceleration assumed |
| Original optimized whole query | soft k^(3/2) | retained better complete algorithm |

All completed nonunit norms are localized to actual original row/index factors before the nonsplit/G_beta consumer. B's factor/unit/global-zero classifier handles arbitrary scalar pivots without assigning them that consumer; formal e coefficients receive no original witness interpretation. The regularization, rank-one cancellation and fused first-s contraction are concrete initialized results, but neither removes the long nonlinear norm. No whole-query exponent gain, finite experiment campaign, shared-file edit or generic determinant/recurrence impossibility is claimed.
