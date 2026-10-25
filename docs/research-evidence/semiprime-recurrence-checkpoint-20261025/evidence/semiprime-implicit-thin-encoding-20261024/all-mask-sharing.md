# Shared Gaussian-binomial matrix action and joint inner masks

24 October 2026. Separate scratch research. Positive results: the reshaped q-Pochhammer coefficient matrix has an actually initialized softly linear matrix-vector AND transposed action; all active inner left masks for ONE supplied outer row combination can then be acquired jointly. A fixed-Q summand including its outer digit box also has a soft-sqrt-b evaluation by a balanced mixed-radix cut. These are input primitives, not a completed terminal-product algorithm. In particular a balanced cut used here is not automatically the thin dimension in the primary matrix theorem.

## Inputs and pins

Use `digit-mask-attempt.md`, SHA256 `300952af3de79e56b9c90d4fe02c756e640273a3e2db444010c0c79d7cb07400`, with independent review SHA256 `6181de9f3141f6fb707cc932b724c5db7fe3307c420a4fa5a770aa67ecb9b40e`. Its fully initialized prefix lemma acquires T requested q-factorial prefixes through b in soft(sqrt b+T), over the actual ring. Its short-unit hypotheses and bit-length charges are retained here.

The exact tensor/outer-band form is in `working.md`, final SHA256 `84c8f8036a33637d6c05dc9e444c75f29ee98b4efe68f18d4d3b55b09d3b5435`, with independent review SHA256 `bd3f762d6b87eeed820c4e03c7411a40401b5f2cf24e301941d3ef2029fcf934`. Primary tensor source: [Alman--Vassilevska Williams, arXiv:2610.06783v1](https://arxiv.org/abs/2610.06783), Sections2.2--2.4. Only its actual masks and layout are used in the new proofs below, not a presumed compressed-input matrix theorem.

Let A be R=Z/N or its acquired constant-rank quadratic algebra. All ring constants have their actual O(log N)-bit representations. The supplied q is a unit and every 1-q^s for1<=s<=b is an ACTUALLY certified unit. Native b and tensor metadata are polynomially bounded in N. Put

    P_b(X)=product_(i=0)^(b-1)(1-q^i X)=sum_(n=0)^b c_n X^n,
    f(n)=product_(s=1)^n(1-q^s), f(0)=1.

The exact coefficient identities are

    c_n=(-1)^n q^[n(n-1)/2] f(b)/(f(n)f(b-n)),
    (1-q^(n+1))*c_(n+1)=(q^b-q^n)*c_n.             (1)

The first identity uses only certified unit denominators; the second is a cleared polynomial identity. No input weight, coefficient value, output or x parameter is inverted.

## 1. Dense reshaping: a complete nearlinear action

Choose ANY integer1<=D<=b+1 and set H=ceil((b+1)/D). The ACTUAL padded coefficient matrix is

    C[rho,r]=c_(D*rho+r), 0<=rho<H, 0<=r<D,

where entries beyond b are zero. The theorem is

    C*v and C^t*u are acquired in soft(sqrt b+H+D)   (2)

for arbitrary supplied vectors v in A^D and u in A^H, including all preprocessing. Since HD>=b+1, H+D>=2sqrt(b+1), this is also soft(H+D). The explicit data have size O(H+D), so in the balanced H,D=O(sqrt b) regime no degree-b coefficient array is acquired; extreme widths such as D=1 can acquire that array at their charged O(H+D) cost. All outputs of these actions are included; this is not merely an oracle for one selected entry.

Here is the initialized forward algorithm. For a FULL row set U_rho=q^(D*rho), gamma_rho=c_(D*rho), and define the fixed degree-one transition polynomials

    a_h(U)=q^b-q^h U,
    b_h(U)=1-q^(h+1)U, 0<=h<D-1.

Repeated use of (1), or clearing the unit denominators, gives

    (C*v)_rho=gamma_rho F_v(U_rho),
    F_v(U)=sum_(r=0)^(D-1) v_r product_(0<=h<r) a_h(U)/b_h(U).   (3)

The denominators at a full row are products of 1-q^(D*rho+h+1), whose indices are at most D*rho+D-1<=b. This checks their ACTUAL ranges, not an extended guard for padded coefficients.

### Build the rational Newton form, with no unused last transition

Acquire a balanced product tree with D leaves. For0<=h<D-1 use the leaf triple

    (P_h,Q_h,S_h)=(a_h,b_h,v_h*b_h).

The FINAL leaf is the dummy transition

    (P_(D-1),Q_(D-1),S_(D-1))=(1,1,v_(D-1)).

Merge two consecutive segments by

    P=P_left P_right, Q=Q_left Q_right,
    S=S_left Q_right+P_left S_right.               (4)

Then F_v=S/Q. Induction on the two segments proves (3): the right segment is multiplied by the left transition product. The final dummy leaf ensures Q=product_(h=0)^(D-2)b_h, NOT a product containing an unneeded denominator at index D*rho+D. Degrees of P,Q,S are at most D-1. Every P/Q subtree is independent of v, and all its coefficient vectors cost soft D. The S tree is linear in v and costs soft D by polynomial multiplication. No q-binomial digit factorization is assumed.

Acquire all full-row starts U_rho by a power walk. Monic MPE evaluates S and Q at their actual H_full starts in soft(D+H). All Q values are certified units by the index bound above; acquire their inverses by explicit scalar/fixed-rank unit arithmetic. Acquire all gamma_rho by the prefix lemma applied to the coefficient identity (1); this costs soft(sqrt b+H), including q phases and every row-start prefix. Multiply gamma_rho*S(U_rho)/Q(U_rho) to return every full-row output.

If the last row is partial, with d=(b+1) modD in{1,...,D-1}, acquire its d ACTUAL coefficients by that same prefix lemma and take its literal dot product with v_0,...,v_(d-1). This costs soft(sqrt b+D), shared with the row-start requests. No transition or denominator beyond b is used. The D=1 case is the same construction with dummy leaf only. Bounded b uses direct arithmetic.

This proves (2), including all row starts, the last partial row and inverses. The output is valid if v has zero or nonunit entries. All nonlinear preprocessing depends only on q,b,D, never on v.

### Executable transposition

After preprocessing, the S tree uses additions and polynomial multiplications by FIXED P/Q factors. Monic MPE is a linear map with fixed node product/remainder trees; its division uses fixed monic reciprocal constants. Final row multipliers gamma_rho/Q(U_rho) are fixed acquired constants. The explicit partial-row dot product is linear too.

Reverse this linear arithmetic circuit: initialize its H output adjoints with u, reverse each addition by accumulation, and reverse multiplication by a fixed scalar or fixed polynomial by its actual transposed scalar/convolution map. Transposed fixed polynomial products/remainders are acquired by reversal and middle-product operations with the same soft degree cost. Thus every reversed operation works over A, with no division by a component of u or v and no hidden field. The partial row contributes the direct updates vbar_r+=u_partial*c_(D*H_full+r),0<=r<d.

The resulting D adjoints are EXACTLY C^t*u. Preprocessing and inverses are reused, not reversed or called free. This proves the transposed claim in (2) at the same cost, even with zero outputs or repeated spectral values.

A weighted matrix C_x[rho,r]=c_(D*rho+r)*x^(D*rho+r) is handled by explicit diagonal factors:

    C_x=diag(x^(D*rho))*C*diag(x^r).

Their powers and action cost O(H+D) after binary acquisition of x^D; x need not be a unit. The SAME preprocessed C works for every x, but each new pair of moving input/output vectors must still be charged.

## 2. The exact displacement equation, with its boundary acquired

The transition in (1) also supplies an actual pencil identity. Let S be the D-by-D lower shift with S_(r+1,r)=1, V=diag(q^r), and U=diag(q^(D*rho)). Then the padded coefficient matrix satisfies

    C*(S-q^b I)-U*C*((qS-I)V)=g*e_(D-1)^t,
    g_rho=C[rho,D-1]*(q^(D*rho+D-1)-q^b).          (5)

Every interior column is exactly (1); the last column is the stated boundary. Coefficients beyond b are zero, so the cleared identity also covers a padded last row without an inverse at a nonexistent index. The boundary coefficients at existing indices are acquired by the prefix lemma in soft(sqrt b+H); padded entries are literally zero. Both sparse pencil matrices and the U/V diagonals are actual data.

Equation (5) is not being used as an uninitialized generic Cauchy solver. The rational Newton construction proves its fast action without any extra spectral-separation assumption. A faster paired-vector contraction from (5) would be an additional algorithm, not a consequence merely of calling its boundary rank one.

## 3. Jointly compute ALL inner left masks for ONE supplied outer combination

Now take D=4^m. The actual nonzero left inner digit map is the explicit6-by-4 matrix

    K*v=(v0,v1,v2,v3,-v0-v2,-v1-v3).

For ONE arbitrary supplied outer row vector u, first acquire a=C^t*u by (2). Apply K at each radix-four digit to a. After s digit transformations the array size is6^s*4^(m-s); the sum of those sizes is O(6^m). Thus this is an actual joint tensor transform computing EVERY active inner left-mask value

    sum_r a_r product_(ell<m) K_(tau_ell,digit_ell(r)),

not6^m separate calls to a one-mask primitive. All4^m singleton forms and all pair-mask forms, zeros included, are returned. The cost is

    soft(sqrt b+H+D+6^m).                          (6)

u is not free: its H actual entries are supplied or generated from its actual outer digit description in soft H. For the balanced regime D~sqrt b, H~sqrt b, the last term is b^[log_4(6)/2], approximately b^0.64625. This is a genuine sub-b acquisition of ALL inner masks for ONE outer combination, including their output writes. It does not assert that the primary thin-matrix theorem's actual D is balanced; at its native D retain the full H=ceil((b+1)/D) term in (6).

For several explicitly supplied outer combinations u_1,...,u_p, reusing preprocessing and performing (6) separately gives soft(sqrt b+p(H+D+6^m)). This is a proved continuation, not a claim that arbitrary compressed outer families cost only p. The primary tensor's active-Q row-block sum changes those outer combinations and assignments; (6) does not silently acquire that whole sum.

## 4. One fixed-Q summand including its full outer digit box

The exact coefficient-side formula in the companion working report is

    Phi_tau=sum_(Q active) sum_(rho<N0) sum_(d<D_tensor)
       c_[D_tensor*(R0+r_Q*N0+rho)+d]
       *outer_weight_(tau,Q)(rho)*inner_weight_(tau,Q)(d),   (7)

with D_tensor=4^m,N0=3^(h-m), and coefficients outside[0,b] padded zero. Both weights are products of actual digit masks: radix four for the m inner digits and radix three for the h-m outer digits. This subsection fixes ONE Q and includes its ENTIRE outer box; it is stronger than just a sparse inner-mask evaluation at one row.

Let B0=D_tensor*N0 and n0=D_tensor*(R0+r_Q*N0). In the actual standard row bands, R0 is a multiple of N0; therefore n0 is a multiple of B0. If n0>b, this whole fixed-Q term is known zero and is skipped.

For b<15 use bounded-b direct evaluation; hence below b>=15, so 4sqrt(b+1)<=b+1 and every chosen balanced cut is an allowed width in Section1. If B0>=sqrt(b+1), choose a digit-boundary cut D0 among

    1,4,...,4^m,4^m*3,...,4^m*3^(h-m)

as the first value at least sqrt(b+1). Consecutive choices differ by at most4, so D0 is between sqrt(b+1) and4sqrt(b+1). It divides B0 and n0. The local mixed-radix weight factors EXACTLY into a lower-digit vector v of length D0 and an upper-digit vector u on the actual global coarse rows. Its upper vector is zero outside this Q's row block and carries the actual integer shift n0/D0. Generate these two vectors by their known digit products, costing soft(D0+H0)=soft sqrt b with H0=ceil((b+1)/D0). The fixed-Q summand of (7) is then exactly u^t*C*v for that balanced coefficient reshaping. Section1 acquires it in soft sqrt b, including all outer digits and clipping by the actual last partial row.

If B0<sqrt(b+1), the fixed-Q block contains fewer than sqrt(b+1) coefficient positions. Enumerate them with their actual weights and use the already proved selected-coefficient prefix lemma; its complete evaluation is again soft sqrt b. The cost to compute digits/exponents is polylogarithmic in the actual tensor dimensions, which are polynomial in native parameters.

Thus ONE fixed-Q summand, not just one inner residue or one outer row, is acquired in soft sqrt b. The actual active-Q sum in (7) remains separate. The source's AP-box bound remains valid; this is an additional sharing method for its fixed-Q term. No change to that frozen report is needed.

## 5. ALL masks and outer combinations: exact counts, not an assumed tiny family

Without outer positions, the full active inner left family has6^m outputs. Its4^m singleton subfamily already gives every input coefficient of a full radix block (weighted by an explicit x power if present). A literal algorithm outputting all those values cannot be counted as a sub-4^m routine; this is the actual output list, not a general lower bound for an aggregate or lazy representation. The joint result (6) gains a sub-b clock because its input coefficient row dimension H is also present; D~sqrt b is smaller than the original degree b.

For the literal full primary construction use its actual nontrivial range m>=1 (m=0 would give equality rather than the strict count below). Set h=19m, A_active=binom(h,m), K0=floor(sqrt(A_active)), N0=3^(h-m),D_tensor=4^m. The unmodified encoding phase forms10^h scalar encodings per band of K0*N0 coefficient rows, including its labelled zeros/repeats. If there are R_rows=ceil((b+1)/D_tensor) coefficient rows, its literal number is

    ceil(R_rows/(K0*N0))*10^h.                      (8)

It exceeds b+1. For example the uniform inequality A_active<=2^h gives K0<=2^(h/2), so for h=19m,

    K0*N0*D_tensor
      <=2^[(19/2)m]*3^(18m)*4^m < 2^(48m) <10^(19m).

Multiply by the actual number of bands to prove the assertion even with the last band padded. This counts the displayed full phase only; it is NOT a theorem that every lazy wanted-leaf union must be large or that repeated/zero encodings cannot be reused.

Fixed-Q evaluation by Section4 yields a valid direct sum cost soft(A_tau*sqrt b+A_description) for one wanted leaf with A_tau active nonzero Q descriptions, with possible real reuse if two descriptions give the same u/v. No identity has yet collapsed that actual grid-assigned sum into one outer vector or a bounded number of fixed-Q bilinear forms. Computing all leaves by their literal phase would still have (8)'s outputs; a requested-subset method must acquire its actual leaf union and outer combinations. Their number is not supplied by the one-Q theorem.

## 6. The precise original terminal contraction still to execute

For a supplied native target y,

    P_b(y)=u(y)^t C v(y),
    u(y)=(1,y^D,...,y^((H-1)D)),
    v(y)=(1,y,...,y^(D-1)),                         (9)

with the last row padded in C. BOTH vectors change when y changes. The preprocessed action of C is real, but separately applying it to K targets and contracting (9) costs soft(sqrt b+K(H+D)). At a balanced cut that is soft(sqrt b+K sqrt b), not soft(H+D+K). The native block product requires the same target's two vectors in every diagonal bilinear form. Replacing that diagonal by all H*K partial values or by two independently summed factors changes the desired output.

Likewise, if a scalar projection is written sum_n c_n u_n for an acquired order-J C-finite u_n, its reshape gives a Hankel-derived weight matrix with a J-term root/recurrence decomposition in the actual input. One fast C action handles ONE supplied rank-one term; it does not make that whole Frobenius pairing cost independent of J. A full-rank or minimal-order lower bound is neither needed nor claimed here.

The concrete next operation is simultaneous DIAGONAL bilinear evaluation for the PAIRED geometric vectors in (9), or a direct product of those diagonal values, preserving original row/interval labels. Whether pencil (5) combines with the two Vandermonde structures to do this in soft(H+D+K) is an open constructive question in this note, not a proved algorithm. The existing block query remains the guaranteed completion.

## 7. General multivariate evaluation does not fill this particular gap automatically

For comparison the primary [Bhargava--Ghosh--Guo--Kumar--Umans, Fast Multivariate Multipoint Evaluation Over All Finite Fields](https://arxiv.org/abs/2205.00342), Theorem5.1 and Section6, DOES give algorithms over Z/N and monic extension rings without factoring. Its explicit first-algorithm cost contains (d^f+K)*Theta(1)^f*poly(f,d,log N) (with homogeneous components handled at polynomial overhead). The nearly-linear large-degree headline explicitly means d=omega(1); it does not certify a soft(t+K) bound at d=2,f=log2 t. The exponential-in-f factor is not then known polylogarithmic. Grouping g consecutive free radix-four digit levels fills a degree about4^g box for only2^g supported terms; that acquisition must also be paid. Thus the valid ring scope is not a substitute for the missing fixed-degree/growing-dimension bound. This comparison is independent of the proved matrix action above.

Cached primary MPE PDF SHA256 `14eddc304a7dd8995ebc1e24171571fd9dc0f1f837ca35a7f9e2e6fb21bfafa8`. No multivariate MPE theorem is used as a correctness or complexity premise of Sections1--6.

## Acquisition ledger and final scope

| Proved object | Cost, usual logarithmic/bit factors suppressed | Output included |
|---|---:|---|
| q-prefix row starts, P/Q Newton blocks, fixed nodes/inverses, partial row | soft(sqrt b+H+D) | actual preprocessed coefficient data |
| C*v or C^t*u | soft(sqrt b+H+D) total | ALL H or D outputs, no weight inversions |
| ONE outer u, ALL6^m active inner masks | soft(sqrt b+H+D+6^m) | every singleton and pair-mask value |
| Balanced inner/outer reshape | soft b^[log_4(6)/2] | genuine joint sub-b input primitive |
| ONE fixed-Q term with entire outer digit box | soft sqrt b | actual shifted row box, not a single row only |
| Several explicit arbitrary right/left vectors | per-vector H+D after shared preprocessing | no implicit all-family oracle |
| Full primary all-encoding phase | literal count(8)>b | not credited as a sub-b phase |
| Native simultaneous paired bilinear outputs or their product | NOT acquired here | no whole-query/exponent gain claimed |

All proved operations are zero safe. Every inverse is a precomputed unit independent of input vectors; arbitrary zero/nonunit weights, x values, and final encodings are allowed. Auxiliary mask values are not original factoring witnesses. The positive sharing results avoid dense degree-b coefficient expansion in their stated regimes, while the full active-Q union and original terminal product remain unacquired at a better clock.
