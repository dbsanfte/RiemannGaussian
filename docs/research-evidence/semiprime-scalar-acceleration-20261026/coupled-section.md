# Execute repeated coupled sections on the pole kernel

26 October 2026. Scratch paper calculation, no repository edits or h-entry arrays. **Result:** every dyadic section has the same compact cyclic-bidiagonal semilinear generator, and the pole-only state becomes ONE active phase after the q-Euler gauge. An acquired phase I modulo b~h/J would give a complete soft-J shortened query. No method acquiring that phase within the target budget is proved. This is not a general lower bound or a claim that a compact generator acquires its kernel.

Use sectioned-newton.md and the root's pole-kernel-handoff.md. In the good field c=Res C_delta spans a one-dimensional kernel of D(L), L=(1+z)S_q on coefficients modulo z^h. The actual pole is

    c(z)=lambda*z^I*B(z), lambda=(-1)^I/(q;q)_I,
    B(z)=sum_(m<h)q^(m(m-1)/2)z^m/(q;q)_m.

Every displayed factorial denominator has index<h and is screened. B is used as a truncated series, not as an infinite product at a finite-order q. The q-Euler gauge is an exact short-series operation, not a supplied full h-vector.

## 1. Execute the NEXT section: four components

For b=2^r write u=z^b and

    f(z)=sum_(e=0)^(b-1)z^e*f_e(u).

Let Q_b=diag(1,q,...,q^(b-1)), and let Z_b(u) have ones on its first subdiagonal and u in its top-right corner. Multiplication by z is Z_b, while S_q is Q_b*S_(q^b), where the last operator scales u. Therefore

    L=M_b(u)*S_(q^b), M_b(u)=(I+Z_b(u))*Q_b.             (1)

For b=4, the result of the second actual binary section is

    M_4(u)=[[1,0,0,q^3*u],
            [1,q,0,0],
            [0,q,q^2,0],
            [0,0,q^2,q^3]].                            (2)

Both the within-pair and wrap carries are retained. This agrees with applying the two-section formula again and regrouping by exponents modulo four. There is no auxiliary root of unity or unidentified exponent reduction.

Equation (1) is CLOSED for all b, with O(b) explicit generator entries and an O(log b)-bit template. It avoids b² dense generator materialization, but that is not yet a solve of D(L)c=0. The source of the full regularized problem is the component e=0 constant 1; its matrix system is D_delta(M_b S_(q^b))C=e_0, not a scalar polynomial in the ordinary matrix M_b alone.

## 2. Exact q-Weyl/quantum-binomial compression, with its shifted state

Put X=Z_b(u), Y=Q_b*S_(q^b), E=X*Y. Semilinearity gives

    Y*X=q*X*Y, X^b=u*I, L=Y+E.

At the wrap entry this uses S_(q^b)(u)=q^b*u. Freezing u before multiplying would leave an erroneous boundary defect.

Since Y*E=q*E*Y, finite q-binomial inversion gives the exact normal-order identity

    E^b=sum_(k=0)^b (-1)^k*q^(k(k-1)/2)*[b choose k]_q
                            *L^(b-k)*Y^k
       =q^(b(b-1)/2)*u*Y^b.                           (3)

For b=2 it reads L²-(1+q)*L*Y+q*Y²=E², which directly checks the noncommutative ordering. Formula (3) does collapse the wrap into u, but retains the q-translated states Y^k c. One cannot reduce every L power modulo D on those terms merely from D(L)c=0: Y^k c is not asserted to satisfy the same homogeneous equation. Sections may stop at the first dyadic b>=h, so b<2h. All needed q-binomial denominators then have index<2h<16H under the native h bound; their formula is not an emitted b-entry array.

For the GOOD single eigenmode there is a further true compression:

    Y^k c = theta^k*c/prod_(t=0)^(k-1)(1+q^t z), theta=q^I. (4)

The denominators in z have unit constant terms, so this is legitimate as a truncated formal series even at the desired native pole. Once theta is known, all translated modes are specified by one amplitude and one spectral parameter. The point of the acquisition problem is that theta has NOT been acquired. Equation (4) is a conditional state formula, not an initialized selected eigenmode.

## 3. Pole-only sections are sparse after the gauge

Conjugating by B gives

    a(z)=B(z)^(-1)c(z)=lambda*z^I,
    D(S_q)a=0.

Writing I=b*s+r, 0<=r<b, the section vector of a has precisely ONE active component: a_r(u)=lambda*u^s. All other components vanish. This differs from the full c sections, which have nonzero coefficients in both parities after I.

More explicitly if B_e^(b)(u) denotes the section of B at exponent e, then

    c_e(u)=lambda*u^(s+1_(e<r))*B_([e-r]_b)^(b)(u).      (5)

This gives every carry without constructing the b component vectors. The common section coefficients obey

    [u^(m+1)]B_e^(b)/[u^m]B_e^(b)
     =q^(b*(b*m+e)+b*(b-1)/2)
         /prod_(t=1)^b(1-q^(b*m+e+t)),                 (6)

in its valid finite coefficient range. Thus the symbolic sections are a shared hypergeometric template, not b unrelated sequences.

This gauge is a SYMBOLIC identification: applying B or B^-1 to a full h-vector would cost at least its emitted vector length in that implementation, and neither the actual c vector nor an h-entry B array is supplied. Only short-prefix convolution actions are paid in soft J. The unknown active component r is a genuine unsupplied datum. If I exceeds the O(J) paid prefix, the actual pole prefix is zero. A homogeneous prefix of zeros cannot initialize a nonzero active section; the regularized source is what fixes its occurrence. Finding a nonzero kernel vector is not accomplished by declaring one phase active.

## 4. Execute the conditional shortened query from ONE phase residue

There is a complete useful conditional algorithm. Choose the smallest dyadic b>=h/J (take b=1 when h<=J). Then b=O(h/J); in the target regime J=Theta(K), this is O(sqrt K). Suppose one has ACTUALLY acquired r=I modulo b for the good hit, or a polylogarithmic covering palette of such residues.

Keep ONLY original clock indices r+b*t, 0<=t<ell_r,
    ell_r=1+floor((h-1-r)/b),

discarding r>=h. Use common base q'=q^b, shifted row roots T'_j=T_j*q^-r, and the unchanged row tags. Every new leaf is exactly an original leaf at that index; no phase carry or endpoint correction is missing. Starts, powers and metadata cost soft J per supplied phase. The inherited common-baby engine costs

    soft(J+sqrt(J*ell_r))=soft J,                       (7)

because ell_r<=ceil(h/b)=O(J). More directly, form the degree-ell_r monic clock polynomial by a division-free product tree and evaluate it at the J shifted row roots by monic MPE. This costs soft(J+ell_r)=soft J and invokes no additional q-prime order hypothesis, root separation or nonunit difference inverse. For a polylogarithmic palette, separate or shared calls preserve soft J. This is the shortened-query ACQUISITION bound; the inherited once-only factor/tag recovery costs soft K, and is not claimed to cost soft J when J is smaller than K.

All required unit guards are inherited directly: each actual q' node gap has exponent b*gap<h. If a geometric conversion or boundary convention requires the next factor, its exponent is at most b*ceil(h/b)<=h+b<3h<16H, using h<=8K^(3/2)+9 and K>=54. Thus the ACTUAL supplied q screen covers every inverse; no unproved global order assertion about q^b is needed. Physical indices remain in the original short interval after its supplied normalization. The exact covered hit survives for the correct phase. Wrong phases/bins return only verified factors or bounded failures, and one cannot stop after an unverified ratio. Thus an ACTUAL coarse phase supplier would produce the desired soft-K whole query, not merely another formal consumer.

For the requested soft-K target without ANY lower bound on J, choose instead the least dyadic b_K>=max(1,h/K). Then b_K=O(sqrt K), ell_r<=K, and the explicit degree-ell_r clock product plus MPE at J<=K/3 rows costs soft K. Every inspected leaf is still an original leaf; the existing norm/coordinate classification and original labelled-leaf recovery finish or return bounded failure. This version is uniform under the actual J upper bound alone. The sharper b~h/J version above gives soft J; identifying b with O(sqrt K) in that version requires J=Omega(K), or the separately proved thinning lower bound, and is not inferred from J=O(K).

The supplied phase must refer to the UNKNOWN global hitting index I, not merely to a row label or a chosen bookkeeping origin. Artificially relabelling the clock i->b*i makes its phase zero but stretches the clock to length b*h; restricting that stretched interval back to the zero phase restores h positions and gives no saving. No such genuine phase supplier is obtained by (1)–(6). Keeping all b phases explicitly restores the unsupplied phase state; acquiring an arbitrary polynomial-kernel support bit is not free. This conditional algorithm is recorded as an acquisition target, not credited as an improved all-input factorer.

## 5. A second exact compression: normalized backward eigenvector

It is also possible to represent every candidate spectral mode in O(J) algebraic coordinates rather than b sections. Let theta be a FORMAL root of D in the acquired algebra B[theta]/D, n=h-1, and normalize its last candidate coefficient v_n=1. The eigenvector coefficient rule gives, without any nonunit inverse,

    v_m=q^(m(m-1)/2-n(n-1)/2)
                     *prod_(k=m+1)^n(theta-q^k), 0<=m<=n. (8)

The requested last pair is already affine in theta. However the FIRST boundary equation is

    (1-theta)*v_0=-q^(-n(n-1)/2)*W_h(theta).             (9)

Therefore this compact candidate is an actual finite eigenmode only on the clock-intersection branch W_h(theta)=0. Choosing that branch or its good nonzero projective output is precisely the unacquired selection; imposing D(theta)=0 alone does not do it. This formulation does not prove the full remainder must be computed. It identifies the exact finite boundary retained by this proposed small-state compression.

Products in (8) are implicit q-factorial templates. For O(J) short factors they can be acquired modulo D within soft J, but a symbolic binary product with q-shifted arguments is not an O(log h)-cost evaluation: its distinct shifted subcalls or a new structured scalar contraction must be paid. The existing joint engine completes the long boundary at soft(J+sqrt(Jh)). No full h coefficient array was emitted here.

## Outcome

Repeated dyadic sections DO admit a compact closed generator and a one-phase pole template. The elementary q-Weyl identities preserve the wrap exactly, and the fourth-component step is explicit. A coarse residue I mod b with b~h/J would complete the native query in soft K. Neither that phase nor the clock-intersection boundary in (9) has been acquired at that cost. These calculations leave a sharply specified sparse-kernel/phase-selection operation, not a general lower bound or a new factoring exponent.
