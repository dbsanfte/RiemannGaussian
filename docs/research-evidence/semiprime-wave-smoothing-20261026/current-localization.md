# Current, invariant and localization: exact finite bridge audit

26 October 2026. Requested paper study only; the factorization goal remains PAUSED. Read the supplied 59-page [paper](https://github.com/openai/math/blob/main/preprints%2FLocal-smoothing-for-the-Euclidean-wave-equation-October-25-2026%2Fpaper.pdf), Sections2 and5 and AppendixE, using its printed page numbers below. This is not an independent verification of the paper's global PDE claims. No factoring experiment or goal resumption; this report was subsequently archived with the study.

**Finding.** The strongest exact native comparison is the paper's passive quadratic invariant Phi and its two-center factorization. A public native discriminant realizes that invariant, but the corresponding clock transport requires division by N and leaves the integer row catalogue. Its short integral unipotent transport reduces to an already known reflection. Coherent norm-square pairing can preserve a unique-hit weak ratio exactly; it does not acquire its long resolvent amplitudes. The Gaussian localization estimates supply neither a finite-ring selector nor a cheap evaluator.

Notation warning: the paper's h is a semiclassical frequency scale, its N a frequency size, and its K a fixed large analytic constant. None is the same as native clock length h, semiprime N, or conductor K. Write h_wave for the paper's h in the discussion below.

## 1. What actually cancels in the two-flow construction

On printed pp6–7, the null-coordinate phase (2.1) has symbol satisfying

    -w^t C(p)w=kappa*|w'-v*w0|²,                 (2.2)

with polarization E(v)=(1,v). The imaginary translation along two real flux states gives exactly exp(-kappa*|zeta-vR|²/2), equation(2.4). Thus the Gaussian is fixed by the symbol's nonnegative quadratic defect; it is not an independently chosen approximate cutoff.

Lemma2.1, printed p7, defines the lifted fields D_(ell,a), their continued state G and Z_ell. The finite cancellation uses D_(ell,a)G=0, the symmetric-system conservation identity and a purely imaginary acceleration term. Taking the real Hermitian tensor removes that acceleration. Written in real fields, the resulting tensor is a sum of four real squares, with divergence-free columns. This is a genuine differential identity for a FINITE superposition; modes are summed before taking the square, so interference is retained rather than discarded termwise.

The flux map Theta is quadratic, (2.7)–(2.9), printed pp8–9. Its density pushforward needs the real Jacobian J=4|R|^(2d+2), equation(2.11). Equal state Hessian blocks cancel because the coordinate map is holomorphic. Proposition2.2 then gives the acquired *definition*

    chi=sum_(kappa,v) V^v iota_e(u_(kappa,v)) m_(kappa,v),
    A0=chi*chi^*,
    m=(kappa/y)^(d/2) exp(-kappa*y*|W-v|²/2),       (2.14)

and the two orthogonal time components in (2.15), printed pp9–10. No theorem in these sections evaluates that coherent sum from a short implicit modal polynomial in sublinear time.

## 2. Phi and the native quadratic: an exact comparison

The useful paper identity is on printed p9, equations(2.10)–(2.13):

    Phi=S1+P·P/(2Y), W=P/Y,
    ell(w)V^v=-(w-W)·(w-v)/2,
    (dPhi)V^v=0, (dW)V^v=(v-W)/(2Y).

The first invariant is passive along the whole current; the second identity controls angular mismatch. This is stronger than a Gaussian metaphor.

For an actual native row f(X)=aX²+ell X+cN, a!=0, let j be its stationary colour and write f(j)=H*eta, f'(j)=K*kappa. The exact INTEGER factorization is

    f(X)-f(j)=(X-j)*[a(X-j)+K*kappa].             (1)

This has the same two-center algebraic shape as ell(w)V^v. But f(j) is H*eta, not an integer zero, and substituting X=j+Ku leaves

    f(j+Ku)/H=a*u²+kappa*u+eta.

The actual factor R=j+Ku and its clock index remain unknown. The public modular phase classes were already compiled in the incidence/unique-cover packets; (1) does not identify which class is realized by the unknown factor.

More exactly set Y=2a, P=ell, S1=-cN in the scalar version of the paper's formula. Then

    Phi_native=(ell²-4acN)/(4a).                  (2)

This is an acquired rational invariant of O(log N) bit height. The actual short coefficient bounds give 0<|a|<min(P,Q) for the nonzero-a rows under discussion, hence gcd(a,N)=1; 2 and4 are also certified units. For any enlarged family that lacks that bound, gate gcd(a,N) first rather than assume an inverse. Rows with a=0 are NOT covered by the division in (2): they remain actual axis rows handled by the existing axis/label consumer, or require a separately oriented chart with c!=0. No axis coverage is removed by this comparison. It is the DISCRIMINANT, not a new selecting equation. In Z/N the term cN is zero; reducing (2) too early loses the integer factor-pair relation rather than preserving it.

### Test an actual Phi-preserving clock correction

The native numerical leaf changes ell to ell-HI. Holding a and (2) fixed would require

    c_I=c+H*I*(H*I-2ell)/(4aN).                   (3)

This is a fully explicit correction, but generally not an integer coefficient. In the prepared short window, 0<|I|<16H<min(P,Q), so gcd(HI,N)=1. Integrality in (3) therefore REQUIRES N|(HI-2ell). The same bound gives |HI-2ell|<16H²+H<N because N>256H². Thus HI=2ell is the only possibility. For strict centered |ell|<H/2 it is impossible at nonzero I. If a centered-endpoint convention admits ell=±H/2, the exceptional I=±1 gives ell-HI=-ell and c_I=c: this is just the public reflection, not a new clock selector. The amended parity family has ell=0 mod4 and H/2=2 mod4, so excludes that endpoint outright. Hence this particular invariant-preserving clock move has no nonreflection short integer continuation. For retuned conductor H_row<=H, use its actual physical index |I|<16H and centered |ell|<=H_row/2; the same |H_row I-2ell|<16H²+H<N proof applies without N<=K_row^6. The normalized/parity clock index must first be converted to that actual physical index.

The natural integral Phi flow is the binary-quadratic unipotent change

    ell'=ell+2a*t,
    c'*N=cN+ell*t+a*t².                          (4)

It preserves (2) exactly. If 0<|t|<min(P,Q), integrality of c' requires N|(ell+a*t). In the native short-coefficient regime |ell+a*t|<N, it forces ell+a*t=0. Then ell'=-ell,c'=c: only the already public reflection remains, when t=-ell/a is an integer. Choosing t a multiple of N is lawful but moves coefficients far outside the short ellipse. This does NOT rule out all conic/SL2 transformations or a change of several coordinates; it audits the concrete passive-Phi correction and its short integral flow. It does not make both unknown physical branches cheap.

## 3. Coherent squaring can preserve a weak residue, but not acquire it

There is an exact finite algebraic analogue which avoids an output-level square loss. In the prepared etale algebra let bar be its conjugation, fix the formal delta under bar, and define the actual long physical Lambert sums

    U0(delta)=sum_l w_l/(delta+a_l),
    Um(delta)=sum_l m_l*w_l/(delta+a_l),
    a_l=1-T_j*q^(-i).

Here l=(j,i), every supplied w_l is a unit, and m_l is the row mark. Each sum has at most a simple delta pole componentwise. At the good unique hit, c_m=m_hit*c_0, c_0=w_hit!=0. Therefore the finite identities

    Res_delta [delta*U0*bar(U0)]=c_0*bar(c_0),
    Res_delta [delta*Um*bar(U0)]=m_hit*c_0*bar(c_0)   (5)

give the SAME weak mark ratio with a nonzero good denominator. The norm/coordinate gate can factor or license its inversion; a wrong-bin saturated additive denominator declines. No positivity or approximation is needed for (5), and no high-order Laurent pole is introduced. With unweighted U0, its good residue is one.

This is the already credited coherent/Ward/two-replica mechanism in explicit norm form, not a new supplier. Both long U amplitudes remain unacquired. Taking the ordinary norm at delta=0 would be undefined; discarding the regular-pole cross terms without the displayed delta factor would be wrong. For the original packed count, squaring also changes its numeric output; (5) is only a sufficient unique-hit projective replacement, not equality to that original integer count.

The exact finite character projector is also valid: b^-1 sum_s zeta^((i-r)s) equals the indicator i=r mod b when b and the cyclotomic differences are units. But it requires the corresponding twisted long responses. The frozen clock-phase character source already specifies those responses and their extension costs. Imaginary translation in the PDE proof does not acquire that missing character datum.

## 4. Why Section5 localization is not a finite modular selector

Section5, printed pp18–21, uses two REAL regions. On the active wall the Gaussian gains exp(-c0*s/h_wave); on a small center cap its inverse costs exp(C*gamma²*s/h_wave). The aperture gamma is fixed first so those exponent constants are separated. The positive majorant J_l and its derivatives give (5.4)–(5.6); Gaussian inversion yields the interior lower bounds(5.11)–(5.12). Division of bounds produces the energy inequality, not an exact support projection or an evaluation algorithm.

Those steps need ordered positivity, absolute values, real volumes and smooth symbol cutoffs. They do not survive reduction modulo unknown prime factors. There is no unital additive/multiplicative embedding of C into a nonzero positive-characteristic coefficient ring: the characteristic relation conflicts with the inverse of that integer in C. An auxiliary complex lift is possible, but its smallness does not detect a zero modulo an unknown factor. For example a nonzero integer multiple of that factor has nonzero ordinary absolute value. A new exact modular bridge would be required.

For one explicit proposed embedding i -> v_i=i/h_clock, suppressing adjacent phases by a Gaussian requires the scale parameter of order h_clock² for fixed suppression, and the center still depends on the unknown hit. The paper's inverse Gaussian then has its stated exponential cost unless its fixed-cap restrictions are retained; using those restrictions instead does not resolve an individual unknown phase. This diagnoses that embedding only, not every analytic algorithm. A finite quadratic-character chirp has no decaying ordered Gaussian majorant to substitute for this argument.

## 5. AppendixE clarifies the scope rather than supplying a new oracle

AppendixE, printed pp49–53, replaces the cone by a SIMPLE largest eigenvalue of a real symmetric pencil with strictly positive transverse Hessian (TheoremE.1). Formula(E.2) makes polarization a local angular coordinate. The passive chart(E.3), conserved pushforward(E.5), and symbol-adapted attenuation(E.6) use the positive block S_perp. Its bounds(E.9) and inversion(E.10) reproduce Section5's wall/interior comparison. The cubic-sheet example shows the method is not confined to a quadratic characteristic variety.

A modular matrix has no canonical largest real eigenvalue or ordered convex sheet. Producing an isolated algebraic eigenprojection requires its own unit spectral gaps and branch selection; that is not supplied by naming the native conic as a symbol. Nor does the paper's rank-one current imply a constant-size modular representation of the J*h leaves: its chi is already the coherent sum of all relevant modes.

## Conclusion

Two exact identities transfer at the algebraic level: the discriminant/Phi comparison and the normalized coherent residue pairing(5). The first does not preserve the native integer bank under a nontrivial short clock transport; the second preserves the weak output but requires the original long amplitudes. The PDE localization mechanism adds powerful real estimates, not a paid finite-ring contraction. No new factoring bound, resumed goal work or claim of a general impossibility result is made.
