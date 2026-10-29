# Execute coefficient multisection and a finite q-Gosper contraction

26 October 2026. Paper-only continuation from the frozen projective-readout packet; no tests, numerical campaign, repository edits, implementation or Lean.

**Outcome.** I executed coefficient-index multisection of the initialized dot product and a polynomial q-Gosper telescoping ansatz in the acquired quotient. Multisection halves length but doubles the number of hypergeometric numerator/denominator parameters; the literal full-section completion costs soft K² at the natural stride K. A polynomial q-Gosper certificate has a concrete native resonance: on the good hit its degree must be I+1, where I is the unknown physical clock index. The now-paid first-5J prefix excludes short such certificates on continuation. Neither is a general lower bound or an exclusion of rational certificates/structured recombination. No improved full query was acquired.

## 1. Exact initialized problem

Use the two-monic family and pure or conductor-aware legal K, H=K², h=2H+1, J<=K. Its F=product_j(X-y_j), unit roots y_j, tags and q=pi^H are acquired. The good family has exactly one hit y_j=q^I, 0<=I<h, at the nonsplit field. q has all required short unit differences and good-field order greater than 256H². Put rho=q^-1, A=rho^h and

    G_h(X)=product_(i<h)(1-rho^i X)=sum_(t=0)^h a_t X^t.

Every coefficient ratio is legitimate because all nonzero exponents through h+1 are guarded:

    a_0=1,
    a_(t+1)/a_t=(A-rho^t)/(1-rho^(t+1)).             (1)

For a supplied linear functional ell on B[X]/F, b_t=ell(X^t mod F) has a supplied proper rational generating series of denominator rev(F). Its first J values and numerator cost soft J; far selected values use modular powering, not a supplied whole stream. The finite contraction is

    S=ell(G_h mod F)=sum_(t=0)^h a_t b_t.             (2)

A general linear projection is not by itself the nonlinear two-norm output. Solving (2) uniformly could acquire the remainder via transposition/batching if that operation were actually proved and charged; alternatively the directional norms or row-cofactor ratio can be sought directly.

## 2. Execute parity on the initialized scalar pairing

Let B(z)=P(z)/Q(z)=sum b_t z^t, Q(0)=1, deg Q<=J, deg P<J. Parity gives the supplied small rational functions

    Q2(u)=Q(z)Q(-z), u=z²,
    B_even(u)=Even(P(z)Q(-z))/Q2(u),
    B_odd(u)=Odd(P(z)Q(-z))/Q2(u).

Their coefficients and starts cost soft J, without field inverses or row separation. Q2 has the powered row roots y_j², with degree still J; cancellations may reduce it. These are paid exact parity inputs, including repeated roots.

Then (2) becomes two dot products

    sum_s a_(2s)b_(2s) + sum_s a_(2s+1)b_(2s+1),

with their exact clipped lengths. Crucially the hypergeometric weight stays first-order, but is no longer the original one-parameter q-binomial weight. For Z=rho^(2s), e=0,1,

    a_(2s+e+2)/a_(2s+e)
       =rho^(2e+1)*(Z-A*rho^(-e))*(Z-A*rho^(-e-1))
          /[(1-rho^(e+1)*Z)*(1-rho^(e+2)*Z)].       (3)

The initial weights are 1 and (A-1)/(1-rho), both actually acquired. Formula (3) is valid through the final included term; the next terminating numerator is retained rather than divided out.

At stride B=2^r, each section e, 0<=e<B, has ratio, with Z=rho^(Bs),

    a_(Bs+e+B)/a_(Bs+e)
      =(-1)^B*rho^(B*e+B(B-1)/2)
          * product_(r=0)^(B-1)(Z-A*rho^(-e-r))
          / product_(r=1)^B(1-rho^(e+r)*Z).         (4)

Its clock length is about h/B but it has B numerator and B denominator factors. Only denominator evaluations actually used for indices <=h are inverted; they are certified native short units. Formula (4) does not authorize advancing beyond the finite endpoint.

All B sections of b have a common denominator with roots y_j^B. Their B numerators are precisely the coefficient sections of

    P(z)*Q_B(z^B)/Q(z),
    Q_B(u)=product_j(1-y_j^B u).

The quotient is exact polynomial since Q is the corresponding split denominator; the rational parity derivation also covers cancellations. Dense simultaneous acquisition emits O(JB) coefficients. At the natural B~h/J~K this is soft K², and the remaining B dot products of length O(J) also contain O(h) scalar terms. This is a fully initialized literal completion, not a soft-K contraction.

One could seek a compact **joint** action on all section numerators and the structured factors in (4); that would be a new algorithm. Merely keeping the numerator/denominator degrees fixed under decimation is false for this transform. This differs from the old Bostan–Mori long-numerator-window audit: here the finite q-hypergeometric weights themselves acquire B parameters under coefficient multisection. No output-size lower bound for the final scalar is asserted.

## 3. Graeffe norm is zero-safe but is not this coefficient decimation

The native odd-order subgroups give the exact identity

    G_h(X)G_h(-X)=product_(i<h)(1-rho^(2i)X²).

At every supplied row and every local component, 1+rho^i y_j is a unit, since rho^i y_j has odd order. Thus the squared-base/squared-root product preserves the actual zero predicate, and its row-cofactor pair has the same good-field tag ratio. Numerical acquisition of that unit multiplier is unnecessary for the weak output. However its horizon is still h, and it does not produce either coefficient section in (3). This is the already audited norm-parity credit, not a new length reduction.

Clock parity is a different exact identity:

    G_h^rho(X)=G_(ceil(h/2))^(rho²)(X)
                    *G_(floor(h/2))^(rho²)(rho X).

It really halves the two child horizons but keeps both finite children and their amplitudes. Without a new shared contraction, computing both by the old engine costs a factor of about sqrt(2) more than one full call. Selecting the child containing the good hit is itself an unacquired membership test. These statements concern that literal split, not every possible use of a residue palette.

## 4. A new concrete certificate attempt: finite q-Gosper in the quotient

Let x be the unit class X modulo F and c_t=a_t x^t. By (1), with z=rho^t,

    c_(t+1)=x*(A-z)/(1-rho*z)*c_t.

Seek a quotient-valued polynomial R(z) for which T_t=c_t R(rho^t) is an antidifference: T_(t+1)-T_t=c_t. Its exact cleared equation is

    x*(A-z)*R(rho*z) - (1-rho*z)*R(z)=1-rho*z.     (5)

All its input coefficients x,A,rho are paid. If a solution is finite at both endpoints, c_(h+1)=0 gives the initialized readout

    sum_(t=0)^h c_t = -R(1).

Applying ell would solve (2). This is a genuine algorithm candidate: solve the finite coefficient equation (5) with a controlled degree and evaluate R(1), rather than invoking a symbolic summation name without a certificate.

### Native leading-degree resonance

Specialize to the good nonsplit field and then to the hit root x=theta=rho^(-I). Any polynomial solution R there is nonzero because the right side is nonzero. A constant solution is impossible: its constant and linear coefficient equations imply x*(rho*A-1)=0, whereas x and 1-rho^(h+1) are units. Let d be the degree AFTER this specialization, dropping any globally present leading coefficients that vanish at the hit root; d is at least one. With nonzero field leading coefficient r_d, comparing z^(d+1) (strictly above the right-hand degree) in (5) gives

    (rho-theta*rho^d)*r_d=0,
    hence rho^(d-I-1)=1.                         (6)

For degrees in the natural range below ord(q), with 0<=I<h, this forces d=I+1 (more generally the congruence is modulo the actual order). In particular, after the **paid first-5J prefix** in initial-chart.md has returned no factor, the good hit has I>=5J. Therefore no polynomial solution of degree <=5J exists for this certificate ansatz on that continuing input. This is a necessary condition only; it does not claim existence at degree I+1 or exclude a rational solution with a different pole structure.

For any preselected fixed degree budget cJ, the same kind of slightly longer original-prefix screen could test its early resonances within soft J, subject to the stated positive-label/finite-size guard. No such optional screen or arbitrary rational classification is counted as a new acquisition result here. The stated 5J conclusion uses the already proved preparation verbatim.

The coefficient recurrence for (5) is executable, but its terminal degree conditions contain the factors rho-x*rho^d. Detecting their nonunits as d runs is exactly testing the original row roots against the finite clock. Thus it is not lawful to claim that a generic “degree bound computation” for (5) is free.

## 5. Primary summation source and its exact interface

Read Abramov–Paule–Petkovšek, [*q-Hypergeometric Solutions of q-Difference Equations*](https://www3.risc.jku.at/publications/download/risc_2062/Abramov_PP_Petkovsek.pdf), introduction, §§2,6–7. Their qHyper framework uses a computable characteristic-zero field, q not a root of unity, and a “q-suitable” field algorithm finding all n with p(q^n)=0. Section 2 uses that operation to obtain polynomial solution degree bounds; §6 applies rational certificates to indefinite summation. These are symbolic algorithms, not a composite finite-ring bit bound.

For the present certificate, that degree test instantiates (6), or across all row components the condition

    F(rho^(1-d))=0.

This is the native finite clock membership problem, not supplied order data. The source's q-suitability oracle is therefore not imported into the algorithm. The cleared finite identities (3)–(6) above were proved directly, so neither characteristic zero nor non-root-of-unity assumptions are used to assert them.

Bostan–Yurkevich's q-holonomic terminal algorithms remain the known comparator, not a fresh fixed-order bound for growing J. Their existence-of-recurrence principle alone does not contract (4) or supply the low-degree solution of (5).

## Cost and exact remaining opportunity

The first parity step, its rational numerators and starts, and a fixed O(J) number of hypergeometric coefficients are paid in soft J. The literal all-section completion at B~K costs soft K². A low-degree polynomial q-Gosper shortcut fails on the actual no-factor prefix continuation by (6); a rational or matrix certificate could still be investigated with its poles and finite endpoints charged.

The strongest remaining concrete operation exposed here is a **joint section contraction** using the common powered denominator and the B shifted Pochhammer factor pairs in (4), without outputting JB section numerators; or a lawful rational-certificate solve for (5) whose initialization avoids the native clock-membership degree test. Neither is obtained in this pass. The best full weighted query remains soft K^(5/4); the uniform two-monic fallback remains soft K^(3/2). No whole-goal rate improvement or general complexity lower bound is claimed.
