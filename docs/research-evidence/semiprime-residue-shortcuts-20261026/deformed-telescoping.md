# Moving-root regularization and a finite valuation coboundary

26 October 2026. Paper execution on the actual unique-hit beta-coupled bank. Result: a degree-J multiplicative moving-root deformation, exact finite endpoint ratio and residue-only recurrence, with a completely initialized evaluator at the retained soft(J+sqrt(Jh)) bound. No nearlinear acquisition is established. The new tested certificate is a logarithmic/multiplicative one; it is not the old same-denominator additive certificate or a general algorithm obstruction.

## 1. Input and allowed change of source

Input is acquired monic D(X)=prod_j(X-T_j), q, 0<=i<h, J<=K/3, h<=8K^(3/2)+9 for the original bank. For the amended unthinned parity bank use its actual bound h<=8sqrt(2)K^(3/2)+9 instead; alternatively use its already endpoint-gated/padded parity-shortened clock Q=q² and length L, whose bound is smaller than the original displayed bound. All formulas below use the chosen actual base/horizon consistently. At the nonsplit good factor exactly one physical leaf is zero, at i=I, with a simple row root. The current amended parity family can replace the old family after its licensed preparation; this does not make the hitting row known. All native small q-gaps used below are already units. No root order or bounded discrete logarithm is supplied.

Set t=1+delta and move all row roots together:

    D_t(X)=t^J D(X/t)=prod_j(X-t T_j),
    L_i(t)=partial_t D_t(q^i)/D_t(q^i).

Only the first two jets are needed for the scalar algorithm; they are acquired in soft J from

    D_1(X)=D(X),   partial_t D_t(X)|_(t=1)=J D(X)-X D'(X).

At the good collision partial_t D_t(q^I)|_1=-q^I D'(q^I) is nonzero. Therefore Res_(t=1) L_I(t)=1. All other good terms are regular. The exact target

    A_h(t)=sum_(i=0)^(h-1)(-1)^i L_i(t)

has residue (-1)^I. Its physical multiple-hit interpretation elsewhere is a signed sum of multiplicities, not a claim of global uniqueness. This nonlinear root deformation is legal and costs soft J; one must not replace it by D+delta while silently keeping the same numerator.

A more general linear deformation D+delta E with compensated numerator E has the same residue 1 at a simple clock zero whenever E(q^I) is nonzero. That nonvanishing needs an actual gate or proof. The moving-root choice supplies it on the promised field, without choosing E from unknown I. It does not globally license inversion of E(q^i).

## 2. Exact finite logarithmic ratio and its endpoint law

Define the rational function (not supplied as an expanded input)

    R_h(t)=prod_(i even<h) D_t(q^i) / prod_(i odd<h) D_t(q^i).

Then A_h=R_h'/R_h and

    Res_(t=1) A_h=ord_(t=1) R_h.

The crucial covariance D_(qt)(q^i)=q^J D_t(q^(i-1)) gives the CLEARED finite identity

    R_h(qt) R_h(t) =
    D_t(q^-1)/D_t(q^(h-1)),                    h even;
    q^J D_t(q^-1) D_t(q^(h-1)),               h odd.       (1)

This can be checked directly by cancellation of each interior factor before any long coefficient expansion. Differentiating the full identity, with the chain-rule factor q retained, yields

    q A_h(qt)+A_h(t)=L_(-1)(t)+(-1)^(h-1)L_(h-1)(t).       (2)

Thus the endpoint rational function on the right is acquired in soft J. This is a genuine logarithmic/multiplicative decomposition retaining the selected residue, unlike cancellation of the entire marked divisor. Its two endpoint functions have degree J and no h-entry input.

## 3. Execute the residue-only recurrence

Over a scalar field component, let a_k=Res_(t=q^k) A_h(t). Taking local residues in (2) gives

    a_(k+1)+a_k=e_k,

    e_k=Res_(t=q^k)[L_(-1)+(-1)^(h-1)L_(h-1)].             (3)

The q factor in (2) makes the first term's residue exactly a_(k+1); omitting it gives the wrong recurrence. For the good hitting row T=q^I, its contribution has a_k=(-1)^(I+k) on -I<=k<=h-1-I and zero outside that interval. Its two endpoint impulses are at k=-1-I and k=h-1-I. The finite q-order margin prevents wrap in this displayed length-h interval. Other rows may occupy the same full q-orbit OUTSIDE that interval; they must not be declared absent.

Equation (3) explains the remaining data in this particular proposed normal-form algorithm: it needs the bounded orbit position of the degree-J endpoint poles relative to t=1, or equivalently the alternating valuation on the ORIGINAL interval. The endpoints are supplied as polynomials, not as a list of exponents q^k. Converting their actual roots into those bounded positions is not a paid operation. The zero initial values outside a chosen arc are therefore not automatically supplied by the short polynomial coefficients. The unique-hit promise gives exactly one contribution on the requested arc, but does not tell its phase.

Ordinary rational q-summability normal forms cannot simply be imported with an infinite-orbit hypothesis: native local q has finite, unknown order. If one instead uses the whole finite orbit, (3) is a cyclic recurrence with a parity wrap and a different boundary condition; its endpoint locations/order are still unsupplied. No assertion that every rational-certificate method must fail follows. A direct algorithm for the selected valuation in (1), from its degree-J endpoint data and finite window, would be a valid new supplier.

For provenance, Chen–Singer's primary paper develops q-discrete residues and rational q-summability (Definitions 2.7 and Proposition 2.10): *Residues and Telescopers for Rational Functions*, Adv. Appl. Math.49 (2012),111–133, https://arxiv.org/abs/1203.4200 ; author PDF https://singer.math.ncsu.edu/papers/YAAMA1465.pdf . Its orbit-residue language motivates (3); no complexity theorem or infinite-order hypothesis from that paper is applied to the composite native input. Equation (3) is proved directly here. The earlier Oct24 rational-mixture report already identifies retained additive orbit invariants; this report does not count that observation as new scalar acquisition.

## 4. Fully initialized execution and composite guards

Put f_i(t)=D_t(q^i), g_i(t)=partial_t D_t(q^i). The fraction-free transfer for a signed logarithmic sum is

    [P_(i+1),N_(i+1)]^T
    = [[f_i,0],[(-1)^i g_i,f_i]] [P_i,N_i]^T,
    [P_0,N_0]=[1,0],

so P_h=prod_i f_i and N_h=P_h A_h. At the good field P_h(1)=0 and partial_t P_h(1) is a nonzero unit there, while

    N_h(1)=(-1)^I partial_t P_h(1).

Acquire only the first t-jet, i.e. dual numbers at t=1. All transfer coefficients have degree O(J) in the geometric clock variable and fixed matrix/jet rank. Pairing the alternating steps and forming blocks of length b costs soft(Jb); monic MPE at the actual giant clock starts costs soft(Jb+h/b). All operations before final gating are division-free. Taking b=max(1,ceil(sqrt(h/J))) gives soft(J+sqrt(Jh)). The extra numerator g has degree J and changes only a constant factor relative to the frozen phase evaluator. No h coefficients, h endpoint locations, or h q-binomial entries are assumed acquired.

Norm/coordinate-test partial_t P_h(1). It is nonzero at the good field, so norm saturation cannot force an invalid inversion: either a proper factor appears, or the inherited nonsplit classification gives a certified global unit. Invert only then and validate the resulting +/-1 candidate by the existing base-coordinate and gcd tests. Wrong bins may fail or produce a factor; a saturated norm of the additive derivative output is a decline, not an actual-leaf relation and not an input to the mixed decoder. One must continue other bins after a rejected candidate. These steps cost soft K beyond acquisition. A norm nonunit from an ACTUAL emitted leaf can use original mixed labels; arbitrary additive pivots are not assigned that decoder.

Endpoint screens, if desired, evaluate D(q^-1) and D(q^(h-1)) by MPE/localization with actual mixed row labels. Screening the last original endpoint can factor; otherwise it removes only that genuine endpoint hit. Removing endpoint residues does not initialize the interior recurrence (3). The fixed startup branch cannot silently omit an endpoint from R_h while retaining the same formula (1).

## 5. What would make this a shortcut

The candidate is now a precise finite selected-valuation primitive: from D_t and the two short endpoint polynomials in (1), acquire ord_(t=1) R_h, or its first-variation ratio, without producing the long quotient. The useful response survives the deformation and the logarithmic cancellation; no unknown clock cofactor normalization is required. However the executed nearlinear operations stop at endpoint-polynomial data. The only completed readout here remains the shared block engine at K^(5/4). This does not prove a separation or exclude another deformation, selected-residue reduction, or native arithmetic algorithm.

Prior exact inputs: frozen clock-phase/phase-recurrence.md (unit gates, original alternating first variation and block engine), symmetric-character.md (finite character tails), and recurrence-checkpoint evidence/semiprime-rational-mixture-telescoping-20261024/rational-mixture.md (older additive orbit invariant). No repository file, group preparation, numerical campaign, implementation or Lean artifact was changed.
