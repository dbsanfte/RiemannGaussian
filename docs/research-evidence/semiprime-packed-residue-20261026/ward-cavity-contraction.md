# Execute Ward Schur complements, paired replicas and residue-only cavity removal

26 October 2026. Focused finite contraction test. Scratch only; no repository changes, code, tests or numerical campaign.

**Result.** The strongest regulated-mass Schur complement removes all known contact terms but leaves the desired resolvent with coefficient ONE. Opposite replicas isolate its pole as a constant term of a squared-mass inverse, whose finite clock factors remain long. A residue-only cavity can omit a certified unit bulk WITHOUT computing its regular self-energy, but the proposed recursive schedule still needs the original nonunit gate on each unclassified bulk. These are executed identities and costs of those specific proposals, not general barriers to a selected-residue algorithm. No faster acquisition is established.

## 1. Actual packed target and permitted source algebra

For the actual original bank put a_e=1-T_j*rho^t and w_e=K/2+[j²]_n. Write

    S_w(delta)=sum_e w_e/(a_e+delta),
    S_0(delta)=sum_e 1/(a_e+delta),
    C=Res_0 S_w.

All physical normalizations, componentwise Laurent conventions and the correct-bin packed-integer consumer are as in packed-source.md. Its first moment A1=sum a_e can be acquired and made a unit by a proper gcd/unit/global-zero gate plus deletion of one screened UNIT leaf if needed. Such deletion leaves C exactly unchanged. D=#remaining leaves and W0=sum remaining weights are known integers/algebra constants.

Primary framework: [Caracciolo–Sokal–Sportiello, arXiv:1105.6270](https://arxiv.org/pdf/1105.6270), Appendix A.5 (fermionic Gaussian/Wick determinants) and B.2 (determinant identities). Everything actually used below is an elementary finite matrix identity over the supplied coefficient ring or its componentwise Laurent algebras. No determinant/Schur-complement identity is differentiated after an invalid singular specialization.

## 2. Experiment A: use the REGULATED mass as the second insertion

Set b_e=a_e+delta before forming the two source columns. Let U=(1,b), V=(w,b) and D_delta=diag(b). Their covariance is EXACTLY

    Q(delta)=V^t D_delta^{-1}U
       =[[S_w(delta), W0],
         [D, A1+delta*D]].                         (1)

Here cancellation D_delta^{-1}b=1 is an identity of rational functions BEFORE specialization; the lower-right entry is sum b_e. This avoids the additional S_0 contact term of the unregulated-mass insertion.

The ordinary two-by-two determinant and its Schur complement are

    det Q=(A1+delta D)*S_w-D*W0,
    det Q/(A1+delta D)
       =S_w-D*W0/(A1+delta D).                    (2)

The normalizer is a legal formal unit because A1 was actually certified a unit. Its entire fixed-precision inverse and the contact term cost soft K (indeed almost constant once totals are known). Their residues vanish, and

    C=Res[det Q/(A1+delta D)].                     (3)

Thus the long common correction HAS cancelled, but its remaining scalar is literally S_w with coefficient ONE. Treating det Q as an acquired two-by-two determinant would hide its top-left input, the selected long sum. Its dimension does not pay that input. The source depends on delta and the actual masses; the fixed-basis matchgate parity test does not rule out this representation, and is not used to dismiss it.

A finite rank-two update gives a polynomial implementation target: with P(delta)=det D_delta, the mixed source coefficient N(delta)=[s t]det(D_delta+U diag(s,t)V^t) satisfies N=P det Q. At a singleton block P has a simple zero and (3) is a ratio of N(0) and P'(0)*(A1). At a whole-bin d-hit component the first relevant coefficients are at orders d-1,d. Removing P or identifying those coefficients remains an acquisition operation. The ratio is not a supplied cofactor merely because the update rank is two.

**Initialized execution:** joint G_h(T_j),G_h'(T_j) evaluation plus fixed-depth block triples, as in packed-source.md, supplies these singleton ratios at soft(K+sqrt(Kh)). The simpler value-only row gate also costs that bound and does not need the physical-clock derivative. No step in (1)–(3) improves either implementation's exponent.

## 3. Experiment B: opposite replicas remove regular background

Both replicas use the ORIGINAL constant clock weights:

    S_w(delta), S_w(-delta).

The finite identity

    delta/2*(S_w(delta)-S_w(-delta))
      =sum_e w_e*delta²/(delta²-a_e²)              (4)

is exact. Its constant coefficient is precisely C: at a_e=0 each term equals w_e, while at a nonzero mass it has zero constant term. In particular the selected replica is a pole-only/one-hot observable; no full-resolvent tensor representation is required as an output.

Up to the explicit minus sign between delta²-a_e² in (4) and a_e²-delta², the paired denominators are

    a_e²-delta²=(1-delta-T_j rho^t)
                  *(1+delta-T_j rho^t).

For one row their product is EXACTLY

    (1-delta)^h*(1+delta)^h
       *G_h(T_j/(1-delta))*G_h(T_j/(1+delta)).     (5)

All prefactors have unit constant term. Both finite clocks have length h, with the actual same T_j. There is no root-of-unity period or shortened interval in (5). Evaluating their jets uses two constant-rank instances of the inherited engine, at the old bound. Inverting them on a collision is not a legal unit-start series operation; (4) has only a componentwise Laurent interpretation there. Thus replica cancellation removes regular terms formally, but leaves the explicit squared-mass inverse in (4) as its unpaid input. It does not supply C by one known endpoint evaluation.

## 4. Experiment C: cavity removal without computing all regular self-energy

Inside a promised singleton block take the rank-one reset matrix

    B_kappa(delta)=D_delta+kappa*1*1^t,

with a known unit kappa. At a unique zero mass, B_kappa(0) is invertible at the good field and

    B_kappa(0)^{-1}*(kappa*1)=e_hit.

Its weighted scalar is w_hit, irrespective of ALL nonhit regular masses. This is a genuine one-hot solve target, not a request for the full inverse.

Split leaf modes into a proposed retained set L and removed cavity R. If D_R is invertible, put S_R=1_R^t D_R^{-1}1_R. When the additional pivot is a certified unit, exact Schur elimination changes the reset strength to

    kappa_eff=kappa/(1+kappa*S_R),

and changes its right side to kappa_eff*1_L. This is the same normalized one-hot equation on L. The regular self-energy can therefore cancel from its output if L contains the hit. But computing a numerical Schur complement requires S_R and its pivot guard; 1+kappa*S_R is an additive expression, not a native short torus binomial. A saturated additive pivot does not inherit an annihilator decoder.

There is a stronger RESIDUE-ONLY use: if product_(e in R)a_e is already certified a unit, the whole R contributes zero residue and may be omitted without acquiring S_R at all. That is lawful cancellation of a regular cavity. The precise missing input is the UNIT CERTIFICATE for the proposed large cavity, or equivalent hit support. A known endpoint guard can certify a few leaves; it does not certify the whole interior.

For an executed divide-and-conquer schedule choose R as half the clock against the current row set. Its product/nonunit certificate is an inherited restricted geometric query, with cost soft(J_R+sqrt(J_R*h_R)). The first nontrivial macroscopic gate on the whole family has J_R of order K and h_R of order h, so this schedule already pays the retained K^(5/4) scale. Coverage may let one omit the full root call, but querying its half-sized child changes only a constant factor. All-hit counting can use the all-row value/flag implementation at the old bound. This is the bill for this specific gate-based cavity algorithm, not a lower bound on all ways to prove a cavity regular.

## 5. Why singleton cofactor cancellation is not a global sum of ratios

At each correct hitting block a gated pair (d1,dw) has ratio equal to the squared tag. Summing L+dw/d1 over ALL globally hitting blocks recovers the exact packed C after the proved no-factor gates. A ratio of globally summed d1 and dw instead weights blocks by their unrelated cofactor amplitudes and returns only a common tag in a correct bin, not the hit count. It is not the packed C. Empty blocks require their constant determinant gate before any ratio is accepted.

Desnanot–Jacobi or Wick/Plücker relations on these scalar minors preserve that distinction. At a single pole the leading adjugate has rank one, giving relations among products of minors; those relations do not supply their individually unknown amplitude or support. Equation (2) is the strongest direct mass-source cancellation tested here: it exposes exactly which entry remains after all known terms are removed, rather than appealing to a general rank or recurrence objection.

## Outcome

The attempted contractions are finite and componentwise valid. The regulated Ward source has a paid Schur normalizer but retains S_w. Opposite replicas expose a selected projector but retain the long squared-mass inverse. A certified regular cavity can be removed without its self-energy, but the tested schedule needs the original long certificate. All current initialized completions remain at K^(5/4). A new identity furnishing ONLY the unpaid selected scalar or a cheap macroscopic cavity certificate would be substantive progress; none is claimed here.
