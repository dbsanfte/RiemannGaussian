# Independent exact review A: arbitrary-clock higher-order recurrence

2026-10-16. PASS. Mathematical proof/source review only; no original report or repository source was modified and no build was run.

Targets: arbitrary-base-recurrence.md10847 bytes/SHA256 `586a884f1a679952919af7c97a24456a574bb94f32669a94aa43f6ab97e1523a`; recurrence-source-pins.json1012 bytes/SHA256 `485a0219177b79cb7f10a3c525800dcf3c7e055e08996c903b38b9104c547a55`. Independently checked all four dependency lengths/hashes, including immutable arbitrary-base-ratio.md8347/`4241ae43992bfba775925e3e0c8fb368e4682324d2d7411a7d658b3d1a204eaf`, the old uniform screen and general-q report, and latest all-semiprime setup13939/`4c4efaba5c3a09dd4ca1a87801e44212d5fcd2570ff26ec5f193f71589ec0d46`.

## Ratio, shifted samples and grouping

Iterating the coefficient relation gives the exact positive-numerator form in equation5. The g exponent is -jt-binom(t,2) outside the running g^k clock. The missing denominator factors give B_t degree<=r. All scalar denominators used in sampled equations have exponent<=L and are nonzero. Expanding exposes exactly g^(-t)q^u h^v with 0<=t,u<=r,0<=v<=D; there are at most (r+1)^2(D+1) frequencies. The available consecutive-equation count supports Vandermonde after grouping numerical aliases. No distinctness of h-nodes is presumed.

## Alias line and formal identity

A nonzero short alias with c=0 would contradict the stated g/q box, including its axis cases. Eliminating h from any two aliases gives g/q exponents bounded by2rD<=m. The box therefore forces both exponents zero. Since each c is nonzero, all alias vectors are rationally collinear. This argument applies to composite orders and arbitrary field characteristic.

The substitution G=x^c,Q=y^c,H=x^(-a)y^(-b), c>0, sends all differences within an actual alias group to zero formal exponents. Merging additional groups is safe because every actual group already has coefficient sum zero. Neither a primitive relation nor division in a finite group algebra is assumed. If there are no nonzero aliases, direct grouped Vandermonde forces all tensor coefficients to vanish; for each t these coefficients are those of the product of a nonzero B_t in the q variable with P_t in the independent h variable, contradicting a nonzero leading polynomial.

## Pole and independent-clock cases

The constants g,q in R_t remain actual scalars; the formal G,Q represent only running powers. At y0^c=q^(-j-r), all lower t denominators are regular. The highest numerator factors reduce to q^L-q^(ell-r), nonzero because L+r-ell is in[L+1,L+r], below ord(q). Its other denominator factors are nonzero. If a!=0, substitution into P_r leaves a nonzero Laurent polynomial in independent x, so the genuine pole cannot cancel. If characteristic divides c, the denominator has higher-order vanishing, which does not remove the pole. If a=0, distinct x^(-ct) powers isolate coefficients; P_r(y^(-b)) is nonzero when b!=0, and P_r(1)!=0 handles b=0. Thus all formal cases are covered.

## Nonvacuity and nominal range

Choosing the largest coefficient FUNCTION nonzero on the h-orbit is essential and correctly stated. A formal polynomial vanishing everywhere on that orbit is vacuous. The proof drops such terms without extending the original k<=L-r range. A nonzero coefficient function has a regular evaluation among j=0,...,D: either those nodes are distinct and polynomial root counting applies, or they cover the full shorter orbit. Shifting loses j<=D equations and leaves at least L-r-D+1, meeting the original nominal-r frequency bound. Smaller effective shift only reduces the number of frequencies and required order margin. The r_eff=0 case is a direct contradiction P0(h^j)A_j=0; no pole argument or invented extra equations is needed.

## Paid application and limits

The all-semiprime setup supplies both local beta/q order margins; the inherited monic square-alias screen uses only that strong-order interface. Its certified mixed differences plus the axes give exactly the required g/q box by sign reversal. Thus the statement is uniformly factor-or-obstruction, fieldwise in both hidden fields, with no prime local orders, balance or new exception deletion. The explicit conditions r<=m,2rD<=m and (r+1)^2(D+1)<=L-r-D+1 hold for all fixed/polylogarithmic r,D eventually; larger parameter regimes are not implicitly excluded.

The first-order result is the report author's immutable predecessor; this review independently checks the new higher-order proof, whose authorship is separate. These are complete finite-stream recurrence representation statements, not operation lower bounds or whole-query algorithms. Multivariate clocks, other transforms, sparse high-degree representations, selected values/convolutions and scalar norms remain outside. No original collision-controller compilation, acquisition improvement or Lean theorem is claimed. All stated scope restrictions are appropriate; no correction requested.
