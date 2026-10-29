# Independent review of the even paired-block readout

26 October 2026. Paper-only review of stable `even-recurrence.md`; no repository edits or tests. **PASS for its formulas and conditional-output scope.** Two presentation clarifications were sent to the author: first-unit-block selection is per factor-size bin, with continued bin attempts after bounded wrong-tag failure; explicit formulas for all c_i do not assert an acquired h-entry list.

## Original-bank parity partition and coverage

The hypothesis is the ORIGINAL one-row-per-unit-j bank, with deterministic identical Gauss choices for j and K−j, not the enlarged completion with repeated colours. The direct map floor(min(j,K−j)/n), n=3^ceil(e/2), has L=K/(2n) blocks. A block is an interval [bn,(b+1)n) of positive representatives below K/2. For each unit square modulo n, its two roots r,n−r have opposite parity, so exactly one representative in that interval is odd. Endpoints are multiples of 3 and not units. Thus each block has exactly one unordered pair for each unit-square tag and phi(n)/2 pairs total.

All actual good-bin hits satisfy j=R modulo n, including nonprimitive rows and axes by the frozen all-content theorem. The block's unique pair with square R² supplies at most one actual orientation hit, because R and −R differ modulo n. Consequently each good block is empty or singleton. This is a genuine partition of the entire original bank; it does not discard signs, axes or carries. Integer bucketing costs soft K.

## Finite Lambert identity and normalization

With rho=q^-1, the coefficients c_i=(-1)^i rho^(i(i+1)/2)[h−1 choose i]_rho give the exact partial fractions in (1). The h=2 normalization reads 1/(1−z)−rho/(1−rho z)=(1−rho)/((1−z)(1−rho z)), confirming the exponent and sign. General residue comparison gives the displayed q-binomial factors. Replacing z by z/(1+delta) and multiplying by (1+delta)^−1 proves (2) with numerator kappa*(1+delta)^(h−1), not a different power.

All coefficients are units by the actual short q-difference screen. Their formulas do not require materializing the h-entry coefficient array. At a single hit, the delta^-1 coefficient is exactly the unit c_I, so good output is (A,A*u*) with A!=0. Empty blocks give (0,0). Repeated row roots, and multiple other-component hits across different rows, do not increase the pole order of the SUM of inverse rows. They can increase the order of the inverse PRODUCT; the report correctly distinguishes them.

Norm/coordinate validation either factors or certifies a legal global denominator. A unit V cannot arise from an empty block at the good field. Thus in the correct bin its first unit block carries the true square tag. Taking both square roots modulo n gives a constant-size candidate palette; complement handles either factor. A wrong bin's unit output may be false, so a bounded HH failure must continue to later bins. One factor-consumer attempt per bin suffices; no globally terminating acceptance of the first arbitrary unit output is licensed.

## Acquired moments and exact AW lowering

The finite q-binomial theorem gives mu_t=(rho^(t+1);rho)_(h−1). Its update ratio (1−rho^(h+t))/(1−rho^(t+1)) and initial mu_0=kappa are correct. A scalar factorial engine acquires mu_0 in soft sqrt(h); only O(sqrt K) subsequent moments are acquired. The stated guarded h+O(sqrt K)<16H range licenses all inverses. The short rational numerator/denominator inputs are acquired by product trees without F′ or node-separation inverses. The report correctly does not extend a short moment identity from polynomials to these singular rational inputs.

For (4), the two length-h paired products share exactly P_(h−1)(c*rho^(1/2),x). Subtracting their two remaining quadratic endpoint factors gives c*rho^(−1/2)(1−rho^h)(x−x^-1). Replacing each constant 1 by 1+delta multiplies that endpoint difference by exactly 1+delta. This proves the division-free identity over B, including collision zeros. The actual square root rho^(1/2)=pi^(−H/2) is supplied by integer powering, not by extracting an unlicensed root.

Substituting c→c*rho^(−1/2) shows that the two required left products share the entire original P_(h−1)(c,x); the remaining factors are endpoints. Thus this executed lowering rule does not acquire its missing long amplitude/pole. The report makes no general AW impossibility claim.

## Completed baseline and cost

The all-row product engine supplies row values and, with constant-rank jets, their first delta derivatives at the same soft K^(5/4) bound. Norm/coordinate classification either factors or leaves every row globally unit/globalzero using the nonsplit field. For a globally zero row each component has exactly one clock zero, so its first derivative is a global unit. Inverting that derivative and multiplying by kappa gives the exact simple-pole coefficient of (2); nonzero rows contribute no negative coefficient. This justifies the fixed-precision baseline without root separation, a growing Hasse degree or inversion of a zero row value.

Ordinary hit flags alone give the normalized whole-bin count/square-tag pair; they need not equal the Lambert-amplitude block values, and the report does not claim that numerical equality. The alternative jet path explicitly acquires the Lambert values. Both preserve the inherited rate. No soft-K simultaneous block-pole evaluator or new factor exponent is obtained.
