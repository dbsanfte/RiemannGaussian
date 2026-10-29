# Independent review: mixed-trace.md

26 October 2026. Read-only paper review; no numerical tests or repository edits. Main identities and initialized rank-two cost pass. The Section 5 coverage-scope correction described below has been incorporated into the scratch report at the parent's request.

## Common coordinates and native promise: pass

The exponent differences proving gamma=beta^((P+Q)/2), delta=A^-1 mod P, and delta=A mod Q are exactly the printed integer multiples of P-1 and Q-1. No division modulo an unknown order or square-root choice is involved. Consequently delta+delta^-1=A+A^-1 globally.

For s=a+b,d=a-b, u=gamma^s beta^lambda,

    u*delta^d=beta^(aP+bQ+lambda)=q^I

at an ACTUAL stationary row with its chosen canonical stationary lambda. Its two public roots are u*A^-d=beta^(a+bN+lambda), u*A^d=beta^(b+aN+lambda), with the stated orientation. The saturated A/pair-difference screens give the short nonzero exponent N-1 or d*(N-1) when d!=0 and may use the licensed consumer. Diagonals require their separately stated handling.

Half-pair coverage is correctly an OR of GLOBAL equalities at the guaranteed stationary pair: if the half-list stores that representative, H(q^I,delta)=0; if it stores its swap, H(q^I,delta^-1)=0. The same list index's factor vanishes at both primes. This is stronger than an arbitrary local-hit assertion and follows from the original stationary two-prime theorem. An arbitrary local hit, or global zero of the scalar norm alone, does NOT imply either H orientation is globally zero; its two CRT components may be split between orientations or rows. The report's Section 3 conditional phrase “if this is the witnessed equation” must retain precisely that distinction.

## Split algebra, norm, and second equation: pass

The monic rank-two algebra has basis 1,D, D^-1=t-D, and split evaluations separated by the guarded unit. Product-tree acquisition in that algebra costs soft J. The norm is

    (h0+h1*D)(h0+h1*D^-1)=h0²+t*h0*h1+h1²,

with the signs printed in Eq. (4). A complete swap-closed row product is invariant and therefore has zero D coefficient. This statement is about the complete product, not an asymmetric subset. Constant algebra rank does not acquire the long clock norm.

If an acquired reduced relation c*delta+e=0 is guaranteed globally, its values at A and A^-1 give a proper gcd unless both vanish globally, in which case unit separation gives c=e=0. A unit c recovers the actual mixed delta and hence factors. No selecting equation has been acquired merely by defining H(q^i,D), and no arbitrary additive saturated zero is passed to the exponent decoder. These qualifications are correctly retained.

## Nonabelian and conic identities: pass

For U=diag(delta,delta^-1), V=[[1,1],[1,2]], one obtains z=delta+2delta^-1 and tr[U,V]=6-t². Fricke gives exactly

    z²-3*t*z+2*t²+1=0.

The two roots A+2A^-1 and A^-1+2A have difference plus or minus (A-A^-1), a unit. It is a lawful symmetric quadratic for an unknown mixed value, not an acquired orientation-selecting coordinate. The framed companion-matrix warning is appropriate.

Since s²-d²=4ab, Eq. (6) has the correct H*c_j and q^c_j normalization, and beta^N=gamma*A. Equation (7) is the correct stronger stationary integer identity. Also gamma^d delta^s=beta^(aP-bQ). Squaring that unknown exponent is not supplied by multiplying its already-known formal group expression; the report correctly leaves the nonlinear acquisition unproved.

## Incorporated Section 5 scope correction

“Keeping all lambda roots is still necessary for the current coverage proof” must mean **the inherited full-list coverage proof used in this report**, not mathematical necessity or a claim that no selected-root coverage family has been proved. The parallel color/weighted-Gauss construction in farey-query.md supplies a SEPARATE acquired selected-root family: one canonical linear lambda_j for each acquired color/vector and scale, with its explicit horizon M' and deletion ledger. This does not change the norm cost or supply the adaptive second equation here, but it supersedes an unconditional claim that all phase roots are required.

Likewise the outcome's “no justified lambda pruning” should read “this mixed-trace calculation itself supplies no justified lambda pruning.” No counterexample to the independent color-family proof is asserted.

## Parallel farey-source/count checks

The explicit determinant-one triple in farey-query.md has phase counts 12,12,4 for sufficiently large stated k, because the first two abN values have 3-adic valuation two and the last is a unit square. The report already says only existence and explicitly excludes the erroneous four-lift claim for the first two rows.

The author's scratch was also corrected after the parent's primary-source check: EMS Theorem 4.4's equal-parameter constant is 2*(alpha+alpha^-1)^2, not generally 8; only the parabolic constant-8 specialization is used. The public horizon satisfies 2M'+1<=8*k^(3/2)+7<16k² already for k>16.

No complete-query gain follows from this report, and none should be counted. The Section 5 qualification is now incorporated; this is a correct initialized common-orientation audit.
