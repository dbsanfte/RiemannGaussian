# Independent review: one unnormalized even moment suffices

26 October 2026. Paper audit, no repository edits or numerical tests. **PASS.** The first, second or third moment of the canonical squared colour is individually a sufficient acquired scalar, with a different divisor-palette consumer. This weakens the output requirement again; no faster acquisition is proved.

## 1. Integer size and component recovery

Use the ORIGINAL beta-coupled/pi bank and correct-bin common tag, not the raw torus-only bank or a completed catalogue. Write n=3^ceil(e/2), D0=3^floor(e/2), K=2nD0, e>=3. Let p be ONE fixed exponent in {1,2,3}, to avoid confusing it with the HH interval parameter. Define

 U_p=[delta^-1]sum_(j,i) [j²]_n^p/(delta+1-T_j rho^i).

At the correct nonsplit prime R it equals the positive integer c=d*u^p, with 1<=d<=D0 and 1<=u<n a unit square. Set M_p=D0*n^p=(K/2)*n^(p-1). Then

 0<c<M_p,    M_p<=3K²/4<16H<R.

The last bound uses n²<=3K/2 and p<=3; it holds throughout the native e>=3 range. Thus coordinate classification and the previous blocked integer recovery work without good-prime wraparound. If the tau coordinate has proper gcd, factor; gcd one can reject only a wrong bin; gcd N certifies a globally scalar value. A canonical scalar c0<M_p must equal c at the good bin. Otherwise monic blocks of width ceil(sqrt M_p) search the differences. Padding remains below 4M_p<16H<P,Q, and a flagged saturated block can be inspected at O(sqrt M_p) cost. At most one such block is inspected. Total soft sqrt M_p<=soft K.

This remains valid when the nonsplit R is the LARGER factor: both primes exceed 16H. Wrong bins may give no recovered integer or a misleading small integer, but the following candidate and factor checks are bounded; they cannot cause an unchecked output. Continue after a failed wrong-bin attempt.

## 2. Fully acquired divisor palette

Reject a recovered candidate unless 1<=c<M_p; in particular a wrong-bin zero is rejected before integer factorization. Factor the recovered actual integer c by trial division through floor(sqrt c)<=K. This is soft K bit work, not factorization of N or an oracle. Enumerate all positive divisors v of c. Keep v only when it is a perfect p-th power u^p with 1<=u<n and 1<=c/v<=D0. Test that u is a unit square modulo the public 3-power n. Each retained u has exactly two public Hensel roots +/-r modulo n; acquire them and their complementary factor residues N/r modulo n. Deduplicate the palette.

There are at most S<=4*tau(c) candidates, and the true u is retained in the correct bin because v=u^p divides c. Its roots contain R mod n; complementing includes the smaller factor P even if R=Q. This requires ONE restricted-HH call on the WHOLE palette, not one call for each divisor. No actual modular alias is used as a factor tag: the covering candidate has provenance from the common-tag theorem and the integer factorization of c.

Output acquisition itself fits soft K: tau(c)<=2sqrt c<=2K, integer fixed-power tests and public Hensel lifting cost polylog N per candidate.

## 3. Explicit constants and a finite-safe HH parameter

The standard divisor bound with epsilon=1/12 gives tau(c)<=C_tau*c^(1/12)<=C_tau*K^(1/6). It can be made entirely explicit. For primes l>=4096 and a>=1, a+1<=2^a<=l^(a/12). For smaller primes, (a+1)l^(-a/12) is bounded by the convergent sum (1-l^(-1/12))^-2<324 (using 2^(-1/12)<17/18). Hence the deliberately loose integer constant

 C_tau=324^4096

works for all c>=1. No input-dependent finite exception is hidden. Thus S/n<=4sqrt(2)C_tau*K^(-1/3); use the rational upper constant C*=8C_tau if desired.

One can avoid putting this huge proof constant into the ACTUAL algorithm. Let A=ceil(K^(4/3)), computed as the integer ceiling cube root of K^4, and choose the HH interval parameter

 t_HH=ceil(16*A/n).

Then n*t_HH>=16K^(4/3), so the source baby alphabet has fewer than K elements under the inherited K>16 guard. Also

 S*t_HH<=16*A*S/n+S=O(K)

by the explicit bound above, with an absolute constant. t_HH=O(K^(5/6)) has O(log N) bits and satisfies the source polynomial-height parameter bound even at the smallest prepared K=54. Thus no huge-constant parameter overflow or unjustified finite-K order assumption occurs. The actual density-adjusted restricted-HH formula gives soft O(K) for its single palette call. This formulation is an alternative to the equivalent t_HH=ceil(16*C* K/S) asymptotic proof choice, whose finite parameter-height guard would otherwise need attention.

The base alpha=beta^(n²) has each local order at least that of beta^H because n² divides H. The inherited global-match deletion, exact quadratic recovery, and saturated localization contract therefore applies unchanged, irrespective of the balance between P and Q. No new order supplier is assumed.

## 4. Scope and prior credit

The restricted-HH palette cost and complement operation are already proved in [axis-supplier README §1](../semiprime-axis-supplier-20261026/README.md) and [review-restricted-residue.md](../semiprime-axis-supplier-20261026/review-restricted-residue.md). Public integer recovery is the packed-consumer construction, now with the bound M_p. The epsilon divisor-palette technique also has prior use in the axis-supplier retrospective provenance/sector menus. A targeted evidence search found no previous formulation of this specific c=d*u^p divisor decoding; that limited search is not a novelty claim.

The consequence is precise: U_1 ALONE suffices, as do U_2 or U_3 ALONE, because loss of the count d can be absorbed into a short public divisor palette. The stronger packed scalar dL+du or ratio (d,du) is unnecessary for this consumer. Canonical integer weights remain essential. Neither a generic Lambert unit-amplitude residue nor a raw-torus hit automatically has the form d*u^p, so the theorem cannot be transferred to those inputs without another proof. Acquisition of any U_p in soft K remains open.
