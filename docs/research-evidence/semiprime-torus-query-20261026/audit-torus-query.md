# Independent torus-query audit and exact support experiments

26 October 2026. Scratch only. **PASS with an explicit cheap-first scheduling requirement for the conditional soft-K branch.** The sampled support unions do not show the desired collapse. They are measurements, not a universal obstruction or a factoring-success campaign.

## 1. Completeness and literal treatment

Equations (1)–(2) correctly give E=- (R+1)(a+bS) at the own-colour physical witness. This is nonzero as an integer: b!=0 implies |bS|>|a|; b=0 leaves a!=0. Removing a row with a literal zero is legitimate because every other leaf in that row is a certified short q0 gap, and a physical nonzero witness in that row would contradict the same order guard. This proof specifically uses the separately executed q0=W^H short screen.

After removing literal rows, arbitrary extra torus aliases are permitted, provided the new torus-annihilator decoder's preparation and bound are retained. A saturated norm-one leaf is a WHOLE identity even at the split prime. The integer label is retained and nonzero. Neither the former coupled pi order nor a tag/unique-hit claim is needed for this torus-only decoder. T_ext is a once-only soft N^(31/192) operation, not a free step.

Parity, Lucas, quadratic resultant and common order-two recurrence formulas pass direct algebra. They are not independent fast contractions. The common recurrence uses global unit W-W^-1 and actual acquired seeds.

## 2. Prove the variable-window engine, including localization

The source common-length compressed baby/giant engine is [probe_semiprime_sparse_residue_gauss.py:293](/home/dbsanfte/riemann/formal/scripts/probe_semiprime_sparse_residue_gauss.py:293), function _shared_collision, with width approximately sqrt(number_of_rows*window_length), common baby polynomial, monic evaluation and exact truncated tails. Its parameters use different names from this packet. The frozen [pure-weighted-common-tag.md §2](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-fused-readout-20261026/pure-weighted-common-tag.md:25) supplies the actual weighted lattice and phase bank.

Decompose each merged integer interval into at most O(log U) disjoint power-of-two pieces, where U is the largest length; the pieces need not preserve its original clock alignment because their actual starting group powers are acquired by binary powering. Let c_r pieces have length 2^r. Total pieces C'=O(C_union log U), and sum_r c_r*2^r=S_union exactly. Batch equal lengths. The common-length monic engine costs

 soft(c_r+sqrt(c_r*2^r))

for each r, with a constant-rank norm-one coefficient algebra. Summation and Cauchy–Schwarz give

 soft(C'+sqrt((number_of_levels)*S_union))
   =soft(C_union+sqrt(S_union)).

Here log U=O(log N), including merged intervals longer than h. No unit q-factorial denominators or order >U are required by the monic engine. Starts are units because they are powers of W. Nonunit products localize inside the actual unpadded pieces; child reevaluation costs a logarithmic multiple of the same bound. A selected label belongs to an original retained support interval even if its row multiplicity was discarded. The nonzero integer exponent and annihilator decoder remain available. Thus the bound in §5 is valid; it is not merely inferred from S_union without accounting for differing lengths.

**Required operational clarification:** acquire union metadata for ALL public bins first, in soft K total. Execute only bins satisfying S_union<=K² times the chosen polylog threshold in a first pass. If a correct bin qualifies, this first pass factors in soft K. Only after it fails should expensive bins/fallback be executed. Processing expensive wrong bins first would invalidate the statement that existence of one cheap correct bin implies a soft-K entire execution. This is a scheduling condition, not a coverage theorem.

## 3. Reproducible exact structural experiment

Script: [check_support_union.py](check_support_union.py). Machine-readable full rows: [support-union.json](support-union.json), and CSV: [support-union.csv](support-union.csv).

The existing exact Gauss code was located first in [probe_semiprime_sparse_residue_gauss.py:65](/home/dbsanfte/riemann/formal/scripts/probe_semiprime_sparse_residue_gauss.py:65), using nearest integer with ties down. That older function has a different lattice. The scratch script adapts that exact rank-two reduction convention to the ACTUAL lattice (K B²,0),(s B²,N), s=[N j^-2]_K. It certifies congruence and the exact squared Hermite inequality, constructs D_j,t_j,ell_j by the frozen formulas, filters literal rows, and merges integer intervals by exact residue modulo H. No floating point enters Gauss, phases, merging, counts or coverage assertions. Floating point is used only to display sqrt(S_union)/K and ratios.

Fixtures: e=3,...,9; two shapes P near 0.55 K³ or 0.75 K³, Q chosen so PQ is near 0.70 K^6. Known fixture primes are acquired by deterministic 64-bit Miller–Rabin, all below 2^64. Each satisfies P<Q, N<=K^6 and P>16H. We sample dyadic factor-size bins from the hard-branch lower size through sqrt N and also the complementary-factor bin. These are 116 bank/bin measurements, not every possible bin or every semiprime. The script explicitly certifies the own-colour physical integer index lies inside the clock and has nonzero torus label in either sampled correct-factor bin. No W, group orders or factor extraction are computed; these are structural native-bank experiments, not prepared-group factoring tests.

| e | K | sampled bins/shapes | min S_union/(Jh), all samples | max S_union/(Jh) | sqrt(S_union)/K range, correct-factor bins |
|---|---:|---:|---:|---:|---:|
|3|54|8|0.888889|1|3.82254–3.82254|
|4|162|10|0.888889|1|5.02522–5.12885|
|5|486|14|0.876543|1|6.56636–6.61245|
|6|1458|16|0.876543|1|8.64148–8.72224|
|7|4374|20|0.876543|1|11.37276–11.39054|
|8|13122|22|0.877000|1|14.99078–15.02971|
|9|39366|26|0.878677|1|19.72384–19.72726|

The literal filter removes at most one row in these samples. The machine-readable table retains J,h,C_union, distinct residue count,S_union,Jh, original J, removed and axis counts, and separate correct-P/Q-bin flags. End-to-end run was under ten seconds in this environment; no support leaves were enumerated.

This experiment finds approximately constant-factor mass savings, not a soft-K acquisition bound. The rising normalized sqrt mass is consistent with retaining the old K^(5/4) scale on these fixtures. It proves no asymptotic family lower bound, no universal failure of arithmetic union collapse, and no obstruction to another torus contraction.

## 4. Inversion-fold experiment and normalization correction

Extended the same stable script and both machine-readable tables with S_inv,C_inv,S_inv/S_union and sqrt(S_inv)/K. For s>H/2, interval [a,b] maps to residue H-s and [-b-1,-a-1]. At s=0 the script uses u->|u| (zero is certified absent); at s=H/2 it splits negative/nonnegative parts and uses u->max(u,-u-1). These are exact interval operations, not leaf enumeration. Every one of the 116 fixtures checks S_union<=2*S_inv and S_inv<=S_union. Final replay took 8.38 seconds.

|e|min S_inv/S_union, all bins|max ratio|bins with strict gain|
|---|---:|---:|---:|
|3|1|1|0|
|4|0.754717|1|3|
|5|0.751553|1|6|
|6|0.750515|1|5|
|7|0.750172|1|10|
|8|0.750057|1|10|
|9|0.750019|1|14|

Every sampled correct-P or correct-Q bin has S_inv=S_union: inversion gives NO further saving on these particular correct bins. Wrong-bin gains approach a factor 4/3 in support, which does not imply a new rate. This is fixture evidence only; it is not a proof that correct native bins never benefit. The all-bin cheap-first rule should use S_inv after this enhancement.

Also corrected joint-lambert.md §§2–3 to carry the exact normalized pullback T_j^-1*C((1+delta)/T_j), and the identical factor on its Padé/error terms. The change of variable contributes T_j, canceled by T_j^-1, so the native delta residue remains exactly c_I. No claim about raw unnormalized pulled-back residues remains.

Final reproducibility additions: the script defaults to max-e=9, emits CSV beside JSON itself, asserts every primality-test candidate is below 2^64, asserts |a|,|b|<=K, and checks f'_j(j)=0 modulo K. Exact reproduction command (the fixture limit is structural, not a factoring benchmark):

```sh
python3 check_support_union.py --max-e 9 --output support-union.json
```
