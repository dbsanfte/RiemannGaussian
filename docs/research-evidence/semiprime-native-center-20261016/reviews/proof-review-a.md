# Independent adversarial review: origin-robust Euclidean carrier energy

2026-10-16. Reviewer q_product_literature_615. Verdict: PASS. No mathematical correction requested. Full exact-byte source/proof review, with no experiments, examples, builds or proof edits.

Target `report.md`: 15784 bytes, SHA256 2e9eef8c4ba33e53fc5ae822483a2d6d524dfb8d46ff02eeb73209f2a88aea1d.
Metadata `source-pins.json`: 1914 bytes, SHA256 6b75e6e2a4f6f0c39ededd3ab0ba3cb581152a67759a88dc594bf549d8b11848.
All EIGHT listed source files independently match exact bytes and hashes. Read the actual lowerSum/upperSum/publicShift/reflectedShift definitions and the inherited native source budget/invariant. Historical prime supply, literal base projection and selector bounds are inherited, not newly reproved here.

## Low-digit source and the new factor-residue count

The deduplicated full pair catalog and deterministic light-tag selection depend only on m,n=N modm. The existing total packet budget gives at least 2m/3 light tags and at most C=64L_m⁴ rows at each, all with nonzero signed |a|<m and 1<=t<m. Weighted cone energy <=4C⁴m^(5/2) legitimately includes repeated field points across color classes.

The factor-digit change of coordinates is exact, including the low-product and low-sum carry constants. At fixed canonical p,q and p!=q, its matrix [[q,p],[1,1]] has nonzero determinant and hence maps (U,V) bijectively to (h_N,h_S). The phase high-digit linear form has precisely coefficient Delta t on h_S and -Delta u/n on h_N, since t/j=u/n. The report now states that coordinate order explicitly. Choices of origins or policies are absent from this raw count.

Independently checked all three cases. If Delta t!=0 modulo m, the low equation fixes s, hence at most two p via p²-(s+1)p+n, and the high equation has exactly m solutions: <=2mR⁴. If Delta t=0 but Delta u!=0, projection to (t,a-2u) has at most four catalog entries per fiber. The monic u quadratic gives at most two u; a,j are then fixed modulo m, and a has at most two signed representatives, with t's representative unique. Deduplication removes any derivation-label ambiguity. Thus <=4R³ relevant quadruples, at most m low p and m high pairs: <=4m²R³. If both vanish, the low equation also forces Delta a=0 and cone energy bounds the weighted quadruples, with at most m³ factor-digit choices: <=4C⁴m^(11/2). No assumption that the remaining high constant vanishes is used. Their sum is <=10C⁴m^(11/2) at each n, and <=10C⁴m^(13/2) overall. Markov therefore gives at most 10m⁴/lambda bad ordered factor-residue pairs. This genuinely differs from the earlier integer-t-sum/high-product-digit argument.

## Exact native-center calculation and no-wrap

Read the native formulas directly. Adding the two signed endpoints in publicShift gives 2ell+2a*A_N+2t*B_N; the sign-dependent endpoints interchange but their SUM is unchanged. ReflectedShift interchanges A_N and B_N. Native integer division by the positive denominator is floor division even for a negative numerator, so rounding supplies e with |e|<=d/2 and

 d*k=ell+a*alpha+t*beta+e.

Substitution into tS+delta-dk cancels the complete centered b contribution, leaving t(S-beta)+a(1-alpha)-e. The exact half-integer interpretation and the integer N/2 inside Nat.sqrt are correctly distinguished.

For N>=4, alpha,beta lie in [1,(3/2)sqrt N]. Euler's S=P+Q-1>=2sqrt N-1 implies S-beta>=0. With S<=3m³ and signed |a|,t<m, the stated common phase interval [-(3/2)m⁴-d/2,(9/2)m⁴+d/2] follows. Its pair-sum difference bound is 12m⁴+2d<16m⁴<D. Thus every equal-product quadruple gives EXACT integer phase equality and hence the raw congruence modulo d, with no integer t-sum equality or local-field no-wrap assertion. Mixed public/reflected choices satisfy the SAME interval, so native center choice really is covered uniformly. A full packet-union cover uses one chosen entry/center per light tag as witness; it does not assume both center copies were included in the raw energy count.

## Original-supply transfer and multiplicities

For each m, fixing P modm² leaves O(M) integer P lifts in the original range. Each half-open width-m² Q selector box has at most one integer per prescribed Q residue. Applying the NEW ordered factor-residue bound gives O(M(G_m+1)m⁴/lambda), which sums to O(K_*M⁶/lambda). The proof does not substitute an N-residue count or use prime equidistribution. The excluded p=q case contributes O(K_*M⁵): at fixed P a box contains at most m Q congruent to P modulo m. All of these are absolute deletions against the same original qualified supply. Polylog and polynomial-menu parameter specializations, and union with separately charged negligible old losses, are correct.

Selected light tag count g>=2m/3 is a LABEL count, not a distinct-target count. Equal values are retained with multiplicity. Assigning labeled indices to covering progressions keeps internal quadruple classes disjoint, even if their values overlap. Weighted Cauchy--Schwarz gives E>=sum g_i⁴/(2T_i), and Holder gives the stated k²T bound (the constant162 is conservative). Therefore the cover of a complete selected family or full multicenter union is obstructed by the witness, without claiming bounded energy for that entire untrimmed union. No collision coverage after trimming is inferred.

## Arbitrary-origin wrap penalty

For ONE origin per retained source entry and range H, the unwrapped effective phase span is bounded by V=(m-2)S+6d+dH. A common arbitrarily large origin cancels. An equal-product quadruple has signed difference ell D with |ell|<=floor(2V/D), so at most W=2floor(2V/D)+1 possible wrap integers need be counted.

For each ell, reducing modulo d places the corresponding selected labeled quadruples inside an off-zero CATALOG congruence count. Pair-sum correlation E_c=sum_x r(x)r(x-c)<=sum_x r(x)²=E_mod by Cauchy--Schwarz. This argument remains valid with repeated phase values, advice-dependent origins, and repeated ell residues; the latter only overcounts. Hence E_global<=W E_mod is justified. Multiple origin copies would destroy the one-entry injection unless separately charged; the report explicitly excludes that inference.

The bound W=O(1+dH/D) follows from S<=3m³,D>16m⁴. For polylogarithmic lambda,C and progression count, total softly linear T forces W>=m^(1/2)/polylogm and hence H>=D/(m^(3/2)polylogm) eventually. This yields m^(5/2)/polylogm from the weaker order promise and m^2.562/polylogm from the inherited stronger actual order. The span requirement is not a bit-cost lower bound: large origins can have short encodings, which is expressly acknowledged. The special native centers use their sharper cancellation envelope to get W=1; their large relative span is not wrongly inserted into a restrictive small-H hypothesis.

The new source-specific arithmetic result handles the previously open native-center choices and quantifies a genuine arbitrary-origin escape penalty. It remains a representation obstruction on the stated retained majority, not an all-input algorithm, universal acquisition lower bound, local-field energy theorem, or new Lean declaration. Tiny tag subsets, other source redesigns, highly shared/non-cover computations and implicit norm evaluators remain open. The report preserves these limits and the unfinished main-query status accurately.
