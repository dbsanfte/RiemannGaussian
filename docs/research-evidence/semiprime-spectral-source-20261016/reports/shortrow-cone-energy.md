# The selected short Euclidean rows also resist small geometric carriers

2026-10-16. A new actual-source carrier obstruction for the literal per-tag short-row family. This is not the already known shrunken-rectangle upper bound or the old linear-center coverage failure. It proves no arithmetic-operation lower bound and supplies no improved query evaluator.

## 1. Literal short-row contract

Let m be an odd prime, n=N mod m nonzero. At each tag 1<=j<m choose the literal publicRow short pair (a_j,t_j). Its choice depends only on (m,n,j), not the second input digit. Native publicRow_correct gives

 0<|a_j|<=sqrt(m),  1<=t_j<=sqrt(m),
 a_j j^2=n t_j mod m.

Retain its exact lift b_j=centered(-j^(-1)(N t_j-a_j j^2)/m mod m), delta_j=a_j+m b_j-2a_j j, and target z_j=gamma^(-N t_j-delta_j). The signed a_j is not replaced by its absolute value. Here delta span is O(m²), uniformly, and for N_h=n+mh,

 delta_j(h)=delta_j(0)-m t_j j^(-1)h mod m².       (1)

No arbitrary high-digit-dependent redesign of the chosen pair is admitted by this theorem. The native Euclidean selection satisfies the contract. The historical all-Euclidean report already excludes the paid O(m)-width rectangle/stationary/cancellation centers; no such old result is claimed anew here.

## 2. An elementary cone-energy lemma

In F_m³ put Q(a,t,u)=u²-nat, and let

 A={ (a_j,t_j,a_j j):1<=j<m }.

Every point is on Q=0. The points are distinct and have distinct cone-generator directions: u/a=j. In fact no affine line contains three points of A. For distinct j,k, Q evaluated on the affine line between their points is

 Q((1-s)A_j+s A_k)=-s(1-s)a_j a_k(j-k)²,

nonzero except s=0,1. Thus A is a cap, even though a,t vary and no Sidon identity is asserted.

Its additive energy satisfies

 E(A)<=4|A|^(5/2)<=4m^(5/2).                     (2)

Here is a self-contained incidence proof, avoiding any imported point-plane theorem. Let B be the nondegenerate polar bilinear form of Q. An additive quadruple x+y=z+w on Q=0 implies B(x-z,y-z)=0. The triples with x=z or y=z contribute at most 2|A|². Fix z and exclude those degeneracies. Capness makes the directions [x-z] distinct projective points in P². Nondegeneracy of B makes the orthogonal conditions B(v,y-z)=0 distinct projective lines as y varies. For N=|A|-1 points and N lines, any two points lie on at most one listed line. If I is their incidence count, Cauchy--Schwarz gives I²/N<=N(N-1)+I, hence I<=N^(3/2)+N. Sum over z and add the degenerate triples to obtain E(A)<=|A|^(5/2)+3|A|²<=4|A|^(5/2). The fourth vertex need only be counted when it belongs to A; counting all such right-angle triples is a valid upper bound.

## 3. Average raw short-row energy over the high digit

Define Eshort(n,h) as the number of ordered TAG quadruples satisfying BOTH

 t_1+t_2=t_3+t_4 as INTEGERS,
 delta_1(h)+delta_2(h)=delta_3(h)+delta_4(h) mod m².

Then

 sum_(h=0)^(m-1) Eshort(n,h)<=6m^(7/2).           (3)

To prove this, first impose the low delta equation. There are at most 2(m-1)³ qualifying quadruples with the integer t-sum constraint: fix three tags, so t_4 and the required low delta value c are fixed. A possible fourth tag satisfies

 c j_4²+2n t_4 j_4-n t_4=0 mod m.

If its selected t_4 exists it is a nonzero field element. This polynomial has at most two roots, including when c=0 because its linear coefficient remains nonzero.

For any such quadruple with nonzero signed slope sum t_j/j modulo m, (1) permits at most one h. For zero signed slope, use t_j/j=a_j j/n modulo m: the signed sum of a_j j is zero. The low delta equation delta_j=a_j-2a_j j modulo m then gives a zero signed sum of a_j as well. Along with the t-sum constraint these are exactly additive quadruples of A. Their count is at most (2), and they can contribute for at most m high digits. Hence the total is at most 2m³+4m^(7/2)<=6m^(7/2). Raw tags, signs and the full centered lift are retained throughout.

For lambda>=1, at most 6m/lambda high digits per n, and at most 6m²/lambda coprime residues N modulo m², have Eshort>lambda m^(5/2). This bound does not assume a distribution of the centered carries.

## 4. Transfer to actual global targets and the original supply

On the inherited balanced large-order supply put S=P+Q-1. The actual global gamma order D divides (P-1)(Q-1), and D>16m⁴. Thus N=S mod D, with S=Theta(m³). Effective target phases are t_j S+delta_j. Their span is O(m^(7/2)), so pair-sum differences are smaller than D eventually. Their delta span is O(m²), also smaller than S/2 eventually. Therefore a global target product equality first gives the exact integer equation

 (t_1+t_2-t_3-t_4)S+(delta_1+delta_2-delta_3-delta_4)=0,

then forces the integer t sums equal and the delta sums equal. Consequently deduplicated GLOBAL multiplicative energy is bounded by Eshort. No individual local-field order of this size is asserted.

The global targets have multiplicity at most two among tags: equal targets force equal integer t and delta; for fixed t and low delta the fourth-tag quadratic above has at most two solutions. Hence the distinct target count J is at least (m-1)/2, and in particular J>=m/3 for m>=3.

Use the same original order-qualified prime-pair supply, candidate envelope K_*, and existing selector strips. At fixed P,m, width-m² Q boxes give at most one Q per bad product residue, because P is invertible modulo m². There are O(G_m+1) boxes and sum_m(G_m+1)=O(K_*M). Summing O(m²/lambda) bad residues over boxes and O(M³) integer P gives the absolute loss

 O(K_* M^6/lambda).                              (4)

This is measured against the SAME original Omega(M^6/log² M) supply. If lambda/(K_*log²M) tends to infinity, its union with all earlier soft O(M^5.994) losses is negligible. The surviving actual majority family has E_times(Z)<=lambda m^(5/2) simultaneously at EVERY current candidate m.

## 5. Exact geometric-carrier consequence

On that retained family, ANY cover by k finite ambient geometric progressions of total listed length T satisfies

 k²T>=J⁴/(2E_times(Z))>=m^(3/2)/(162lambda).       (5)

Indeed partition distinct targets among progressions and apply the same energy/Holder bound; each assigned productset has at most 2T_i-1 elements. Starts and ratios may be fully input-dependent or privately advised, with holes, repeats, overlap, outside-subgroup ratios and cyclic wraparound. No union over descriptions is required. Any containing finite carrier C also satisfies |CC|>=m^(3/2)/(81lambda).

For a polylogarithmic candidate envelope take lambda=K_*log⁴M. Then k²T is soft Omega(m^(3/2)). In particular polylogarithmically many progressions cannot have total nearlinear length. For the larger frozen K_*=O(M^.020), taking the candidate-scale threshold lambda_m=m^.04 gives loss O(M^5.980), since m is comparable to M, and the explicit tradeoff k²T>=m^1.46/162. This is weaker than the denominator-one carrier bound but applies to the DIFFERENT, actual short Euclidean source.

No nearlinear acquisition follows from shrinking row lengths to O(m^(3/2)); nor does this proof exclude every way to share those rows. Large high-productset carriers, many progressions with shared operations, fixed-payload cancellations, scalar norms and other factor-selective algorithms remain open. Restricting to subsets may alter the geometry and coverage. This theorem concerns one low-digit-dependent short row per original tag, not all intermediate rays at once or arbitrary high-digit-adaptive ray choices. No native file, frozen packet or backend was edited; no build, example accumulation or full-clock improvement is claimed.
