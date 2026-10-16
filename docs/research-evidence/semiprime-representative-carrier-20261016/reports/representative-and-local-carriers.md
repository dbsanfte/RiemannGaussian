# One representative relation excludes local carrier plans using four input digits

2026-10-16. New classical tightening of the carrier-plan argument. A successful cover annihilates every pair/triple relation, so one may select ONE prescribed nonzero relation rather than union over O(m) of them. The counting ingredients and the source energy lemma are inherited. This is a stronger specified-representation obstruction, not a new acquisition clock or an operation lower bound.

## 1. Source and precise plan contract

Use the SAME original balanced, order-qualified prime-pair supply P,Q=Theta(M³), N=PQ, of size Omega(M⁶/log²M). At each current auxiliary prime m=Theta(M), let d=m² and use the literal public projected gamma. Its local orders are distinct primes

 R_P>P^.677>=c M^2.031,  R_Q>Q^.677>=c M^2.031.

In particular P=1+vR_P and Q=1+wR_Q for positive v,w<=C M^.969. All these order/factor statements are proof-side qualifications of the actual source, not algorithm inputs.

At every tag 1<=j<m the canonical first current has

 a_j=N j^(-2) mod m, with 1<=a_j<m,
 D_j=(N-a_j j²)/m,
 b_j=centered(m,-j^(-1)D_j),
 delta_j=a_j+m b_j-2a_jj.

The exact delta_j is periodic in N modulo m². Every native publicPairs stream contains this first current. On g>=2m/3 deterministically light tags, the inherited native-center theorem gives the labeled raw bound

 E_raw=#{delta_1+delta_2=delta_3+delta_4 modulo m²}
       <=E_*=m^.04 C_m^4 m^(5/2),
 C_m=64(floor(log₂m)+1)^4.                                             (1)

This holds simultaneously at CURRENT candidates on a retained majority of the original supply, before any plan is chosen. It uses the previously counted O(M^5.980) energy exceptions, O(M^5.020) singular exceptions, and inherited soft O(M^5.994) losses. It is not asserted at every comparable m. Enumeration over all comparable m below is only a counting overestimate.

Fix an integer r>=2, independent of M. For each comparable m and residue h in [0,m^r), m not dividing h, prescribe at most B(M) plans. Their metadata is fixed as N varies subject to N=h modulo m^r. Each plan supplies an integer origin k_j, a carrier assignment i(j), integer positions 0<=s_j<T_{i(j)}, and lengths T_i. All integers have uniformly polylogarithmic bit length, and with k the number of nonempty carriers and T=sum_i T_i, require

 k²T<=M(log M)^A                                                     (2)

for a fixed A. Numerical origins may be arbitrarily large within the encoding bound. Full-input or factor advice may select among the prescribed plans and may supply all carrier seeds/ratios.

There are two distinct success contracts:

- LOCAL-P: units c_i,rho_i in F_P satisfy gamma^(-N-delta_j+d k_j)=c_i rho_i^(s_j) on every tag. LOCAL-Q is defined independently over F_Q, with entirely different seeds/ratios permitted.
- GLOBAL: the same equations hold in (Z/NZ)^units. This forces both local orders to divide every elimination relation.

The conclusions below concern a cover of the full first-current family, or any supplied cover including its full light-tag witness. No collision completeness of the light subset is assumed. A tiny privately selected tag family is outside the conclusion.

## 2. Statements

The number of original retained pairs where some plan succeeds LOCALLY in EITHER hidden field at some CURRENT candidate is at most

 soft O(B(M) [M^4.969+M^(r+1.969)]).                                  (3)

For GLOBAL success the stronger bound is

 soft O(B(M) M^(r+1.969)).                                            (4)

The implicit polylogarithms are uniform over all prescribed plans under the fixed metadata encoding bounds. There is no additional candidate-menu factor: all O(M) comparable integers m are counted.

Consequently each of the following success losses is negligible against Omega(M⁶/log²M):

- LOCAL, r=4 and B polylogarithmic: soft O(M^5.969).
- LOCAL, r=3 and B<=M: soft O(M^5.969).
- LOCAL, r=2 and B<=M: soft O(M^5.969).
- GLOBAL, r=2 and B<=M²: soft O(M^5.969).

The last case also covers a deterministic plan depending on N modulo m⁴ by treating its two additional digits as O(m²) choices above a fixed residue modulo m². The direct local four-digit assertion is stronger than that global interpretation. After unioning the indicated success loss with the inherited exceptions on the SAME original supply, a majority family remains for which no permitted plan works in either field (in the local cases), simultaneously at every current candidate.

These are asymptotic statements for sufficiently large M. For larger r or libraries the formulas remain valid but need not give a negligible exceptional set.

## 3. Select a single representative before inspecting further digits

For a plan, restrict to the light tags, whose labels are determined by h modulo m. Set f_j=-delta_j+d k_j. For each assigned carrier choose a base tag 0 by increasing tag order. Retain equal-position differences f_j-f_0 when s_j=s_0. If a distinct position exists, choose the first such tag 1 and retain all anchored relations

 K_j=(s_1-s_0)(f_j-f_0)-(s_j-s_0)(f_1-f_0).                            (5)

Use a fixed ordering of these at most 2g candidates. They are integers depending only on (m,h,plan): delta_j depends only on h modulo m², while the common -N in the actual exponent cancels. Their bit lengths are polylogarithmic in M.

If all candidates were zero, equal labels would have equal f, and each carrier's f_j would be rational-affine in s_j. A group with g_i labeled entries then has at most 2T_i-1 integer pair sums. Weighted Cauchy--Schwarz and Hölder give

 E_integer>=sum_i g_i^4/(2T_i)>=g⁴/(2k²T).

On the other hand integer f-sum equality implies the delta congruence in (1), for arbitrary origins, so E_integer<=E_*. This contradicts (2), since g>=2m/3 and

 g⁴/(2E_*)>=c m^1.46/(log m)^O(1)>M(log M)^A

eventually. Repeated target values are kept as labeled entries, so no distinct-target lower bound is used.

Therefore on every successful retained input at a current candidate the candidate list contains a nonzero integer. Define K(m,h,plan) as its FIRST nonzero member. If a formal plan has an entirely zero list, assign it no representative; it cannot succeed on the retained energy family. Finding the representative costs O(m) arithmetic tests, but COUNTING requires only this one integer, not O(m) possible annihilators.

For a local cover, divide its equations by the base equation and take opposite integer powers. The carrier seed and ratio cancel, so gamma^K=1 in that field. Thus LOCAL-P implies R_P|K, LOCAL-Q implies R_Q|K. For a global cover both divisibilities hold. The representative is the same before choosing either local carrier realization, since its selection is integer arithmetic on the prescribed metadata alone. Bases and ratios can lie outside the gamma subgroup. No discrete logarithms are used.

## 4. One-sided local count

Fix m,h,plan and its representative nonzero K. Its polylogarithmic bit length implies that it has only polylogarithmically many prime divisors R>=cM^2.031. This is a counting statement; computing these prime divisors is not granted to an algorithm.

For LOCAL-P, each such R permits only O(M^.969) values P=1+vR in the factor range. Ignore primality to overcount. The qualified P is coprime to m, and the fixed product residue determines

 Q=h P^(-1) modulo m^r.

The full Q range has length O(M³), so this gives O(M^(3-r)+1) integer lifts Q. Thus the per-(m,h,plan) count is

 soft O(M^.969 [M^(3-r)+1]).

There are O(M) comparable integers m and O(M^r) h values per m. Multiplying by B(M) yields exactly (3). Swap P and Q to cover LOCAL-Q at a factor-two cost. This includes success in either hidden field with unrelated local seeds/ratios, and even a different successful prescribed plan in the two fields.

There is no assumption that current auxiliary primes form one global menu of size K_*. All comparable m are explicitly counted. The inherited selector telescope is used only for (1), not for this count. Nor is there an assumed distribution of primes in residue classes: all Q lifts and P cofactors are counted as integers.

## 5. Two-sided global count

For GLOBAL success, both distinct primes R_P,R_Q divide the one K. There are only polylogarithmically many possible ordered pairs of such divisors. Fix one pair and choose v in its O(M^.969) range. Then P is fixed and the product residue fixes Q modulo m^r. As R_Q is a prime larger than m, it is invertible modulo m^r. Consequently

 Q=1+wR_Q=h P^(-1) modulo m^r

fixes w modulo m^r. The allowed w range O(M^.969) is shorter than m^r for every r>=2, so at most one w is possible. This gives soft O(M^.969) pairs per (m,h,plan), proving (4) after summing all m,h and plans.

The previous packet's global two-digit bound retained an O(m) union over all anchored relations. Selecting the first nonzero relation removes that factor and strengthens its admissible library from B<=M to B<=M². No previous frozen report is edited or treated as false: its weaker upper bound remains valid.

## 6. Novelty, prerequisite comparison, and limits

The October 7 cyclic-norm obstruction already counted arbitrary short exponent CATALOGS based on (m,N mod m²). Its total logarithmic budget T_X gave local exception count O(M^4.969 T_X/log M). Inserting O(m) relation candidates per carrier plan reproduces the weaker soft O(BM^5.969) local bound. That old counting argument is not new here.

The additional observation is that every successful carrier representation annihilates ALL candidates. One prescribed first-nonzero representative suffices, with only polylogarithmic logarithmic size per plan. This saves a factor M, enables the stated four-digit local conclusion, and strengthens the two-digit global library bound. The general residue/cofactor count is elementary and uses no new analytic prime theorem.

Full-input-dependent origins/positions outside the prescribed residue classes remain open. Polynomial-time or straight-line circuits producing the metadata need not fall in this static plan contract. Longer encodings, larger libraries, arbitrary nonlinear carriers, and implicit scalar methods are not ruled out. Integer energy, not local multiplicative energy/no-wrap, forces the nonzero representative; hence no local order-to-span transfer is silently assumed. The local conclusion does not acquire a local order or give a factoring algorithm. It supplies no operation lower bound, new long-query bound, all-input controller theorem, or Lean declaration.

The five exact prerequisite files are pinned in source-pins.json. prior-cyclic-norm.md is an unchanged restored copy of the archived original /tmp/semiprime-mask-acquisition-20261007/cyclic-norm-obstruction.md (11565 bytes, SHA256 264fca0018ff33277a172ea0e93f6273311a0178a038b127bca8978f8d315b4f). The native-center source and the latest carrier-plan proof supply the labeled witness and algebra, and the historical source supplies the actual prime orders. No examples, source edits or builds are used.

## 7. Total explicit relative-origin budget, with a free common origin

The conclusions also hold under a broader encoding contract. Allow

 k_j=c(N)+kappa_j(m,h,plan),

where the common integer c(N) may depend arbitrarily on the full input, have any numerical magnitude, and need not have a short encoding. Only the relative origins kappa_j are prescribed by the low-digit plan. Replace their individual polylogarithmic bit bounds by the TOTAL explicit-list bound

 sum_j bitlen(kappa_j)<=C m(log m)^A,                                  (7)

for fixed C,A>=0. Carrier assignments, positions and listed lengths remain prescribed as above and satisfy (2); their necessary index encodings can be canonicalized to O(log M) bits. This is a statement about an explicit relative-origin list, not an arbitrary succinct program.

Absorb the common unit gamma^(d c(N)) into every carrier seed. All difference relations and all equal-sum tests are unchanged. Discard any tag with bitlen(kappa_j)>(log m)^(A+2). By (7) there are at most C m/(log m)² such tags. Intersecting the remaining tags with the deterministic light tags leaves g>=m/2 eventually. Both the discarded set and this witness depend only on (m,h,plan), so the representative remains prescribed before inspecting further digits.

The raw congruence energy of this smaller labeled witness is at most E_*. Its g⁴/(2E_*) lower bound still grows as m^1.46 divided by a fixed polylogarithm, contradicting (2) if all candidate integers vanish. Select the first nonzero representative on this SHORT-ORIGIN witness. Every origin occurring in it has polylogarithmic bit length, hence so does the representative. Sections 4–5 then apply verbatim: there is still just one representative per (m,h,plan), so (3), (4), and their stated library/residue-depth consequences are unchanged.

This permits a few individually very long relative-origin integers, and an unrestricted full-input common offset, while excluding every successful plan with a nearlinear TOTAL explicit relative-origin encoding on the retained family. It does not price reading or acquiring a huge common offset, does not assert a fast certificate extractor for it, and does not constrain a short program whose expanded list violates (7). Full-input-dependent RELATIVE origins or positions remain outside the static plan contract.
