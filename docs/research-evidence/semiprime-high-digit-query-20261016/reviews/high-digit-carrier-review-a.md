# Independent review: high-digit energy and advised carrier covers

Verdict: PASS for the exact final theorem and its stated representation scope. No correction remains requested.

Final report carrier/high-digit-ap-cover-obstruction.md: 9861 bytes, SHA256 720e5546858fc02091052e759919fb0d9b5b1dfec97bd83792621eb7e86e7eb7.
Source metadata carrier/source-pins.json: 1340 bytes, SHA256 e325a6ace5f111b282074b85dad87da33d4184db4fffe5d6197592f20bd6edb2. Independently checked all six source paths, byte counts and hashes.

## Literal source and high-digit averaging

Checked the native definitions, not only a surrogate modular model. quotientSlope is the canonical residue of N times publicInverse squared; representative at t=1 gives canonical a_j. denseRow calls liftRow with D=(N-a_j j^2)/m and b=centered(-inverse D); seedRow takes t=1 and the positive branch. The pinned cached/literal offset is a_j+m b_j-2a_j j. Integrality follows from the slope congruence. N -> N+m^2 fixes a_j and adds m to D, so centered_congr fixes b_j exactly. Thus the literal catalog, not just its residue image, depends only on N modulo m^2. Replacing publicInverse by its F_m inverse representative changes no centered result.

For N_h=n+mh, the displayed offset slope modulo m^2 is -m I_j h. The low quadratic is n(t^2-2t), n nonzero. It permits at most two fourth variables after three nonzero inverse residues are fixed. Hence at most 2(m-1)^3 low-equality ordered tag quadruples. If the high-digit slope sum is nonzero, at most one h solves the additional equation modulo m^2. If it is zero, equality of low quadratics equates sums and products of the two inverse-residue pairs (m odd), forcing the same unordered pair. There are at most 2(m-1)^2 such ordered quadruples, each counted at most m times. These estimates give the claimed <=4m^3 total.

Selecting one original tag per distinct literal offset injects each deduplicated INTEGER energy quadruple into a raw modular tag quadruple. This injection can depend on h and requires no fixed labeling across h. Exact integer equality is a sufficient condition for modular equality; no converse is presumed. The averaging and Markov removal therefore remain valid even before using literal periodicity. After summing over nonzero n the excessive-energy residue set has size at most 4m^(2-eta).

## Progression covers, overlaps and arbitrary advice

The exact low image is n(Squares-1), including all squares despite excluding inverse residue zero, so J>m/2. Arbitrary overlapping progression covers can be partitioned by assigning each distinct target to one covering progression. Empty assigned pieces may be ignored. Nonempty progressions have positive listed lengths; a zero step is a singleton and causes no failure. Each assigned subset has sumset at most 2T_i, independently of holes, signs or step magnitude. Internal energy quadruples of distinct assigned pieces are disjoint.

Cauchy gives E>=sum n_i^4/(2T_i). Holder, or Cauchy followed by sum n_i^2>=J^2/k, gives E>=J^4/(2k^2 T). With E<=m^(2+eta) and J>m/2 this proves the stated constant 1/32. All starts/steps/assignments may depend on full N or hidden advice, because the energy bound is a property of the actual set and contains no union over covers.

## Varying-menu majority count

Independently checked the pinned endpoint theorem's selector envelope and telescoping estimate: at fixed P,m, Q lies in O(G_m+1) half-open intervals of width at most m^2, and sum_m(G_m+1)=O(K_* M). P is a unit modulo m^2; distinct integer Q in one such interval cannot yield the same product residue. Each box therefore has at most O(m^(2-eta)) bad Q, already counting all integers and hence prime Q. Summing O(M^3) possible P and all candidate m gives O(K_* M^(6-eta)), with no extra tag, slope, field or candidate factor. For eta=.04 and K_*=O(M^.020), this is O(M^5.980). It is negligible versus the same original Omega(M^6/log^2 M) supply and can be unioned with its prior sub-six-power losses. The report correctly avoids multiplying a global fixed-m count by K_* when m is input-dependent, and does not intersect unrelated thin retained sets.

## Arbitrary geometric and higher-rank carriers

The strengthened transfer is exact: target product equality means the gamma order divides a four-offset sum difference, whose absolute value is at most 8m^2. Under order >8m^2 it is zero. Thus multiplicative and literal additive energies agree. This holds in either field and in the global unit group because the GLOBAL ORDER OF GAMMA is a multiple of each local gamma order; the final wording states this explicitly.

For any ambient abelian-group geometric progression, assigned products have exponent-index sums in [0,2T_i-2]. Therefore productset size <=2T_i-1 even if its origin/ratio is outside the gamma subgroup, privately advised, equal to one, or causes cyclic repetitions. Partition and Cauchy prove the identical k^2 T bound, simultaneously over all such covers. No hidden-order oracle, root extraction, or discrete logarithm is supplied.

For a containing carrier C, E>=J^4/|ZZ| implies |CC|>=|ZZ|>=J^4/E>=m^(2-eta)/16. A rank-r progression box has productset at most 2^r T, proving the final extension. Nearlinear listed size and r=o(log m) contradict this bound; arbitrary polylogarithmic rank is correctly left open.

These are actual-source carrier representation bounds. They do not lower-bound arithmetic operations, exclude sharing across a large implicit carrier, or acquire a norm/locator/factor query. Nonlinear large-productset carriers, fixed-source cancellations and other sufficient observables remain allowed. No field counting is charged as an algorithm, no additional prime-distribution theorem is invoked, and no new native proof, build or numerical experiment is claimed. This review is read-only; only this external review artifact was written.
