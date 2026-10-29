# Native cone reciprocity: a licensed scalar Cayley collision, and cancelled interior rays

26 October 2026. Paper-only finite algebra and acquisition ledger; no repository edits, code or tests. **Executed result:** the raw torus query admits a completely initialized scalar additive-collision form, with symmetric clock halving. The associated cone-reciprocity sum cancels every retained interior collision instead of evaluating it. Neither execution improves the uniform soft K^(5/4) bound.

Read prior credit: frozen `semiprime-knot-trace-20261026/farey-query.md` (including its index-K same-colour repair), `semiprime-string-native-boundary-20261026/native-boundary.md`, the current torus-query and packed-finite-part reports. In particular the old linear coloured endpoint kernel and the index-K character/carry law are NOT new here. The original beta-coupled M1 consumer is kept separate from the raw-torus factor controller.

## 1. Actual same-colour lattice, not an ambient uncoloured cone

For a public unit j modulo K, let

    Lambda_j={(a,b): a*j²=b*N modulo K},
    L_j(a,b)=−a*j−b*N*j^-1,

with the inverse modulo H fixed. The canonical centered phase is ell_j(v)=L_j(v)+H*tau_v. On Lambda_j this is the actual stationary phase modulo H; the colour lift is independent of the chosen representative modulo K. The exact torus-only character is

    chi_j(a,b,k)=W^[L_j(a,b)−a−bN+H*k].          (1)

The ACTUAL leaf is chi_j(a,b,tau_v−i), not chi_j(a,b,−i). All carries are public integers of O(log N) bits. A lattice basis of Lambda_j has determinant K in ambient coordinates and is unimodular only relative to that lattice. Ordinary determinant-one Farey triples in Z² cannot silently replace it.

Thus same-colour addition in this rank-three exponent lattice is exact. All phases/characters for acquired vectors and supplied triangles cost soft K overall. This is inherited character initialization; it is not a selector of the unknown colour or physical index. A Gauss shortest-vector list is also not automatically the full lattice-point set of its convex hull. Filling such a hull is a different family with a separately charged decoder, mask and count. We do not assume a soft-K unimodular sail triangulation of all rows without constructing it.

## 2. Execute cone subdivision at an actual native hit

For any two formal characters x,y, the half-open unimodular cone identity is

    1/((1−x)(1−y))
      =1/((1−x)(1−xy))+y/((1−y)(1−xy)).         (2)

It follows by putting the two terms over their common denominator; the numerator is 1−xy. This is the elementary local form of rational-cone subdivision. The primary [Brion, Points entiers dans les polyèdres convexes](https://www.numdam.org/article/ASENS_1988_4_21_4_653_0.pdf), Theorem 2.2, sums tangent-cone rational generating functions to recover a FINITE lattice-point polynomial. It does not assert an entrywise resolvent transform of that polynomial is acquired at the same cost.

Use actual canonical torus roots x=z_j and bounded clock character y=q0^-i. First test x−1 for every row. Every nonliteral nonunit is an actual W-annihilator and factors by the new consumer; literal rows have already been removed by the torus-query guard. On continuing branches x−1 is a global unit. For i!=0 in the physical interval, y−1 is a certified global unit by the actual q0 short screen. The i=0 leaves have already been handled by the row test.

At every remaining native hit xy=1, both endpoint generators x,y have unit differences. Yet the two NEW diagonal-ray terms on the right of (2) have poles at 1−xy=0. Their combined coefficient at that pole is

    1/(1−x)+y/(1−y)=0 when y=x^-1.             (3)

Thus their diagonal pole cancels EXACTLY at the actual native collision. The left side is regular and has no selected collision residue. This is not a free-coefficient diagnostic: if the cheap i=0 gates have not factored, the correct bin's remaining witness is precisely a hit to which (3) applies. Adding actual carry coordinates in (1) preserves the identity and the cancellation; discarding those carries would instead change the tested leaf.

Consequently the internal-edge cancellation in this explicit cone sum removes, rather than acquires, the original interior witness. It is not a theorem against all fan algorithms. A construction retaining one diagonal denominator instead of summing its cancelling partner has the licensed collision described next.

## 3. Positive execution: cone/cotangent addition becomes a scalar collision query

Put F(x)=(1+x)/(1−x). The exact cotangent/character identity is

    F(x)+F(y)=2(1−xy)/((1−x)(1−y)),              (4)
    F(x)F(y)−F(xy)*(F(x)+F(y))=−1.              (5)

These are finite rational identities proved by clearing. Equation (5) is the cotangent addition/triangle identity; no root-of-unity Dedekind sum is specialized. On the unit-gated locus above, equation (4) is a UNIT multiple of the original multiplicative gap. A nonunit additive sum is therefore a proved genuine torus relation, unlike an arbitrary zero of a Fricke polynomial or a graph determinant.

Norm-one x gives bar(F(x))=−F(x). With the supplied tau and tau²=D, F(x)/tau is an actual BASE scalar. Define acquired row values

    A_j=F(z_j)/tau.

They cost soft K after the row unit gates. For the clock put

    B_i=F(q0^-i)/tau, i!=0.

Every denominator is a known short unit and B_-i=−B_i. Clock values have random-access acquisition by binary powering; we do NOT emit h entries for free. The entire retained raw-torus query is exactly the scalar additive-collision problem

    A_j+B_i=0 for some j and nonzero i in [-M0,M0].

All actual aliases remain useful through equation (4) and the torus annihilator consumer. This is a coverage-preserving rewrite with a complete decoder; no common-tag or singleton assertion from the original coupled bank is imported.

Symmetry of the finite window now gives

    (A_j+B_i)(A_j−B_i)=A_j²−B_i², 1<=i<=M0.    (6)

Thus one may use M0 positive clock positions and row targets A_j². The factor sign is retained during localization: if a squared difference is saturated, test its two linear factors and select a nonunit one. Every selected factor has a literal nonzero native exponent from the original torus ledger. This is constant-factor folding, not a power saving.

## 4. Initialize the scalar Chebyshev clock and complete the experiment

Let t0=Tr(q0), and C_i(t0)=q0^i+q0^-i, with C_0=2,C_1=t0 and C_(i+1)=t0*C_i−C_(i−1). Then

    B_i²=(C_i(t0)+2)/(D*(C_i(t0)−2)).           (7)

Every denominator is a certified unit: C_i−2=−Norm(q0^i−1), and 1<=i<=M0<16H. D is already a unit. This supplies a common order-two trace clock and an exact scalar Möbius transform, with seeds, index and endpoint metadata acquired. It does not supply the whole length-M0 list in soft K.

The old shared query can be run without that list. For x=z_j and z=q0^i, clearing (7) gives explicitly

    A_j²−B_i²
      =−4z/[(1−x)²*D*(z−1)²]
                  *(1−xz)*(1−x/z).            (8)

Every prefactor is a known unit. Therefore the scalar Cayley query is EXACTLY the two signed geometric-clock products already initialized by the old engine. Its shared blocked completion, including all finite tails and localization, costs soft(K+sqrt(Kh))=soft K^(5/4). Equations (6)–(8) prove the initialization and all denominator gates, rather than assuming a fast evaluation theorem for a Möbius clock.

A Stern–Brocot addition chain computes F(chi(v+w))=(F(chi(v))*F(chi(w))+1)/(F(chi(v))+F(chi(w))) whenever its displayed denominator is a unit. If it is nonunit and the combined exponent is nonzero, equation (4) gives a legal factor exit; literal zero labels must be detected first. This is useful guarded random access for supplied fan nodes. It does not search the unknown clock index or select a covered subtree. On the pure clock these addition pivots are short units when the involved i,j,i+j are nonzero and have absolute value at most 16H; within that guard this random access is fully legal; the unacquired operation remains joint row/clock collision search.

## 5. Why a short Brion/Carlitz polynomial sum is a different observable

For a FINITE support S, let Phi(X)=sum_(alpha in S) c_alpha X^alpha, with the actual colour, canonical carry and clock coordinates. Its selected-resolvent transform is exactly

    sum_alpha c_alpha/(1−z*chi(alpha))
      =sum_(r>=0) z^r * Phi(chi^r).             (9)

This is an equality of formal power series at z=0. It shows where a short rational cone formula must be used: at ALL needed power substitutions, not just once at chi. Evaluating a short Brion polynomial sum computes Phi(chi), which is not the selected pole at z=1. Cone denominators after power substitution may themselves become nonunits; the ordinary unit screen supplies only the stipulated short range. No hidden finite group order or convergent analytic completion is available to replace that power sum by a known complete character average.

The primary [Beck–Haase–Matthews, Dedekind–Carlitz polynomials as lattice-point enumerators in rational polyhedra](https://arxiv.org/abs/0710.1323) concerns finite lattice enumerators and reciprocity, not a finite-ring selected-resolvent evaluator. A reciprocity relation for such enumerators can be transported through (9) only with its transformed functions/finite boundaries still paid. The old native-boundary report already demonstrates the analogous mistake for multiplicative images of finite differences; it is prior credit, not rediscovered acquisition here.

On the original beta-coupled bank the desired M1 is a canonical colour-weighted selected residue with its exact count bound. Filling rational cones or changing row multiplicities does NOT automatically preserve that observable. The raw-torus alternative above can accept a nonzero-exponent overcover because every localized alias factors; it makes no assertion about original coupled moments. This branch distinction is essential.

## Outcome

The strongest executed positive operation is an acquired scalar Cayley row alphabet and a guarded Chebyshev/Möbius clock, with an exact factor-preserving collision relation and finite sign folding. Its completion is still the old geometric engine. The explicit cone-subdivision candidate cancels the pole of every actual interior witness after the cheap endpoint gates; a Brion/Carlitz polynomial sum alone does not supply its resolvent transform. A useful successor would need to acquire the scalar joint collision or the selected transform in (9), while retaining the native finite support or an actually decoded overcover. No faster whole-query algorithm or general obstruction is claimed.
