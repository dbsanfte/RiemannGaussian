# Independent D.1 precision audit: Cauchy integrality and tapered Hermite recovery

26October2026. Goal explicitly resumed, but this artifact is a proof audit, not a factoring implementation. Source: supplied OpenAI ETH paper,17October/revised25October2026, AppendixD.4.1–D.4.4, printedpp.57–61. **Disposition: the audited precision layer PASSES independent reconstruction under its stated parameter hypotheses.** I found no essential failure in LemmasD.4/D.5 or(D.9)–(D.11). This does NOT certify the mode construction, child-size reduction, evaluator recursion or whole TheoremD.1; those remain separate proof obligations.

Exact standard-library controls: [check_precision.py](/tmp/semiprime-d1-audit-20261026/check_precision.py), output [precision-checks.json](/tmp/semiprime-d1-audit-20261026/precision-checks.json). Replay:

    python3 /tmp/semiprime-d1-audit-20261026/check_precision.py

These finite controls supplement the universal derivation below, rather than prove it by fixtures.

## 1. The valuation ring and arbitrary tensor entries

D.4.1 constructs a monic integer f of degree e=4ceil(log2s), irreducible modulo2, and O=Z_(2)[U]/f. The coordinate-minimum valuation really is multiplicative in its fraction field K: factor out the two minima, and the two resulting nonzero residues have nonzero product in F_(2^e). An element with nonzero residue is a unit, for example by the multiplication-matrix adjugate divided by its odd determinant. All this is valid for the stated f, not an assumed arbitrary extension ring.

For A=O[V]/V^ell, only COORDINATEWISE divisibility and scalar multiplication are needed in D.4.3–4.4. Multiplicativity of a minimum valuation for arbitrary nilpotent A elements is neither true nor required.

At a call, entrywise canonical lifts are fixed at their creation precisions. Therefore A(Y),B(X) in(D.8) are coefficients independent of T, even for arbitrary high-arity tensor tables. Each real row port supplies one affine l_Y(W(T)X), so deg F<=M(2L-1). No assumption of low polynomial degree in the tensor's OWN ports is used. Its arbitrary lifted entries lie in A; all local integrality below is therefore preserved by their finite sums/products.

The creation-precision convention matters: a child must evaluate its original tensor modulo its tagged precision and lift those SAME representatives. Relifting an unrelated higher-precision oracle value would define a different F. The paper explicitly gives the required convention and strictly increasing working precisions; this audit assumes the eventual evaluator obeys it.

## 2. Reconstruct LemmaD.4 without a division by a zero factor

Write L=2^a, alpha=2^(a+1)=2L, S={-L,...,L-1}. This is a COMPLETE residue system modulo2L. For each t inS, nonzero differences t-q have valuation at most a, with 2^(a-j) differences of valuation j for0<=j<=a. Thus

v2(C'(t))=v2(C'(0))=sum_(j=0)^a j 2^(a-j)=2L-a-2.  (P1)

For W_xy(T), omit the factor indexed by d=y-x. If d=t, the expansion W_xy(t+alpha z) consists of all q!=t factors, divided by C'(0). Each factor has content2^v2(t-q); their contents cancel precisely(P1), and the residual scalar denominator is odd. Hence every coefficient lies in Z_(2).

If d!=t, the factor alpha z remains and the omitted nonzero-difference factor has content at most2^a. The net content is at least2^(a+1-v2(t-d)), hence at least2. This proves the stronger off-node divisibility too. No inversion of alpha z or of a possibly vanishing evaluated factor is performed. It remains valid at z=0 and at arbitrary unramified-extension zeta.

Evaluation is constructive: divide each nonzero-difference linear factor by its KNOWN two-power content, multiply these integral factors, include the residual nonnegative power of2, and invert only the ODD denominator. There are O(L) factors of O(a)-bit constant data. Arithmetic modulo2^p in the e-dimensional extension and ell coefficients costs polynomial(s,p,ell). This verifies the algorithmic claim as well as integrality. Substituting in(D.8) proves F(t+alpha z) in A[z] for arbitrary lifted input tensors.

## 3. Reconstruct the Hermite identity(D.9)

Let q_t=h max(0,u-v2(t)), h=ceil(3M/u), for nonzero nodes, and use only q_t>0. The L odd nodes alone give total multiplicity>=L h u>=3ML>M(2L-1). Also h<=4M/u because M>=u, so every q_t<=4M.

Define E_t exactly as in the paper, omitting0 and t and raising each other node factor to its assigned multiplicity. Then

E_t(T) * [F(t+alpha z)/E_t(t+alpha z)]_(degree<q_t)
                    evaluated at z=(T-t)/alpha

has the prescribed jet at its own node and the required zeros at all other active nodes. Its degree is below the total multiplicity. The usual divisibility argument therefore proves the identity over K[V]/V^ell coefficientwise; setting T=0 gives(D.9). This does not require A itself to be a field.

Every factor of E_t(t+alpha z) is a power of 1+alpha z/(t-q). Its nonconstant coefficient is integral (in fact even), and its constant is1. The reciprocal series has integral coefficients: (1+c z)^(-m) has coefficient(-1)^j binom(m+j-1,j)c^j. Thus dividing the local jet by this series loses NO two-adic precision. It also requires no division by a Taylor index.

## 4. Derive the ESSENTIAL j factor in(D.10)

Fix i=v2(t), D=L/2^i. The exact valuation is

v2(E_t(0))=sum_(q!=0,t) q_(v2(q))[v2(q)-v2(t-q)].

Points with v2(q)<i contribute zero. For each j=1,...,a-i:

* D/2^j points have v2(q)=i+j and v2(t-q)=i; each contributes +j q_(i+j).
* D/2^j points have v2(q)=i and v2(t-q)=i+j; each contributes -j q_i.

The count is exact on this complete residue grid, including its asymmetric endpoint -L and excluding0,t. Therefore

v2(E_t(0))=D sum_(j=1)^(a-i) (j/2^j)[q_(i+j)-q_i].  (P2)

The numerator j is essential. It is present in the printed(D.10), and follows independently from the valuation differences. Since the tapered multiplicities are h-Lipschitz in the level, q_(i+j)-q_i>=-hj. Hence

v2(E_t(0))>=-Dh sum_(j>=1) j²/2^j=-6Dh.             (P3)

This validates the contested taper gain: a hard cutoff of equal multiplicities does not have the same Lipschitz estimate, while the linear taper does.

## 5. Exact error budget for local data

Evaluation at -t/alpha has valuation loss j(a+1-i) on coefficient j. Its maximum for j<q_t is at most4M(a+1), using q_t<=4M. Together with(P3), a sufficient local precision is already

p+6hD+4M(a+1).

The paper uses the larger p_t=p+8hD+8M(a+1). Consequently ANY lifts of the supplied local coefficient residues cause an error of valuation>=p in every Hermite summand. Summing does not decrease this minimum. There is no further logarithmic precision cost for the number of nodes. Integrality of the reconstructed value follows from its difference from the stipulated integral F(0), not from rounding a nonintegral rational result without proof.

All Hermite multipliers have polynomial bit length: their node denominators have O(a) bits, and total multiplicity is O(ML). Rational common-denominator arithmetic, cancellation of its two-power part and reduction modulo2^p therefore cost polynomial(M,L,a,e,ell,p_t). This substantiates the stated arithmetic model, not only an abstract interpolation identity.

## 6. Reconstruct(D.11), with its actual conditional dependencies

Write lambda=ceil(log2s), a_d=2sum_(j<=d)u_j, a_(-1)=0. Assume the claimed active-path bounds supplied by the OTHER recursion stages: M>H~s/sqrt(lambda), M<=Cs8^-d, u_d>=lambda^(4/5), a_d<=4epsilon lambda. Then d<=log2(lambda)/6+O_C(1).

At depth d, the inherited precision is root P0<=Cs plus all earlier increments. Every earlier packet exponent is <=a_(d-1), M_j<=Cs, and all remaining factors/depth counts are polynomial in lambda. Thus

p<=s lambda^O(1) 2^(a_(d-1)).

For an active node i<u_d,

D_t=2^(a_d-i)>=2^(a_d-u_d)
                  =2^(a_(d-1)+u_d).                 (P4)

The extra 2^u absorbs every fixed polynomial in lambda. More explicitly, the ratio of the inherited bound to M D_t/u is at most lambda^O(1)2^-u, because s/M=O(sqrt(lambda)). The same estimate absorbs8M(a+1), and8hD_t<=32M D_t/u directly. This proves p_t=O_C(MD_t/u). There is no lost 2^a factor hidden in that bound.

The local interpolation also has charged finite size: M(2L-1)+1=O(s^(1+4epsilon))<s^4 for sufficiently large s, so the e=4lambda residue field supplies enough binary-coordinate lifts with unit differences. Representing all these coefficients, ell V coordinates and e extension coordinates at precision p_t is polynomial in s. Brute construction of the irreducible polynomial by the stated candidate/divisor enumerations is polynomial in s as well. This establishes the local arithmetic overhead; it does not bound the number of recursive child evaluations needed to obtain those values.

All precisions are polynomial in s since a_d<=4epsilon lambda. However the parameter thresholds can be enormous; the argument is asymptotic, with the paper's explicit finite-size parameter checks/fallback. This is no practical speed claim. This audit has NOT independently established that every eventual child really has M/8 edges or the asserted entry-evaluator description; those are required premises for this part and must be checked in D.4.5 onward.

## 7. Exact rational controls and replay scope

The supplied script uses only Fraction/integer arithmetic. It checks:

* 84 Cauchy W_xy polynomials, all slot pairs for a=1,2,3;
* 17,472 coefficients at every local grid expansion, all two-adically integral;
* 46 exact(P2) valuation counts;
* 378 Hermite weights against the advertised p_t error budget;
* 6 full rational reconstructions with independently perturbed coefficient lifts of size2^p_t.

The test F polynomials are nontrivial integer linear combinations of products of actual Cauchy entries, degree at mostM(2L-1), with known integral F(0). Their observed reconstruction-error valuations exceed the requested p=5 in all cases. This checks normalization, signs, endpoint counting and precision-sized perturbation behavior. It is NOT a proof for all tensors, not a D.1 implementation, not a contraction benchmark and not a semiprime experiment. Universality follows from the derivation above, which is linear and coordinatewise and therefore also applies to the extension and V coefficients.

## Final proof obligation

No repair is required in the audited local precision formulas. The source's p_t has explicit slack; using it consistently is safe. To claim whole D.1, the remaining evaluator must return the correct first q_t local coefficients modulo exactly p_t while respecting the canonical creation lifts, actual child-size bounds, implicit tensor-entry costs and fixed polynomial bit overhead. This precision audit does not replace those stages. It does isolate a fully reconstructed layer which, under those interfaces, does not consume an uncharged amount of precision or exponential data.
