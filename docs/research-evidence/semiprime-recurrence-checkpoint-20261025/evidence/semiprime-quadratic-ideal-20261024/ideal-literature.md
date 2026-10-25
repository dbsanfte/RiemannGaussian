# Native quadratic point ideals: paid separation and a compact exact ideal

24 October 2026. Scratch only. This gives concrete soft-J factor-or-separation preprocessing and a soft-J arithmetic-circuit representation of the TRUE point ideal, including repeated-delta fibers. With the public modulus refinement in Section 3a, it also acquires an explicit bounded-width auxiliary-coordinate ideal in soft k. It does not acquire a balanced original-bivariate Gröbner basis or a faster long incidence query.

## 1. Actual input, not an arbitrary torus-point premise

Use `/tmp/semiprime-recurrence-closure-20261024/frobenius-pairing.md`, SHA256 `215f1fd452452ce0719ff4b88b81f74b69c8a88dc12d80c8bb63a81d11e2e363`, with independent PASS review SHA256 `147ed84ea489fb61e8e2b47e2c6d09a90cf247f743df017e48314b613f815a97`.

R=Z/N, N=PQ distinct odd primes, B=R[tau]/(tau^2-D), with 4D a unit and conjugation tau -> -tau. Exactly one unknown local side p* is a quadratic FIELD; the other is split. All actual unit targets V_j=x_j+y_j tau, their native integer delta_j, and unit seed z are acquired in soft k. Put H=k^2, E_j=N+delta_j, J<=k, L=2H+2. The native bounds are delta_j in [-3H,H], beta has odd local orders >16H, and

    Norm(V_j)=beta^(2E_j),  Norm(z)=t=beta^(2H).

The actual seed unit screen and same-leaf saturated decoder are already paid. No large order for the Cayley point W is assumed. We use the actual constructor's norm identity and margins; a general arbitrary norm-one point contract is not substituted for this family.

## 2. New useful preprocessing: exact duplicates, then separation or a factor

First sort the pairs (x_j,y_j) as canonical residues and remove exact global duplicates. This costs soft J. Removing repeated actual targets preserves every row/interval zero mask when corresponding original labels are retained as a fiber. It is not the unsafe deletion of different V values sharing delta. Exact equal V values necessarily have the same integer delta, by the norm margin below. Let J0 be the remaining count.

**Pair lemma.** For distinct retained V_j,V_h, gcd(Norm(V_j-V_h),N) cannot be N.

Proof: a saturated difference norm vanishes at the FIELD side p*, hence V_j=V_h there. Their norms give beta^[2(delta_j-delta_h)]=1 modulo p*. Since |2(delta_j-delta_h)|<=8H and the local beta order exceeds 16H, the integer deltas are equal. Their norms therefore agree GLOBALLY and are units. On the split side write V_j=(u,v), V_h=(u',v'), with uv=u'v'=n a unit. A zero difference norm means u=u' or v=v'. Either equality and the unit norm force the other equality as well. Thus the two targets agree at both sides, hence globally in B, contrary to the deduplication. This proves the lemma without identifying p* or a split component.

Execute it without a quadratic all-pairs test. Acquire

    F(U)=prod_(j<=J0)(U-V_j),
    d_j=F'(V_j)=prod_(h!=j)(V_j-V_h)

by a monic product tree, derivative and monic multipoint evaluation, all in soft J. Scan gcd(Norm(d_j),N). If all are one, every target difference is a unit in B. If a bad row is found, scan its J0-1 individual differences. Multiplicativity guarantees a nonunit pair, and the pair lemma guarantees a proper factor. The scan is done for only ONE bad row. Total cost is soft J, including all gcds and actual B coordinates; no target separation is presumed to perform monic evaluation.

Hence we either factor N or obtain certified unit-separated, globally distinct targets in soft J. This is an acquisition result, not an algorithm for the length-L product. It also makes original simple-root contracts available after actual preprocessing. The input and guarantee are stronger than those for arbitrary quadratic points: the short native beta norm labels and unique nonsplit side are essential to the saturated-pair lemma.

## 3. A true point ideal in soft-J circuit size, with all norm fibers retained

Continue only after successful separation. Group retained targets by their exact integer delta. Let groups d=1,...,M have sizes r_d, sum r_d=J0; set

    n_d=beta^[2(N+delta_d)],
    G(T)=prod_d(T-n_d),
    F_d(U)=prod_(j in group d)(U-V_j).

Distinct norm nodes n_d-n_e are units in R: otherwise beta^[2(delta_d-delta_e)]=1 at one local prime, contradicting the same short order margin. These are real acquired nodes, not a generic linear projection. Acquire dense G and all dense univariate F_d in soft J. Evaluate G'(n_d) and invert these certified units in soft M. Define the CRT selectors

    e_d(T)=[G(T)/(T-n_d)]/G'(n_d),
    mathcalF(T,X,Y)=sum_d e_d(T) F_d(X+tau Y)
                   =H0(T,X,Y)+tau H1(T,X,Y).

All selector POLYNOMIALS are represented by a shared product/complement tree. Compute sibling products down the tree; the leaf complement is G/(T-n_d). This gives O(M) multiplication gates sharing intermediate polynomials, rather than M separate length-M coefficient vectors. Evaluating all F_d at the common formal X+tau Y and summing takes O(J) further constant-rank gates. The division above is only by the acquired scalar unit G'(n_d). The coefficient computations cost soft J; generator circuits have O(J) gates with O(log N)-bit constants. No symbolic inversion of T-n_d is performed.

Put n(X,Y)=X^2-DY^2. The exact bivariate point ideal is

    I = < G(n(X,Y)),
          H0(n(X,Y),X,Y), H1(n(X,Y),X,Y) >
      = intersection_j <X-x_j,Y-y_j>.                 (1)

Equivalently retain T and add T-n(X,Y), G(T), H0, H1 as auxiliary-coordinate generators. This is an actual initialized arithmetic-circuit ideal, not merely equations whose zero set has unknown extra components.

Proof of equality, including split sides: CRT modulo G reduces to one norm fiber. After the faithfully flat quadratic base extension R -> B, use u=X+tau Y, v=X-tau Y; 2 and 2tau are units. The fiber equation becomes uv=n_d, so u is invertible. Its two component equations are F_d(u)=0 and bar(F_d)(v)=0. Since every root V_j has norm n_d,

    bar(F_d)(n_d/u)
      =(-1)^r_d (prod_(j in d)bar(V_j)) u^(-r_d) F_d(u).

The multiplier is a unit on uv=n_d. Thus the fiber quotient after base extension is B[u]/F_d(u); its nonzero constant coefficient makes u invertible automatically. All roots V_j in the fiber have certified unit differences. Consequently this quotient is the product of r_d copies of B, and the corresponding ideal is precisely the intersection of the actual point ideals. Faithfully flat descent proves (1) over R. Alternatively, unit difference norms imply coordinate difference ideals generate R, so these actual point ideals are pairwise comaximal. The acquired quotient is finite etale of rank J0 over R. This is a structural proof, not a hidden-field algorithm.

If separation had been omitted, the same equations could keep multiplicities at local collisions; they should then be described as a support/fat-point construction, not automatically the reduced true point ideal. Section 2 removes that ambiguity with a paid factor-or-unit branch.

### Representation and degree ledger

The nearlinear claim concerns arithmetic circuits with shared products. It does not claim that all expanded coefficient arrays are nearlinear. G(n) has exact total degree 2M. The other two generators have total degree at most 2(M-1)+max r_d <=2J0-1, before possible cancellations. A dense bivariate representation can therefore have O(J^2) slots; expanding it is not charged as soft J. The auxiliary-coordinate representation is not a balanced degree-O(sqrt J) bivariate Gröbner basis. The same norm-coordinate construction in the singleton-fiber case can also be expressed through soft-J univariate interpolation of x_d,y_d against n_d; the selector construction handles every repeated-delta group without discarding its distinct points.

## 3a. Public modulus refinement: bounded fibers and explicit bounded-width generators

The following refinement was proposed by root and is derived here; it is not silently attributed to the frozen predecessor. For N=1 mod 4, the accepted predecessor scan acquires a with Jacobi(a,N)=-1 and a<=ceil(N^(5/32)). Factor this PUBLIC integer by trial division. Some prime factor ell has Jacobi(ell,N)=-1; select one. Set D=-ell when ell=3 mod 4, D=-4ell when ell=1 mod 4, and D=-8 for ell=2. For N=3 mod 4 use D=-4. These are negative fundamental discriminants, Jacobi(D,N)=-1, and c=|D| has at most one odd prime factor. Its discovery/factoring cost stays soft k: sqrt(a)<=O(N^(5/64)), below the sixth-root scale. This uses the predecessor's already accepted character-discovery bound, not a new least-nonresidue theorem.

Let r=ceil(N^(1/6)), A=max(3,ceil(r/(2c))). Sieve to 4A and choose an odd prime q>=A different from ell (where relevant). Bertrand in two successive intervals guarantees a choice <=4A even if the first candidate is ell. Set k=2c q, H=k^2. Then k>=r and k<=8c A=O(r+c); since c=O(N^(5/32))=o(r), k=Theta(r). Finite bounded exceptions are handled by the predecessor's finite-input factoring branch. Sieve cost is soft A<=soft k. The factorization of k is public: at most two distinct odd prime factors, each exponent one, and v2(k) in {1,3,4}. Use this actual k throughout the preparation: rerun scalar-order/seed guards and construct its actual native rows. The original conductor-divisibility and own-tag arguments remain applicable; no existing guard for a different k is imported.

For a native unit tag j, a_j=N j^-2 and ell_j=k b_j-2a_j j give the exact congruence

    N^-1 delta_j = j^-2-2j^-1
                 = (j^-1-1)^2-1 mod k.

Thus each fixed EXACT integer delta imposes a quadratic congruence on u=j^-1-1. At an odd prime divisor of k there are at most two roots; at 2^e, e in {1,3,4}, at most four roots. CRT gives at most 4*2*2=16 roots, and j->j^-1-1 is injective on unit tags. Every repeated-delta fiber therefore has r_d<=16, even before exact target deduplication. This bound concerns the newly chosen public modulus; it is not asserted for arbitrary older conductor multiples with large prime-power factors. In particular M>=phi(k)/16. Since there are at most two distinct odd prime divisors, phi(k)/k>=4/15, hence M>=k/60. Exact global target deduplication cannot remove an entire distinct-delta fiber: equal targets force equal deltas. Thus M=Theta(k) for this full unit-tag family, independently of the Cayley point's order. This is a degree/cardinality ledger, not a computational lower bound.

Now upgrade the compact ideal to explicit coefficient data WITHOUT expanding norm substitution. Pad F_d(U) to 17 coefficient entries, and interpolate each of these 17 scalar B-valued coefficient functions at the actual separated nodes n_d. The resulting

    mathcalF(T,U)=sum_(a=0)^16 C_a(T) U^a,
    degree C_a < M,

has at most 17M B-coefficients, acquired by ordinary unit-safe univariate interpolation in soft k. It is precisely the CRT selector polynomial above modulo G, not a symbolic input. Expand only U=X+tau Y: because a<=16 is constant, H0(T,X,Y), H1(T,X,Y) have O(M) coefficient slots, with T-degree<M and (X,Y)-total degree<=16. Together with dense G(T) and T-X^2+DY^2 these give a fully acquired exact auxiliary-coordinate point ideal in soft k. The proof of Section 3, including true reducedness after the factor-or-separation branch, is unchanged.

This is a bounded-width norm-coordinate representation, not a claim that eliminating T preserves its coefficient size or that it supplies a balanced degree-O(sqrt J) basis in X,Y. The projected incidence condition G(t^i)=0 still has degree M, potentially Theta(k), and the other generators still retain the row choice within its bounded norm fiber. No terminal-query saving follows just from the constant fiber width.

## 4. Exact seed incidence and the safe paid overcover

Acquire z^i=x_i+y_i tau at any selected i by binary powering, or successively by the common quadratic recurrence. Exact local incidence with the point set is simultaneous vanishing of the three generators in (1) at (x_i,y_i). Since n(x_i,y_i)=t^i, the first generator is simply G(t^i). The other two generators retain which actual point lies in that norm fiber; they are not automatically zero when the norm coordinate matches.

This already yields a complete safe OVERCOVER query:

    Q_norm=prod_(0<=i<L) G(t^i).                       (2)

Its M nodes are acquired and unit-separated, and own-row coverage guarantees a local zero. A nonunit restricted product is localized to one d,i. At a saturated leaf, beta^[2(E_d-Hi)]=1 globally, odd local orders remove 2, and the original short-index/global-order decoder recovers P+Q=1+Hi-delta_d. A proper gcd factors immediately. Only the known original norm labels and bounded i are used. Thus omitted H0,H1 cannot produce an unhandled false positive. Exact duplicate labels may be lifted to any retained original delta-compatible tag.

Query (2) costs soft(M+sqrt(M L)) by the existing blocked scalar method, with the same paid restriction/localization interface. M can be of order J; no actual-family theorem making it uniformly smaller is proved here. In fact (2) is the old scalar norm projection in an ideal language, not an acquisition advance for the terminal endpoint. At each local prime its leaf has the same zero support as beta^E-beta^Hi, since the complementary factor beta^E+beta^Hi is a unit for odd-order beta. Relative to the full quadratic point-incidence test it is an overcover, and its independent scalar decoder is why that overcover is safe.

Evaluating the compact exact ideal at every seed point by its gates would cost soft(J L), with all L points acquired. A fast reduction or quotient multiplication routine for the rank-J point algebra still does not execute the interval intersection/product functional for free. The existing exact covered B query remains soft(J+sqrt(JL)); (1) supplies a better acquired interface, not a better terminal exponent.

## 5. Primary ideal/basis algorithms checked against this contract

**Jeannerod–Neiger–Schost–Villard, ISSAC 2016, Theorem 1.3.** [Fast computation of minimal interpolation bases in Popov form for arbitrary shifts](https://perso.ens-lyon.fr/gilles.villard/BIBLIOGRAPHIE/PDF/issac-bases-2016.pdf) computes an m-by-m shifted Popov interpolation basis for explicit E in K^(m-by-sigma) and a standard Jordan representation, deterministically over a FIELD, in soft(m^(omega-1) sigma) operations (with its stated multiplication/log factors and m=O(sigma) regime). Arbitrary shifts are allowed. For bivariate point interpolation with Y-degree <m, take columns (1,y_j,...,y_j^(m-1)) and diagonal x-coordinate action. At m about sqrt J, sigma=J, the bound is soft(J^((omega+1)/2)); the explicit matrix alone has Jm entries. Constant m gives nearlinear acquisition but does not supply balanced degrees in both coordinates. Neither our circuit generators nor a compact power description is automatically that explicit theorem input. Over R every actual inversion needs a certified unit; target separation does not certify all interpolation pivots or generic rank profiles.

**van der Hoeven–Larrieu, final December 2019 version.** [Fast Groebner basis computation and polynomial reduction for generic bivariate ideals](https://www.texmacs.org/joris/ggg/ggg.pdf), Theorems 11, 17, 18 and 20, starts with TWO explicit sufficiently generic field polynomials A,B of total degrees n<=m. Genericity includes a normal Euclidean degree sequence of dominant diagonals and nonzero Y^n coefficient. A concise basis representation, reduction and quotient multiplication can be nearlinear in the dense input scale; the full reduced basis has larger output. Theorem 20 costs O(R(m^2)n log n), with relaxed multiplication R quasi-linear, hence soft(n m^2); at balanced n,m about sqrt J, that is soft(J^(3/2)). Our points have not supplied two balanced generators satisfying those hypotheses. Equation (1) is a different three-generator circuit input with degrees potentially O(J). No nearlinear basis acquisition is imported from fast reduction after the requisite ideal presentation has been acquired.

**Schost–St-Pierre, 2024 and 2025.** [Newton iteration for lexicographic Groebner bases in two variables](https://cs.uwaterloo.ca/~eschost/publications/ScSt24.pdf), Theorem 1.4, lifts an already supplied reduced basis modulo a GOOD maximal ideal of a domain to higher powers, with shape/multiplicity parameters charged. It does not obtain the initial basis over unknown local factors of Z/N. The later [An m-adic algorithm for bivariate Groebner bases](https://cs.uwaterloo.ca/~eschost/publications/ScSt25.pdf) is a randomized domain/fraction-field reconstruction algorithm, not a deterministic prime-free constructor over this composite ring. Neither supplies a new long C-finite seed-intersection theorem here.

The normative separation lemma proves a useful nondegeneracy property of the actual family, but it does not establish the much stronger generic Hilbert-function/degree-drop hypotheses in these ideal algorithms. No failure example for the fixed Cayley constructor, no generic lower bound, and no changed factoring exponent is claimed.

## Cached exact source pins

PDFs and searchable text are in `sources/` beside this report:

- `interpolation-bases.pdf`: `ab2a405bb5f7e86b0efd405ad614f04eb7c0a76da08fef48826dbea81b29e546`.
- `generic-ideals.pdf`: `c5d41a8624d882c4180ccd757219035b67216e3d849d8c02269bf9cbc99c1b89`.
- `newton2024.pdf`: `f34f1374716e29a8ce8cda4f33306b80f3bc7850c582efdca62d407983184907`.
- `madic2025.pdf`: `a6daf5998c6d9bc2012e53a4145513eef033026c49d0c9e30dafa42574f7486a`.
