# Short-seed factoring source: actual bounds and remaining condition

2026-10-22. Scope: classical factoring of every binary semiprime N, n=ceil(log2N), target soft N^(1/6). Read the duplicate-work guard and quantitative-derandomization target in AGENTS.md, lines20226–20330, plus the previous lowspace-factoring.md. No repo/frozen197 changes. This investigates replacement sources, not another compiler argument.

## Outcome

No proven explicit source with o(n) seed and subexponential successful factoring time was constructed or located. There are precise primary small-box/character bounds, but their effective ranges do not establish the needed source. Two concrete results of this investigation are: (i) an exact conditional small-family criterion with the published error terms substituted; (ii) an elementary zero-success counterexample for a tempting short Dixon source.

The statements below identify failures of specified constructions/bounds, not lower bounds on all factoring sources.

## 1. Normalize the HECM source to four parameters, without pretending this makes the seed short

Primary: Lenstra–Pila–Pomerance, [A hyperelliptic smoothness test, II](https://people.maths.ox.ac.uk/pila/HyperII.pdf), Theorem1.1 and Proposition2.1; [PartI](https://math.dartmouth.edu/~carlp/hyperI.pdf), Theorem1.1/Corollary1.2. These are the rigorous prime-by-prime order/success inputs identified previously, not a new theorem here.

PartII samples all degree-five polynomials over F_p: six coefficients, with nonzero leading coefficient and discriminant. Its fixed-order fiber lower bound is p^(9/2)/(24000(logp)^2(loglogp)^2), except for at most p target orders in its central length-p^(3/2) interval. Combining with PartI gives sufficiently smooth order with subexponential inverse probability, denoted rho_p=p^(-o(1)).

Here is a useful exact normalization. For p not2 or5, let

`f(x)=a*x^5+b*x^4+...`, a!=0.

Then

`F(u)=a^(-6)*f(a*u-b/(5*a))`

is monic with zero u^4 coefficient. The substitution x=a*u-b/(5a), y=a^3*v is defined over F_p and preserves the curve and Jacobian order. Conversely, given F and any a!=0,b, this formula uniquely recovers f. Each normalized polynomial therefore has exactly p(p-1) preimages. A full-family isomorphism-invariant property has exactly the same density in the normalized four-coefficient family

`v^2=u^5+c3*u^3+c2*u^2+c1*u+c0`.

Thus one can reduce six uniform field coefficients to four. This still costs 4log2p bits, hence Theta(n) on balanced inputs. Moduli dimension3 and one-dimensional scaling orbits do not imply an o(n)-bit hitting family.

A proposed direct source could enumerate c_i in [1,H]. Its seed is 4log2H+O(1), support H^4. To obtain an N^o(1) deterministic algorithm by direct seed enumeration, one would need H=p^o(1), with per-seed work p^o(1). Even the weaker sixth-rate target permits only H^4<=p^(1/3+o(1)) on balanced N, namely H<=p^(1/12+o(1)). An order-density theorem on this box has not been supplied.

## 2. Exact genus-two small-box theorem and its insufficient range

Primary: Chang, Cilleruelo, Garaev, Hernandez, Shparlinski, Zumalacarregui, [Points on curves in small boxes and applications](https://arxiv.org/pdf/1111.1543), v3, sections1.2/2.2, Theorem8. They study precisely the normalized 2g-coefficient family above. For a fixed class, their displayed complete-sum asymptotic has main scale H^(2g)/p^(2g-1) and error O(sqrt(p)(logp)^(2g)); their paper states the asymptotic range H>=p^(1-1/(4g)+epsilon). The leading normalization is immaterial below. Theorem8 gives at least a constant times min(p^(2g-1),H^(2g+o(1))) distinct classes in the box.

For g=2, the orbit-count comparison requires

`H^4/p^3 >> sqrt(p)*(logp)^4`,

that is

`H >> p^(7/8)*logp`.

This is the actual published asymptotic range, far from p^(1/12), and its full enumeration H^4 has size at least p^(7/2+o(1)). Small-box Theorem8 is much stronger for *distinctness*: H=p^o(1) gives nearly H^4 distinct classes. It does not say their orders hit the smooth subset. A box may contain many different classes and still contain none of the desired class subset; distinctness does not imply smooth-order distribution.

A precise missing theorem is, with G_p the normalized nonsingular smooth-order coefficient set of density rho_p,

`#(G_p intersect [1,H]^4) >= rho_p*H^4 - E(p,H)`

uniformly for every sufficiently large prime p, with `E(p,H)<rho_p*H^4`, at H=p^o(1), or at least H<=p^(1/12-o(1)) for direct sixth-rate enumeration. The published class-count result does not provide E of that strength for G_p.

## 3. The strongest located arbitrary-property transfer has a large support floor

Primary: Banks–Shparlinski, [Sato–Tate, cyclicity, and divisibility statistics on average for elliptic curves of small height](https://arxiv.org/pdf/math/0609144), v4, Theorem12, Corollaries13–15 (the published version renumbers some statements). It applies to ANY F_p-isomorphism-invariant set S of short-Weierstrass elliptic curves, rather than just a fixed smooth test function.

Write rho=#S/p^2 and M_p(S;A,B) for its count in |a|<=A,|b|<=B. Theorem12 estimates deviation from 4rho AB. Corollary13 bounds that deviation by p^o(1) times the minimum of

`A*B^(1-1/nu)*p^((nu+1)/(4nu^2)) + sqrt(A)*B*p^(1/4) + sqrt(ABp)`

and the same expression with A,B exchanged, for fixed integer nu>1. Corollary15 obtains error O(AB*p^(-delta)) if min(A,B)>p^(1/4+epsilon) and AB>p^(1+epsilon).

For a target density rho=p^(-o(1)), the common square-root error must be smaller than the main term:

`sqrt(ABp)*p^o(1) << rho*AB`,

which requires

`AB >> p^(1+o(1))/rho^2`.

This condition describes when this bound certifies a positive count; it is not a lower bound on the true count. It means roughly logp bits of seed and p trials. For balanced N this is N^(1/2+o(1)), above the sixth-rate budget. Even substituting hypothetical perfect cancellation for the short-character-sum term leaves that common error term in Corollary13. Corollary14 offers a different error branch, but its normalized second term is at least sqrt(p) when A,B=p^o(1), so it also does not certify the short-source regime.

This theorem is elliptic, not a theorem for HECM's genus-two property. It is a useful quantitative comparison showing that an arbitrary-property transfer really exists, while preventing transfer of its conclusion into a much smaller unsupported box. Its averaged-over-primes applications cannot cover every hidden prime of an arbitrary semiprime.

## 4. Bounded-conductor character bounds: exact cost and why coarse Sato–Tate is insufficient

Primary: de la Breteche, Sha, Shparlinski, Voloch, [The Sato–Tate distribution in thin parametric families of elliptic curves](https://web.ma.utexas.edu/users/voloch/Preprints/EC-ST_PolyFam_Subgr.pdf), Lemmas3.3–3.7, Corollary3.2, Theorems2.1–2.2. For a fixed non-isotrivial family E(t), let Delta(t) be its discriminant polynomial and U_k(cos theta)=sin((k+1)theta)/sin theta.

Lemma3.4 gives the explicit complete twisted estimate

`|sum_t U_k(cos theta_p(t))*chi(t)| <= (k+1)*deg(Delta)*sqrt(p)`.

Their proof uses Sym^k of the rank-two elliptic sheaf (rank k+1), tensored with a rank-one tame Kummer sheaf. On the punctured line, the relevant first cohomology dimension is at most (k+1)degDelta; algebraic RH supplies the sqrtp weight. These are proven finite-field RH consequences, not an extra analytic GRH hypothesis.

Completion (Lemma3.7) yields, for interval length H<=p, a moment bound of scale

`C_family*k*sqrt(p)*logp`.

Corollary3.2 then gives angle-interval discrepancy of scale

`E_angle = O_family(sqrt(H*sqrt(p)*logp))`.

To infer a positive count in a single angle interval of Sato–Tate measure rho, this bound needs

`H >> sqrt(p)*logp/rho^2`.

Even for rho=p^(-o(1)), this means H>=p^(1/2+o(1)), or balanced cost N^(1/4+o(1)); neither o(n) seed nor sixth-rate direct enumeration follows. Their subgroup result similarly has error O(sqrt(r)*p^(1/4)), and their product-set result error O((#U#V)^(3/4)*p^(1/4)); these certify coarse distributions only above comparable polynomial support thresholds.

More fundamentally, smooth Jacobian/group order is not a fixed angle interval. It is a p-dependent arithmetic set of exact integer orders. Elliptic traces are spaced by p^(-1/2) after normalization; resolving each trace by a moment approximation drives k up to roughly sqrtp, and the printed bound grows with k. Summing discrepancy over many tiny intervals also multiplies the error. For genus2 the full order varies over a p^(3/2)-length integer interval. No low-conductor character expansion for its smoothness indicator was located. One cannot insert that indicator into the fixed-family bound with the same constant.

Analytic GRH for Dirichlet L-functions can improve some least-character-witness questions. It does not turn the smooth-order predicate into a Dirichlet character or justify such an insertion. No conditional all-hidden-prime short-source theorem under GRH was found either.

## 5. Dixon: what independence its actual proof requires

Primary: Dixon, [Asymptotically fast factorization of integers](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf), Mathematics of Computation36(1981),255–260, especially Lemma3 on p259. For N with d distinct odd prime factors, every unit square has 2^d roots. After conditioning on the WHOLE vector of sampled squares, all root assignments at the chosen positions are equally likely. The dependency selector depends on the squares, not the root choices. This gives the probability of repeated trivial relations at most2^(-k). The smooth-relation count separately uses a second-moment estimate.

Limited independence can preserve a second-moment count without preserving that conditional root law. Exact uniform marginals on Z/NZ alone require seed at least log2N bits by support size; pairwise-independent affine sources normally cost two such field/ring elements. They are not o(n)-seed sources. Their joint algebraic constraints also invalidate the step of independently replacing one selected root by another while all squares stay fixed.

A sufficient replacement condition can be stated exactly. For each square transcript w and its selected nonempty dependency lambda(w), let y(w)^2=product_i w_i^lambda_i. The random variable

`R=product_i x_i^lambda_i / y(w)`

lies in K_N={r:r^2=1 modN}. On semiprimes, success is precisely R notin {+1,-1}. If a proposed joint source guarantees, conditioned on w, that R is within total variation epsilon of uniform K_N, its success probability is at least1/2-epsilon. A direct bound on the probability of the two trivial roots would also suffice. No structured short source satisfying either property for the selected dependencies was obtained.

Even very high-wise independence of hidden root signs need not preserve the required product: independent kernel elements conditioned to have product1 are (K-1)-wise uniform, while their K-fold product is fixed. Thus a low-order character/moment calculation cannot simply replace the conditional statement. This example is an independence illustration, not a construction using the unknown factors.

### Concrete failed source, with proof

Take any distribution on positive x_i<=H<sqrtN. Retain those for which w_i=x_i^2 is factor-base-smooth. There is no modular wrap. For any selected dependency lambda making every factor-base exponent even,

`product_i w_i^lambda_i = (product_i x_i^lambda_i)^2`

as an equality of positive integers. Dixon's positive square root y therefore equals product_i x_i^lambda_i, and X is that same product reduced moduloN. Hence X=y modN on every dependency and every seed; gcd(X-y,N)=N, and for odd unit inputs gcd(X+y,N)=1. The factoring success probability is ZERO, regardless of how many smooth relations the source generates. In particular H=N^(1/6) does not supply the desired source. A family centered near sqrtN or using wrapped residues avoids this specific identity but still needs its own uniform smoothness AND nontrivial-root proof.

## 6. Full-source obligations still outstanding

A useful HECM replacement must give curves AND starting-point generation modulo the hidden primes. Proving a smooth-order curve exists in a small list does not automatically preserve the full algorithm's nontrivial-divisor probability: the same exponent may annihilate points modulo both factors, and point distributions/CRT correlations matter. Fixing a rational point by constraining one coefficient also changes the curve family; LPP's full-family theorem does not automatically apply to that slice.

For direct seed enumeration it would suffice to construct a fully specified generator G_N:{0,1}^r -> bounded factoring runs with r+log2T <= n/6+O(logn), and at least one successful seed on every semiprime. An o(n)-seed, T=2^o(n) source would give the stronger N^o(1) result immediately, without a workspace-based simulator. Replacing uniform draws by a short support and invoking total variation is impossible without new information: a distribution on 2^r elements is at distance at least1-2^r/M from uniform on an M-element universe. The theorem may still hold for a short specialized hitting family, but global uniformity alone does not prove it.

The actual quantitative missing input is the box discrepancy condition in section2, together with a matching point/splitting condition, or the conditional root-product balance in section5 for a computable short Dixon source. None is proved here, so no guaranteed sixth-rate factorizer follows from this investigation.
