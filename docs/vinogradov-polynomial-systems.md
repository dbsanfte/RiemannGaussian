# Polynomial-system counting for the next moment iteration

The explicit bounds in [the quantitative descent](vinogradov-quantitative-descent.md)
have excessively large degree costs. The next route is the classical
polynomial-system iteration. The checked continuation proves its algebraic
and congruence-counting ingredients, the quantitative differencing bound,
and nonsingular conditioning for the literal prime-dilated integer count.
The original undilated tail now reaches an attained next polynomial type
at the required quotient endpoint, with low-degree conditioning, endpoint
deletion and exact row transport all proved. Full conditioning, the diagonal
moment iteration and a weaker-constant VK region have since been completed;
see [the current endpoint](vinogradov-cubic-summation.md). The full mixed
iteration with the published constants remains open. The active priority is
[direct literature reproduction](vinogradov-literature-reproduction.md).

The source is [Ford, Section 3](https://arxiv.org/pdf/1910.08209).
The relevant moment-order step also appears in
[Bellotti, Section 2](https://arxiv.org/html/2306.10680v1#S2).

## Exact systems and differences

[`VinogradovPolynomialSystems`](../RiemannGaussian/VinogradovPolynomialSystems.lean)
indexes the active polynomials by `Fin m`, where `m=k-d`. Its `HasType`
records

\[
 \deg F_i=i+1,\qquad
 \operatorname{lc}(F_i)=
 (d+i+1)^{\underline d}\,2^eT,
 \qquad 0\le i<m.
\]

Here the descending factorial is an exact integer; `e` is shared by the
whole system. The first `d` zero polynomial coordinates of the full system
are omitted from this indexing. The corresponding low-degree constraints
on the separate monomial tail must still be retained when defining the
conditioning counts.

The module proves that ordinary monomials have the starting type, and that
common input translation preserves the type. It defines the literal
difference

\[
 \Delta_h f(X)=f(X+h)-f(X)
\]

and proves its degree drops by exactly one for a nonzero integer step,
with leading coefficient `deg(f)*lc(f)*h`. The first linear coordinate
becomes constant. Removing that constant coordinate gives the next type
`(d+1,hT)`, with the same `e`. For `1<=h<=P`, the new parameter lies in
`[T,PT]`.

## Actual moment and residue bounds

[`VinogradovPolynomialRigidity`](../RiemannGaussian/VinogradovPolynomialRigidity.lean)
proves that every triangular system with cancellable leading coefficients
has exactly the same two-sided weighted equations as ordinary power sums.
Arbitrary signed weights are preserved. The proof works over quotient
rings as well as integers, so it does not assume that a prime-power residue
ring is a field.

Over integers, every positive-parameter type therefore has exactly the
ordinary degree-`m` Vinogradov moment, at every moment order and interval
length. All existing elementary moment bounds transfer without a
coefficient-size allowance.

For a prime `p>max(k,2)` with `p ∤ T`, all leading coefficients are proved
to be units modulo every `p^r`. Consequently:

- Each complete nonsingular polynomial target has at most `m!` ordered
  residue tuples.
- Any correlated finite family of complete targets costs its actual
  cardinality times `m!`.
- Different coordinate precisions `e_i<=r` cost
  `m!*p^(sum_i(r-e_i))`.

The terminal `type_integer_congruence_card_le` applies to the literal
integer equations. For `r<=k`, it bounds the number of residue tuples
distinct modulo `p` satisfying

\[
 \sum_{j=1}^{m}F_i(u_j)\equiv a_i
 \pmod {p^{\min(d+i+1,r)}}\quad(0\le i<m)
\]

by

\[
 m!\,p^{(r-d)(r-d-1)/2}\qquad(d\le r).
\]

The theorem also covers `r<d`, using natural truncated subtraction in the
exponent. The target integers are arbitrary; unattainable targets are
included. No polynomial fibre bound is assumed as an input.

## Quantitative mixed differencing

[`VinogradovMixedMoments`](../RiemannGaussian/VinogradovMixedMoments.lean)
identifies the complete mixed moment with its actual full-frequency tuple
count. Bounded complex masks are dominated by that complete count after
forming the even moment. Hölder then pays the intermediate difference
power without a pointwise comparison of oscillating sums.

[`VinogradovDifferenceEnergy`](../RiemannGaussian/VinogradovDifferenceEnergy.lean)
proves the exact residue-energy expansion. Write `q` for the congruence
modulus, `H=floor(P/q)`, and `V(z)` for the full polynomial-frequency vector.
Then

\[
 I(\alpha)=\sum_{c\bmod q}
 \left|\sum_{\substack{1\le z\le P\\z\equiv c\bmod q}}
 e(V(z)\cdot\alpha)\right|^2
 =P+2\operatorname{Re}\sum_{h=1}^{H}
 \sum_{1\le z\le P-hq}e((V(z+hq)-V(z))\cdot\alpha).
\]

The endpoint mask is literal; no periodic completion or omitted boundary
is used. For any original tail polynomial `f`, let

\[
 L=\int I(\alpha)^M|f(\alpha)|^{2s}\,d\alpha,
 \qquad J=\int |f(\alpha)|^{2s}\,d\alpha,
 \qquad t=\frac{M}{2(M-1)},\quad M\ge2,
\]

and let `K_h` be the complete mixed moment

\[
 K_h=\int\left|\sum_{1\le z\le P}
 e((V(z+hq)-V(z))\cdot\alpha)\right|^{2(M-1)}
 |f(\alpha)|^{2s}\,d\alpha.
\]

[`VinogradovMixedDifferencing.exists_difference_bound`](../RiemannGaussian/VinogradovMixedDifferencing.lean)
proves that, when `q<=P`, a single fixed `1<=h<=H` satisfies

\[
 \boxed{L\le\max\left\{(2MP)^M J,
 2(2H)^M K_h^t J^{1-t}\right\}.}
\]

It first proves a stronger sum over the separate `K_h` allowances. Finite
Hölder is applied before integration; only then is an attained maximum
chosen. Weighted convexity with weight `1/(2M)` and Bernoulli's inequality
give exactly the displayed factor two in the second alternative. If
`P<q`, the module proves `L=P^M J` exactly.

[`VinogradovPolynomialDifferencing.exists_typed_difference_bound`](../RiemannGaussian/VinogradovPolynomialDifferencing.lean)
applies this inequality to the literal type system. Its selected step is
`h*q`; the next system has type `(d+1,T')`, where
`T'=(h*q)*T` and `T<=T'<=P*T`. The first active difference contributes a
constant unit phase and is removed exactly from the complete sum's norm.
**Every original tail coordinate remains present**, including the first
`d` coordinates and the newly constant polynomial coordinate. All boundary
majorants, integral exchanges, exponent interpolation and type conditions
are proved; no mixed-moment estimate is supplied as an assumption.

## Nonsingular count to the next polynomial type

[`VinogradovPolynomialConditioning.configuration_integral_le`](../RiemannGaussian/VinogradovPolynomialConditioning.lean)
transports the proved modular fibre count to the actual configuration
energy. The full tuple residue, polynomial coefficients and arbitrary
complex configuration weights are retained. The only tail condition is
the displayed divisibility of each active coordinate by its degree modulus.

[`VinogradovPolynomialNonsingular.prime_dilated_count_le`](../RiemannGaussian/VinogradovPolynomialNonsingular.lean)
discharges those divisibilities for the literal tail with entries
`((p*q)*x)^j`, `1<=j<=k`. Write `S_ns` for the actual integer count with
`m=k-d` block variables on each side, each block distinct modulo `p`,
`1<=z,w<=P`, and `s` monomial-tail variables on each side in `[1,Q]`.
It counts the full system

\[
 \sum_{i=1}^{m}\bigl(V_j(z_i)-V_j(w_i)\bigr)
 +(pq)^j\sum_{i=1}^{s}(x_i^j-y_i^j)=0
 \quad(1\le j\le k),
\]

where the first `d` coordinates of `V` are zero and the rest are the
active type polynomials. For a prime `p>max(k,2)`, `p ∤ T` and
`1<=r<=k`, Lean proves

\[
 \boxed{S_{\rm ns}\le D\,L,\qquad
 D=m!\,p^{(r-d)(r-d-1)/2}.}
\]

Natural truncated subtraction is used when `r<d`. Here `L` is the literal
residue mixed moment above with modulus `p^r` and the full dilated tail.
The interval endpoints are unchanged. Exact factorization over complete
tuple colours pays the admissible block fibres by the original residue
energy power. Orthogonality identifies the integral with the actual
integer count; neither an analytic estimate nor a modular counting estimate
is an input.

[`VinogradovNonsingularDescent.monomialTail_moment`](../RiemannGaussian/VinogradovNonsingularDescent.lean)
identifies the full tail moment with `J_{s,k}(Q)` when `p,q>0`, by exact
coordinate reindexing and dilation. Its `exists_nonsingular_descent`
then combines the count bound and differencing: for `m>=2`, `p^r<=P`,
`H=floor(P/p^r)` and `t=m/(2(m-1))`, an attained `1<=h<=H` gives

\[
 \boxed{S_{\rm ns}\le D\max\left\{(2mP)^mJ_{s,k}(Q),
 2(2H)^m K_h^t J_{s,k}(Q)^{1-t}\right\}.}
\]

The selected system is the literal difference at step `h*p^r`, has type
`(d+1,T')` with `T'=(h*p^r)*T` and `T<=T'<=P*T`, and keeps every original
monomial-tail equation in the same ambient space.

This is the nonsingular stage **after prime dilation of the tail**. It
does not bound the full original `K` count by silently assuming its tail
already lies in one residue class. The earlier efficient-congruencing
module `VinogradovNonsingularConditioning` remains a separate, unchanged
part of the repository.

## Low-degree tail conditioning

[`VinogradovLowDegreeTail.exists_tail_class_bound`](../RiemannGaussian/VinogradovLowDegreeTail.lean)
now controls the original nonsingular count before prime dilation. Let
`S_3(p)` count the same full system with tail dilation `q`, and let
`S_4(c,p)` retain exactly those tail entries in one fixed residue class
`c mod p`, still in the original interval `[1,Q]`. For `d<p`, `d<=s`,
`s>=1`, prime `p` and `q>0`, it proves that some fixed class satisfies

\[
 \boxed{S_3(p)\le d!\,p^{2s-d}\,S_4(c,p).}
\]

All active polynomial coefficients are arbitrary in this step. The first
`d` coordinates of the block vanish, leaving exact integer tail equations.
The proof cancels the nonzero integer dilation before reducing modulo `p`;
it does not require `p` and `q` to be coprime. Newton's identities bound
every low-degree residue signature fibre by `d!*p^(s-d)`, including repeated
residues. The complete configuration energy is partitioned by that
signature. Finite Hölder contributes `p^(s-1)`, and the sum over all `p`
class integrals is bounded by its attained maximum **after integration**.
Thus the displayed coefficient is paid on the actual original count.

The selected class is still in `[1,Q]`. Reindexing it as a shifted dilated
interval can introduce one extra endpoint. The following continuation
pays that endpoint and proves the exact transport to prime dilation.

## Endpoint deletion and exact row transport

[`VinogradovEndpointDeletion.mixedMoment_succ_le`](../RiemannGaussian/VinogradovEndpointDeletion.lean)
proves, for arbitrary original integer-frequency maps,

\[
 \boxed{K(N+1)\le2K(N)\qquad(N\ge16s^2,\ s\ge1),}
\]

where only the tail length changes and its moment order is `2s`. The
actual diagonal tail configurations give `K(N)>=N^s*J_block`. A two-term
weighted power inequality then absorbs the extra unit Fourier atom using
that reserve. The full block and every tail equation remain coupled.

[`VinogradovResidueEndpoint.exists_floor_tail_bound`](../RiemannGaussian/VinogradovResidueEndpoint.lean)
applies this to the existing exact residue quotient injection. Its
completion to `floor(Q/p)+1` is first paid at the integer-count level;
then the endpoint theorem gives length `floor(Q/p)` with factor two.
The original nonsingular count is consequently at most
`2*d!*p^(2s-d)` times one shifted mixed count at that endpoint.
The checked `floor_condition_of_packet` derives the needed length from
`p<=2*M` and `32*s^2*M<=Q`.

The affine tail is literally `q*(p*x+xi-p)`, where `0<=xi<p`. Set
`c=q*(p-xi)`. [`VinogradovBinomialRows`](../RiemannGaussian/VinogradovBinomialRows.lean)
constructs

\[
 \Phi_j(X)=\sum_{\ell=0}^{j}
 \binom{j}{\ell}c^{j-\ell}\Psi_\ell(X)
\]

and proves that this unit-triangular row operation preserves all equations
through the same degree cutoff. Its exact polynomial type is unchanged:
the same degrees, leading coefficients, `T` and shared binary exponent.
The factor `q` is included in the shift. The degree-zero equation has the
same tail count on both sides, so it is retained during transport.

[`VinogradovRowTransport.shifted_count_eq`](../RiemannGaussian/VinogradovRowTransport.lean)
identifies the full shifted solution count with the literal prime-dilated
count for `Phi`. Nonsingularity, original block windows and all low-degree
tail equations remain unchanged. This is an exact collision equivalence.

## The composed original nonsingular step

[`VinogradovPolynomialConditionedDescent.exists_conditioning`](../RiemannGaussian/VinogradovPolynomialConditionedDescent.lean)
joins the preceding bounds. With `k=d+m`, an eligible prime
`p>max(k,2)`, `p ∤ T`, `1<=r<=k`, `d<=s`, `s>=1` and
`16*s^2<=floor(Q/p)`, it proves

\[
 \boxed{S_3(p)\le C_{p,m,d,r,s}\,
 L(P,\lfloor Q/p\rfloor;\Phi;p,q,r),}
\]

where

\[
 C_{p,m,d,r,s}
 =2d!m!\,p^{\,2s-d+(r-d)(r-d-1)/2}.
\]

The exponent uses natural truncated subtraction as before. `Phi` is an
attained binomial row transform of the original system; its type is
proved. No analytic or congruence-counting estimate is a premise.

Its `exists_descent` further assumes `m>=2` and `p^r<=P`. For
`H=floor(P/p^r)`, `t=m/(2(m-1))` and `J=J_{s,k}(floor(Q/p))`, an attained
fixed `1<=h<=H` then gives

\[
 \boxed{S_3(p)\le C_{p,m,d,r,s}
 \max\left\{(2mP)^mJ,\;2(2H)^m K_h^tJ^{1-t}\right\}.}
\]

The next system is the literal finite difference of the transformed
polynomials at step `h*p^r`. It has type `(d+1,T')`, with
`T'=(h*p^r)*T` and `T<=T'<=P*T`. The complete original tail stays in the
same ambient coordinates. The left side is still the count whose blocks
are distinct modulo the given eligible prime; it is not yet the
unrestricted `K` count.

## The unrestricted count: type maximum and repeated tuples

[`VinogradovTypeMaximum.exists_maximizer`](../RiemannGaussian/VinogradovTypeMaximum.lean)
proves that the complete mixed count attains its maximum over all systems
of the same type `(d,T)`. Neither the common binary exponent nor the lower
polynomial coefficients are bounded. The proof uses the actual integer
count, bounded above by `P^(2m)*Q^(2s)`, rather than compactness of a
coefficient space. Doubling the polynomial block increments its binary
exponent, so at the maximizing system `F*` the actual count satisfies
`K(2F*,u)<=K(F*,u)` with exactly the same original tail `u`.

[`VinogradovMixedRepeated.repeated_integral_le`](../RiemannGaussian/VinogradovMixedRepeated.lean)
retains three Hölder factors:

\[
 \int |F|^{2m-2}|F_2||f|^{2s}
 \le K(F)^{1-1/m}K(2F)^{1/(2m)}J^{1/(2m)}.
\]

Here `F_2` doubles only the polynomial frequencies. No invariance of the
mixed moment under this partial doubling is asserted. The actual maximum
supplies the required comparison.
[`VinogradovMixedExceptional`](../RiemannGaussian/VinogradovMixedExceptional.lean)
compresses and permutes literal repeated tuples, retaining all tail
equations. It counts unordered position pairs on both original blocks,
obtaining

\[
 E\le m^2K_*^{1-1/(2m)}J^{1/(2m)},\qquad K_*\ge P^mJ.
\]

For `m>=2` and `P>=4*m^4`, the diagonal reserve proves `2E<=K*`, including
zero moments and equality at the threshold. Consequently
[`exists_count_reduction`](../RiemannGaussian/VinogradovPolynomialExceptional.lean)
proves `K(F)<=K(F*)<=2*S_1(F*)`, where both polynomial blocks in `S_1`
are physically distinct. The maximizing system may differ from the
original one, but its type parameter, full degree, tail and endpoints are
unchanged.

## One eligible prime and the full conditioning bound

[`VinogradovTwoBlockPacket`](../RiemannGaussian/VinogradovTwoBlockPacket.lean)
uses the unordered discriminant

\[
 \Delta=T\prod_{i<j}|x_i-x_j|\prod_{i<j}|y_i-y_j|,
 \qquad 0<\Delta\le P^{d+2\binom m2}.
\]

This simultaneously retains both original blocks and the type multiplier.
A packet whose prime product exceeds this budget contains a prime that
avoids `T` and separates both blocks. The proof constructs `R` primes in
`(M,2^R*M]` by iterated Bertrand. Thus the explicit sufficient budget is
`P^(d+2*choose(m,2))<M^R`. It does **not** presume a packet in `(M,2M]`.

[`VinogradovPolynomialPrimeTransfer.exists_prime_carrying_count`](../RiemannGaussian/VinogradovPolynomialPrimeTransfer.lean)
covers the complete distinct solution set with this one packet, then
selects the largest eligible nonsingular count. For the actual maximizing
system this gives `K(F)<=2*R*S_3(p,F*)` at one fixed prime, with no supplied
moment estimate.

[`VinogradovUnrestrictedConditioning.exists_conditioning`](../RiemannGaussian/VinogradovUnrestrictedConditioning.lean)
composes this with all preceding tail and congruence bounds:

\[
 \boxed{K(F)\le
 4R\,d!\,m!\,p^{\,2s-d+(r-d)(r-d-1)/2}
 L(P,\lfloor Q/p\rfloor;G;p,q,r).}
\]

The exponent uses natural truncated subtraction as in the Lean theorem.
The selected `G` has type `(d,T)` with an attained binary exponent.
The complete original tail is retained, including its original dilation
`q`. The explicit hypotheses include `m>=2`, `P>=4*m^4`, `0<T<=P^d`,
`d+m<=M`, the packet budget above, `1<=r<=d+m`, `d<=s`, `s>=1`, `q>0`,
and `16*s^2*(2^R*M)<=Q`. There is no `p^r<=P` requirement for this
conditioning theorem.

## Remaining iteration and quantitative costs

The unrestricted conditioning step is now proved with the stated Bertrand
packet costs. Its direct diagonal branch now closes an all-endpoint
`s -> s+k` iteration: the actual homogeneous moment at order `(7k+1)k`
has defect at most `k^2/256` and coefficient at most `2^(18k^6)`, with no
moment premise. The small-endpoint reserve is retained as a maximum,
rather than multiplied into each recursive coefficient. See
[the explicit diagonal descent](vinogradov-diagonal-descent.md).

Each iteration must choose an eligible prime for its new type parameter;
the preceding prime generally divides `T'`. Also, `p<=2M` and `M^r<=P`
alone would not imply `p^r<=P`. If `P<p^r`, the existing exact diagonal
identity `L=P^m*J` must be used. If `p^r<=P`, the proved fixed-displacement
differencing bound supplies the next type.

The [fixed-width packet continuation](vinogradov-narrow-packet.md) now
proves a packet in `(M,8M]`, improves the moment coefficient to
`(2^62*k^6)^(k^3)`, and performs Gaussian and Dirichlet transport at the
actual order `(7k+1)k`. Its literal Dirichlet block has uniform coefficient
five and saving `1/(8192*k^2)` on the displayed rectangle. The generic
`exists_conditioning_of_packet` theorem retains any proved packet's
cardinality, upper endpoint and full product budget.

The general mixed-type iteration and the literature's denser packet are
now the reproduction priorities. `VinogradovLiteratureStep` proves the
next-type count equality and the full two-branch differencing inequality,
and composes them with unrestricted conditioning. `VinogradovResidueMonotone`
now proves tail monotonicity at cost one, and `VinogradovLiteratureIteration`
proves the finite backward induction from the diagonal base through to
the original homogeneous moment. It retains the exact conditioning cost
and all finite packet and endpoint hypotheses.
`VinogradovPowerConditioning` now couples the selected prime to its literal
quotient moment, paying the reduced exponent `e-lambda` before using the
packet upper endpoint. `VinogradovFordScales` proves a nonpositive
remainder for Ford's original scale recurrence under its depth restriction.
`VinogradovFordIteration.moment_power_bound` then proves the actual original
moment bound with the published updated defect and an explicit coefficient
independent of the physical endpoint. `VinogradovFordCoefficient` now
proves that full coefficient at most `k^(3k)*eta^(4s+k^2)`, deriving
`lambda>=s` from the actual diagonal lower bound. `VinogradovFordMoment`
transports it to the literal homogeneous moment.
`VinogradovFordTailThreshold.published_height_bound` pays every recursive
quotient-size condition at the original `P>=V^(k+1)` starting height.
`VinogradovFordSchedule` constructs the backward scales using Ford's
stationary lower bound. `VinogradovFordParameters` constructs the integer
cutoffs and pays every remaining scale/type condition, including rounding
at exact roots. `VinogradovFordGlobalStep.all_endpoint_bound` pays small
endpoints with the original maximum coefficient.
`VinogradovFordMomentSequence.iterated_moment_bound` starts at the proved
diagonal moment and iterates at every positive integer endpoint, with no
source moment premise. `VinogradovFordRank` now constructs the published
rounded rank and maximal depth and proves their scalar admissibility.
`VinogradovFordSelectedIteration.selected_moment_bound` removes that
schedule premise from the actual moment estimate, retaining dense prime
supply. `VinogradovFordScaleError`, `VinogradovFordQuantitativeScale` and
`VinogradovFordDefectRate` prove Ford's original numerical first-scale
budget and normalized defect recurrence (3.14), with constants unchanged.
The selected sequence includes the final rank-k step down to Delta<=k-1.
`VinogradovFordLowerDefect` proves positivity through every step, and
`VinogradovFordPotentialIteration.potential_cumulative` sums the signed
potential gain with the exact 1.34/k reciprocal-error allowance. Potential
endpoint evaluation and the closed coefficient bound still require proof. The sharper
Bellotti 2.3 scale recurrence remains a distinct audit; see the
[reproduction ledger](vinogradov-literature-reproduction.md).
The
[summed all-scale continuation](vinogradov-cubic-summation.md) already
pays adaptive coverage and the zero detector for the weaker-constant
region. That proved region and the independent RH signed-floor obstruction
are unchanged by the new mixed-system interface.
