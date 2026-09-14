# Vinogradov–Korobov formalization: signed congruencing and Gaussian resonance

**Status:** the exact finite logarithmic expansion, product-shift averaging
of actual Dirichlet blocks, transport through their full damping, shifted
moment domination and the two-Hölder reduction of the actual polynomial
sum are proved. Newton's identities now give the complete diagonal-range
moment bound and an elementary estimate at every order, for arbitrary
finite sets of distinct integers. Both moment factors in the actual
Gaussian product-sum bound have explicit costs. Complete nonsingular
power-sum fibres are now controlled at every prime-power precision,
including the unequal degree-by-degree moduli used in congruencing.
The signed version retains both sign classes and an arbitrary common
translation, and now bounds the nonsingular block projection of the
original moment equations when both tails lie in one coarse residue class.
The complete coarse-conditioned count also covers original blocks sharing
a residue modulo p^a, with distinct normalized next digits. Exact target
partition and the actual signed count now control the full original
weighted moment by its finer block-residue energies, for all admissible
positive blocks and tails up to the finite endpoint. Exact product
factorization and the first finite Hölder estimate now reduce that energy
to an actual mixed-moment maximum, retaining arbitrary complex tail weights.
Both original collision contributions now have explicit bounds, giving the
actual finite conditioning recurrence. Its deeper remainder now has an
explicit power saving at the elementary exponent, with rounded cutoffs and
all constants paid. The normalized signed recurrence now couples these
steps, retaining the full intermediate energy sum. Initial global conditioning
and a first independent exponent improvement of 1/(3k) are now proved for
every k>=2,u>=k and all sufficiently large endpoints. That exponent now
pays both actual quotient moments in the full signed recurrence and the
original Riesz carrier bound. An exact audit shows that lowering the
exponent improves the deep remainder while retaining identical intermediate
energies after restoring the source scale. A uniform finite profile
induction now independently bounds every later energy under constructed
descendant cutoffs, producing a negative initial profile. It improves every
proved eventual exponent strictly above critical and replaces the complete
initial allowance in the original Riesz bound. A uniform improvement above
each fixed positive defect now closes the infimum argument and proves
the critical high-order exponent plus every positive epsilon. Both actual
Korobov product moments and the original Riesz profile receive it. Uniform
parameter costs and the complete joint resonance estimate remain open.
The Vinogradov–Korobov zeta growth estimate
and zero-free region remain unproved in this repository. No external
analytic estimate is installed as an axiom or as a claimed discharged premise.

The research lead is [Bellotti (2023), Section 8](https://arxiv.org/html/2306.10680v1#S8).
That argument connects shifted logarithmic sums to polynomial phases and
then uses high mean-value estimates. The current implementation closes the
averaging, phase approximation, damping transport and moment reduction;
the stronger high-moment and resonance estimates needed for the VK saving
remain open.

## Exact signed expansion

For every natural degree `k` and **every `x ≥ 0`**, define

```math
P_k(x)=\sum_{j=0}^{k-1}\frac{(-1)^j x^{j+1}}{j+1},
\qquad R_k(x)=\int_0^x\frac{u^k}{1+u}\,du.
```

[VinogradovKorobovLogPhase](../RiemannGaussian/VinogradovKorobovLogPhase.lean)
proves the exact identity and bounds

```math
\log(1+x)=P_k(x)+(-1)^kR_k(x),\qquad
0\le R_k(x)\le\frac{x^{k+1}}{k+1}.
```

The proof uses an exact recurrence for consecutive integrals, not a
convergence assumption at a series endpoint. The companion complex identity
keeps `exp(-it*(-1)^k*R_k(x))` as a separate factor before bounding its effect.

## Literal powers and coupled products

[VinogradovKorobovBilinearPhase](../RiemannGaussian/VinogradovKorobovBilinearPhase.lean)
identifies the actual power `(z+a*b)^(-it)` for `z>0`, `a,b≥0` with its
unit base phase and `exp(-it log(1+a*b/z))`. The polynomial phase is exactly

```math
-tP_k(ab/z)=\sum_{j=0}^{k-1}
\frac{-t(-1)^j}{(j+1)z^{j+1}}a^{j+1}b^{j+1}.
```

For arbitrary finite complex weights `w(a,b)`, the error between the whole
logarithmic sum and the whole polynomial sum is at most

```math
\sum_{a,b}|w(a,b)|\,
\frac{|t|(ab/z)^{k+1}}{k+1}.
```

Both factors, every weight and the complete polynomial sum survive. The
proof reuses the repository's unit-phase Lipschitz theorem from
[EtaCubicBoundaryTest](../RiemannGaussian/EtaCubicBoundaryTest.lean).
The unweighted version pays the explicit cardinality and box sizes.

## Actual blocks, exact boundaries and the remaining polynomial sum

[VinogradovKorobovBlock](../RiemannGaussian/VinogradovKorobovBlock.lean)
proves an exact product-shift identity for every real `z>0`, every real
height `t`, integer block length `L`, and finite integer shift sets `A,B`.
Write `m=|A||B|`, `f(n)=(z+n)^(-it)` and

```math
C_p=\sum_{j\lt p}f(j)-\sum_{j\lt p}f(L+j),\qquad
C=\sum_{a\in A,b\in B}C_{ab}.
```

The theorem `averaged_dirichlet_identity` keeps the original signed boundary:

```math
m\sum_{n\lt L}f(n)=
\sum_{n\lt L}e^{-it\log(z+n)}
  \sum_{a\in A,b\in B}e^{-it\log(1+ab/(z+n))}+C.
```

Replacing only the inner logarithmic phases by their degree-`k` polynomials
gives `Q_k`. The outer phases remain coupled. For nonempty shift sets with
`0≤a≤M₁`, `0≤b≤M₂`, put

```math
E=\frac{|t|}{k+1}\left(\frac{M_1M_2}{z}\right)^{k+1},\qquad
F_L=\frac{Q_k+C}{m}.
```

`block_sub_approximation_le` proves the complex approximation
`|sum_(n<L) f(n)-F_L|≤L E`. This includes the exact boundary before the
error is bounded. `dirichlet_norm_le_coupled` retains `Q_k+C` under one norm;
`dirichlet_norm_le` separately pays

```math
\frac{|C|}{m}\le
2\left(\frac{\sum_{a\in A}a}{|A|}\right)
 \left(\frac{\sum_{b\in B}b}{|B|}\right).
```

Thus the boundary allowance uses the actual mean shifts, and the exact
signed expression remains available upstream. All endpoints are integers
with an explicit half-open block convention. The identities hold even
when a shift exceeds the block length; no omitted rounding correction or
small-ratio assumption is needed. A separate exact identity also allows
arbitrary complex shift weights.

[VinogradovKorobovDamping](../RiemannGaussian/VinogradovKorobovDamping.lean)
then applies exact Abel summation. For any nonnegative decreasing weights
`w_n`, the weighted approximation formed from the prefixes `F_l` satisfies

```math
\left|\sum_{n=0}^{N}w_n f(n)-
\left(w_N F_{N+1}+\sum_{n\lt N}(w_n-w_{n+1})F_{n+1}\right)\right|
\le E\sum_{n=0}^{N}w_n.
```

`feature_approximation_error_le` discharges the weight conditions for the
literal `zetaPrimeFeature s (a+n)`, for every positive integer `a` and
`Re(s)≥0`. The allowance pays its actual damping mass. This connects the
product-phase argument to the Dirichlet terms already used by the zeta
chain; it does not yet bound the surviving polynomial approximation.

## Exact mean values and their arithmetic correlations

[VinogradovMeanValue](../RiemannGaussian/VinogradovMeanValue.lean) proves,
for every finite family of integer frequency vectors `v_i`,

```math
\int_{(\mathbb R/\mathbb Z)^d}
\left|\sum_i e^{2\pi i\langle v_i,\alpha\rangle}\right|^{2s}d\alpha
=\#\left\{(x,y):\sum_{j=1}^s v_{x_j}=\sum_{j=1}^s v_{y_j}\right\}.
```

The monomial vector `(n,n²,...,n^k)` gives the actual Vinogradov
mean value on `1,...,N`. The torus expression is explicitly identified
with the usual polynomial-exponential integral on the unit cube. For
`k≥1`, the first mean value is proved to equal `N` exactly.

The upstream weighted identity keeps all matching-frequency cross terms,
`w_i*conj(w_j)`. Thus later bounds can use the actual frequency collisions
rather than assume independent phases. This is the classical moment/count
identity, not a new quantitative saving or a historical novelty claim.

## Power-sum rigidity and quantitative base estimates

[VinogradovPowerSumRigidity](../RiemannGaussian/VinogradovPowerSumRigidity.lean)
evaluates Mathlib's proved Newton identities at the actual integer tuples.
Equal power sums through degree `r` force equal elementary symmetric
coefficients, hence the same root polynomial and the same multiset,
including repeated entries. For any injective integer-valued family on
`N` indices and `r≤k`, `collision_iff_perm` therefore proves that every
collision is a permutation of the original tuple. There are at most `r!`
such ordered tuples. The resulting bound is

```math
J_{r,k}\le r!N^r\quad(r\le k),\qquad
J_{r,k}\le m!N^{2r-m}\quad(m=\min(r,k)).
```

The second estimate uses the first at order `m` and pays the pointwise
cardinality bound only for the extra powers. Both are unconditional,
uniform in the chosen finite integer set, and include empty sets and
zero orders. The proof keeps multiplicity before bounding permutation
counts. This is a formalization of the classical diagonal argument;
no historical novelty is claimed. It supplies quantitative base estimates,
not the stronger high-order saving needed for the full VK argument.

## Prime-power rigidity and unequal congruence moduli

[VinogradovPrimePowerRigidity](../RiemannGaussian/VinogradovPrimePowerRigidity.lean)
retains the full Jacobian of the first `k` power sums. Its determinant is

```math
\det\left(jx_i^{j-1}\right)_{1\le j,i\le k}
=k!\prod_{i\lt l}(x_l-x_i).
```

For a prime `p>k` and entries distinct modulo `p`, every factor is nonzero.
The proof pays the exact integer nonlinear remainder when lifting from one
precision to the next; it does not assume a linearized congruence. Newton
identities first identify the possible residue orderings. The resulting
`prime_power_permutation` and `nonsingular_fibre_le_factorial` show that
any complete power-sum vector modulo `p^n` has at most `k!` nonsingular
ordered tuples among the canonical representatives `0,...,p^n-1`.
This includes empty target fibres. `nonsingular_preimage_le` keeps arbitrary
correlated target sets, with cost at most `k!` times their actual cardinality.

[VinogradovAnisotropicCongruence](../RiemannGaussian/VinogradovAnisotropicCongruence.lean)
then allows each equation to have its own precision `e_j≤n`. For every
prescribed vector `a`, Lean proves

```math
\#\left\{x\in\{0,\ldots,p^n-1\}^k:
\begin{array}{l}
x_i\not\equiv x_l\pmod p\quad(i\ne l),\\
\sum_i x_i^j\equiv a_j\pmod{p^{e_j}}\quad(1\le j\le k)
\end{array}\right\}
\le k!\,p^{\sum_{j=1}^k(n-e_j)}.
```

Here targets are taken as canonical residues at their respective moduli.
The code connects these congruences to the literal natural power sums,
including all reductions between moduli. Specializing to `n=kb` and
`e_j=jb`, `degree_moduli_card_le` gives the uniform bound

```math
\boxed{k!\,p^{\,b k(k-1)/2}}.
```

These are classical nonsingular congruencing ingredients. Their signed and
translated form is proved next. The more general coarse-conditioned count in
[Wooley (2012), Section 4, Lemma 4.1](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf)
is now proved below for canonical residue representatives. The ensuing
high-moment iteration remains open.

## Keeping the signs through reconstruction and conditioning

For a fixed sign pattern `epsilon_i` in `{+1,-1}`, let `r_+` and `r_-`
be its two class sizes. In every domain where `1,...,k` are nonzero,
[VinogradovSignedRigidity.signed_fibre_card](../RiemannGaussian/VinogradovSignedRigidity.lean)
proves that a tuple of distinct entries has exactly

```math
r_+!\,r_-!
```

ordered realizations of its complete first-`k` signed moment vector.
Each realization permutes entries within the original sign classes.
Crossing the positive and negative entries converts the signed equations
into ordinary Newton identities. Distinctness prevents an entry from
cancelling against an opposite sign from the same original tuple. The
proof preserves the colour partition before counting its permutations.
This is a structural refinement of the factorial allowance, not a claim
of historical novelty.

[VinogradovWeightedLifting.weighted_prime_power_rigidity](../RiemannGaussian/VinogradovWeightedLifting.lean)
keeps arbitrary integer coefficients nonzero modulo `p` throughout the
exact nonlinear lifting argument. Both signs satisfy that condition.
[VinogradovSignedCongruence.degree_moduli_card_le](../RiemannGaussian/VinogradovSignedCongruence.lean)
therefore proves, for every prime `p>k`, integer `eta`, and target vector `a`,

```math
\#\left\{x\in\{0,\ldots,p^{kb}-1\}^k:
\begin{array}{l}
x_i\not\equiv x_l\pmod p\quad(i\ne l),\\
\sum_i\epsilon_i(x_i-\eta)^j\equiv a_j\pmod{p^{jb}}
\quad(1\le j\le k)
\end{array}\right\}
\le r_+!\,r_-!\,p^{\,b k(k-1)/2}.
```

Before taking this product of coordinate refinement costs,
`nonsingular_preimage_le` retains an arbitrary correlated family of
complete targets with cost `r_+!*r_-!` per target. The exact algebraic
fibre description remains available upstream of either inequality.

[VinogradovConditionedMoment.conditioned_power_difference](../RiemannGaussian/VinogradovConditionedMoment.lean)
connects these congruences to the original equations. If

```math
\sum_i\epsilon_i x_i^d+\sum_l v_l^d
=\sum_i\epsilon_i y_i^d+\sum_l w_l^d\qquad(1\le d\le k),
\qquad v_l\equiv w_l\equiv\eta\pmod{p^b},
```

then the full binomial translation, including its degree-zero identity,
gives

```math
p^{jb}\mid\sum_i\epsilon_i(x_i-\eta)^j
           -\sum_i\epsilon_i(y_i-\eta)^j\qquad(1\le j\le k).
```

The terminal theorem `conditioned_block_card_le` applies the preceding
count to the actual nonsingular residue blocks that admit such tail
completions, for every fixed `y`. The tails may be arbitrary integer tuples;
their existence implies the congruences. This counts the projected blocks,
**not the number of their tail completions or the whole moment**.

These base counts require distinct residues modulo `p`. The next theorem
also covers a common coarse residue class, including `a>0`.

## Original tuples in a common coarse residue class

[VinogradovCoarseCongruence.conditioned_residue_card_le](../RiemannGaussian/VinogradovCoarseCongruence.lean)
proves, for `1≤k<p`, `0≤a≤b`, every fixed sign pattern, integer `eta`,
natural residue `xi` and integer target vector `m`,

```math
\#\left\{x\in\{0,\ldots,p^{kb}-1\}^k:
\begin{array}{l}
x_i\equiv\xi\pmod{p^a}\quad(1\le i\le k),\\
\lfloor x_i/p^a\rfloor\not\equiv\lfloor x_l/p^a\rfloor
  \pmod p\quad(i\ne l),\\
\sum_i\epsilon_i(x_i-\eta)^j\equiv m_j\pmod{p^{jb}}
  \quad(1\le j\le k)
\end{array}\right\}
\le r_+!\,r_-!\,p^{(a+b)k(k-1)/2}.
```

The two costs are explicit. Refining the original degree moduli to the
complete modulus spends `b*k*(k-1)/2` digits. The full weighted translation
then permits division by the common scale `p^a`, spending another
`a*k*(k-1)/2` digits. No lower-degree term is discarded. The quotient map
is injective within the retained residue class and reconstructs every
original integer exactly, so this is a count of the original tuples.
Division in the theorem is **natural-number division before reduction
modulo `p`**, not field division.

`coarse_preimage_le` keeps correlated complete targets before either
coordinate product bound. `colourFactorial_le_factorial` proves
`r_+!*r_-!≤k!`, and `conditioned_residue_card_le_factorial` recovers the
classical uniform factorial allowance from
[Wooley's Lemma 4.1](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf).
Our statement uses canonical representatives `0,...,p^(kb)-1`, arbitrary
translation and residue parameters, and also permits `a=b`. No historical
novelty is claimed.

The terminal theorem `conditioned_moment_card_le` applies this count to the
original complete signed moment equations when both tails lie in `eta`
modulo `p^b`. It counts the admissible original residue blocks for each
fixed opposite block; it does not count their tail completions.

The common-class configurations above can be singular modulo `p` before
division. The count still requires their normalized next digits to be
distinct. The finite-window completion bounds below now provide the
normalized mean-value budget for each fixed pair of blocks. The following
combined count also pays all finite tail completions for canonical block
representatives. The full conditioned-moment transfer is proved below;
the one-step recurrence and elementary deep-remainder saving are proved below.
The critical high-order exponent plus positive epsilon is proved below; quantitative joint arithmetic resonance remains open. No required
exponential-sum saving, new zeta-growth estimate, VK zero-free region or RH
proof follows yet.

## Actual residue-window tails and every fixed sign pattern

[VinogradovAffineMoment](../RiemannGaussian/VinogradovAffineMoment.lean)
proves that common integer dilation by a nonzero `q` and translation by
`xi` preserve the complete homogeneous moment equations, including
arbitrary integer weights and repeated entries. The exact torus moment
and full complex weighted homogeneous Gram coefficient are unchanged.
Every shifted progression count is consequently bounded by the literal
Vinogradov mean value at its normalized length.

[VinogradovResidueMoment](../RiemannGaussian/VinogradovResidueMoment.lean)
applies this to the actual finite positive window

```math
A_{q,\xi}(X)=\{n\in\mathbb Z:1\le n\le X,\ n\equiv\xi\pmod q\},
\qquad q\ge1,\quad 0\le\xi\lt q,\quad M=\lfloor X/q\rfloor+1.
```

The quotient map is injective and reconstructs each original integer
exactly. Its exact supported moment and complex Gram identity remain
available before embedding into `1,...,M`; the extra endpoint is explicit.
`residue_window_shift_le_meanValue` proves, for every full integer target
vector `h`,

```math
\#\left\{(v,w)\in A_{q,\xi}(X)^r\times A_{q,\xi}(X)^r:
\sum_l v_l^j-\sum_l w_l^j=h_j\quad(1\le j\le k)\right\}
\le J_{r,k}(M).
```

[VinogradovSignedTailMoment](../RiemannGaussian/VinogradovSignedTailMoment.lean)
retains any fixed signs `tau_l` in `{+1,-1}`. Swapping `v_l` and `w_l`
exactly at the negative positions is an involution of the complete tuple
product and preserves the entire difference vector. Thus every signed
shifted count equals the corresponding ordinary shifted count, with no
restriction on the number of signs of either colour.

The weighted statement is an exact complex identity, before norms. With
`P_tau(x)=sum_l tau_l nu(x_l)`, `P(x)=sum_l nu(x_l)` for the ordinary tuple,
and `W(x)=prod_l w(x_l)`, define

```math
\widetilde W_\tau(x)=\prod_l
\begin{cases}w(x_l),&\tau_l=+1,\\
\overline{w(x_l)},&\tau_l=-1.\end{cases}
\qquad
G_{P_\tau,W}(h)=G_{P,\widetilde W_\tau}(h).
```

Here the ordinary tuple frequency in the last formula is the sum of the
single-entry power vectors. `signed_weightedShift_eq_crossed` proves the
identity for every finite integer-vector family and every `h`. No complex
weight is replaced by its modulus in that identity. For bounded original
weights, `signed_residue_weighted_shift_le_meanValue` gives the downstream
norm budget `J_(r,k)(M)`.

Finally, `signed_tail_completions_le_meanValue` proves that for every fixed
pair of blocks `x,y`, arbitrary integer block weights `c_i`, and every
fixed tail sign pattern, the number of pairs `v,w` in the actual window
satisfying

```math
\sum_i c_i x_i^j+\sum_l\tau_l v_l^j
=\sum_i c_i y_i^j+\sum_l\tau_l w_l^j
\qquad(1\le j\le k)
```

is at most `J_(r,k)(M)`. The existing elementary all-order theorem supplies
`J_(r,k)(M)≤min(r,k)!*M^(2r-min(r,k))`; the stronger saving needed for VK
remains open. The crossing uses the complete tuple product. Additional
conditions coupling entries within one tuple, such as nonsingularity,
need their own transport proof and are not asserted to survive the swap.
These affine and counting identities are classical ingredients; no
historical novelty or new zero-free region is claimed.

## Combined completions and actual congruence-fibre energy

[VinogradovConditionedCompletion.conditioned_complete_count_le](../RiemannGaussian/VinogradovConditionedCompletion.lean)
now combines the coarse count with the finite signed tail budget. For every
fixed opposite block `y`, count pairs consisting of a canonical block
`x` in `0,...,p^(kb)-1` and a tail pair `v,w` in the actual positive window
of the residue `eta` modulo `p^b`. Require the original complete signed
moment equations, a common class `xi` modulo `p^a`, and distinct normalized
next digits for `x`, as above. For `1≤k<p` and `a≤b`, the count is at most

```math
r_+!\,r_-!\,p^{(a+b)k(k-1)/2}
 J_{r,k}(\lfloor X/p^b\rfloor+1).
```

The proof retains arbitrary integer coefficients on both blocks and tails
through the complete binomial translation. It first expresses the count
as the exact sum of its supported row counts. Each row keeps its full
block-dependent target before applying the uniform tail budget. This
statement concerns canonical block representatives; it does not on its
own count arbitrary block entries up to `X`.

[VinogradovCongruenceEnergy](../RiemannGaussian/VinogradovCongruenceEnergy.lean)
then pays the pointwise energy step. Let `B_epsilon(m;xi,eta)` be the complete
coarse fibre defined above, and `D=r_+!*r_-!*p^((a+b)*k*(k-1)/2)`. For
**every complex weight on that fibre**, Lean retains

```math
\left|\sum_{z\in B_\epsilon}w_z\right|^2
=\mathrm{Re}\sum_{z,z'\in B_\epsilon}w_z\overline{w_{z'}}
\le D\sum_{z\in B_\epsilon}|w_z|^2.
```

The first equality is the exact full Gram identity. The inequality spends
the actual proved fibre count at Cauchy; no unproved energy premise is
introduced. The literal finite residue sums are

```math
f_{q,c}(\alpha;\zeta)=
\sum_{\substack{1\le n\le X\\n\equiv\zeta\pmod q}}
 e^{2\pi i c\sum_{j=1}^k\alpha_j n^j},\qquad
f_{q,-c}(\alpha;\zeta)=\overline{f_{q,c}(\alpha;\zeta)}.
```

The equality for reversed phase is proved before taking its norm.
`coarse_product_energy_le` specializes the estimate to the actual product
of these sums, for every finite endpoint `X` and every torus point:

```math
\left|\sum_{z\in B_\epsilon}
 \prod_{i=1}^k f_{p^{kb},\epsilon_i}(\alpha;z_i)\right|^2
\le D\sum_{z\in B_\epsilon}
 \prod_{i=1}^k|f_{p^{kb},1}(\alpha;z_i)|^2.
```

This is the pointwise Cauchy ingredient in
[Wooley (2012), equation (6.5), p. 1601](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf).
The source uses the uniform `k!` allowance; the Lean statement retains the
actual sign factorial. The full target fibre, all residue coordinates and
original complex products remain available upstream. The exact target
partition, its whole-moment energy transfer, exact product factorization
and both Hölder steps are now proved below, along with the higher
homogeneous comparison, finite congruencing transfer and explicit one-step
conditioning recurrence. The uniform iteration and critical high-order exponent plus positive epsilon are proved below. No new zero-free width follows yet, and no
historical novelty is claimed for these classical ingredients.

## Exact whole-moment partition and finer-residue energy

[VinogradovMomentPartition](../RiemannGaussian/VinogradovMomentPartition.lean)
keeps any finite configuration family `z`, its original integer blocks
`x(z)`, literal positive tails `u(z)` in `eta` modulo `q^b`, and arbitrary
complex weights `w_z`. Both block coefficients `c_i` and tail coefficients
`tau_i` may be arbitrary integers. Define the full frequency and target by

```math
v_j(z)=\sum_i c_i x_i(z)^j+\sum_i\tau_i u_i(z)^j,
\qquad
M_j(z)=\sum_i c_i(x_i(z)-\eta)^j\pmod{q^{jb}}.
```

Complete frequency equality implies equality of **every** target degree.
This follows from the proved weighted binomial translation and the literal
tail divisibilities. It is valid for every nonzero base `q`; primality is
not needed for the partition. If `P` is the original weighted Fourier sum
and `P_m` restricts its original weights to `M(z)=m`, Lean proves

```math
\int_{(\mathbb R/\mathbb Z)^k}|P(\alpha)|^2\,d\alpha
=\sum_m\int_{(\mathbb R/\mathbb Z)^k}|P_m(\alpha)|^2\,d\alpha.
```

The full complex Gram identity is proved before this real energy identity.
It retains all same-target cross terms; only proved cross-target
orthogonality removes terms. Arbitrary correlations and restrictions
represented by the original finite configuration family remain intact.

[VinogradovPartitionEnergy](../RiemannGaussian/VinogradovPartitionEnergy.lean)
then retains the exact polynomial refinement `P_m=sum_{c:coarse(c)=m}P_c`.
Pointwise Cauchy with the proved number of fine labels, continuity, and the
actual Haar integral give its whole-energy inequality. No integrability or
finite sum exchange is left as an assumption.

[VinogradovResidueEnergy.window_whole_integral_le](../RiemannGaussian/VinogradovResidueEnergy.lean)
discharges the arithmetic conditions for the **full original window**, not
just canonical block representatives. For `1≤k<p`, `a<b`, include every
positive block `x_i≤X` in the specified class `xi` modulo `p^a` with distinct
normalized next digits, and every positive tail entry `u_i≤X` in `eta`
modulo `p^b`. Retain the original block signs and arbitrary integer tail
coefficients and complex configuration weights. Let `P_c` now restrict
only the full block residue tuple modulo `p^(kb)`. The result is

```math
\boxed{\displaystyle
\int|P(\alpha)|^2\,d\alpha
\le r_+!\,r_-!\,p^{(a+b)k(k-1)/2}
\sum_{c\in\mathcal C}\int|P_c(\alpha)|^2\,d\alpha.}
```

Here `C` is the complete set of canonical residue tuples retaining the
coarse class and distinct normalized next digits. Reduction of each
original entry modulo `p^(kb)` is proved to preserve both properties and
every translated degree target. Thus the earlier signed prime-power count
bounds each target fibre and pays the displayed cost. The result holds at
every finite endpoint, including empty windows. A general version also
retains arbitrary finite correlated configuration families.

This is the whole-moment transfer underlying
[Wooley (2012), equations (6.4)–(6.6), pp. 1600–1601](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf).
It forces matching finer block residues in the surviving energies. The
actual product identification and first finite Hölder bound follow next;
the higher homogeneous comparison and finite congruencing step are proved
below, together with the actual one-step conditioning recurrence. The critical high-order exponent plus positive epsilon is proved below; uniform quantitative parameter costs remain open. No zero-free width follows yet.

## Literal products and the actual mixed-moment maximum

[VinogradovProductEnergy](../RiemannGaussian/VinogradovProductEnergy.lean)
constructs an exact bijection between each original conditioned block fibre
and its coordinate product of literal positive residue windows. It then
identifies the finer-fibre polynomial with the actual signed residue
product. Let `W(alpha)` be the complete tail polynomial with **arbitrary
complex configuration weights**. Its weights may retain joint restrictions
and correlations between tail entries; no coordinate independence is
assumed inside `W`.

Write `F_epsilon` for the original conditioned block sum, `P=p^(kb)` and
`D=r_+!*r_-!*p^((a+b)*k*(k-1)/2)`. Exact complex product identities precede
the norm estimate:

```math
\int |F_\epsilon(\alpha)W(\alpha)|^2\,d\alpha
\le D\sum_{c\in\mathcal C}\int
 \left(\prod_{i=1}^k |f_{P,1}(\alpha;c_i)|^2\right)
 |W(\alpha)|^2\,d\alpha.
```

The signed block phases are retained before their exact conjugation identity
simplifies the norms. The whole tail polynomial survives on both sides.
The original class `xi` modulo `p^a` still restricts the finer tuples.
An exact quotient injection proves

```math
|\mathcal C|\le \bigl(p^{kb-a}\bigr)^k.
```

For nonnegative continuous `f_i,g` on the actual torus, Lean also proves
that if every integral `int f_i^k*g` is at most `B`, then `int prod_i f_i*g`
is at most `B`. The proof uses the pointwise finite mean inequality
`prod_i f_i <= (sum_i f_i^k)/k`, with all integral exchanges and
integrability proved. Applying this to the literal residue factors gives
[conditioned_product_max_le](../RiemannGaussian/VinogradovProductEnergy.lean):

```math
\boxed{\displaystyle
\int |F_\epsilon(\alpha)|^2|W(\alpha)|^2\,d\alpha
\le D\,\bigl(p^{kb-a}\bigr)^k\,M,}
\qquad
M=\max_{0\le\zeta\lt p^{kb}}\int
 |f_{P,1}(\alpha;\zeta)|^{2k}|W(\alpha)|^2\,d\alpha.
```

This maximum is defined from the actual finite mixed torus integrals;
there is **no unproved moment-budget premise** in the endpoint. The earlier
fibre identities remain available before taking this maximum, including
their complete residue restrictions and complex weights.

This proves the product and first finite Hölder ingredients following
[Wooley (2012), equation (6.6), pp. 1601–1602](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf).
The analytic mixed-moment interpolation is now proved in
[VinogradovInterpolation](../RiemannGaussian/VinogradovInterpolation.lean),
including zero values, the first-moment endpoint and all Lp requirements.
It applies to arbitrary continuous complex functions. The actual Riesz
carrier now receives that interpolation together with a constructive
falling-factorial and floor lower bound on its original block mass;
see the [explicit interpolated carrier bound](zeta-riesz-conditioned-energy.md).
The higher homogeneous comparison and finite congruencing step are now
proved below, together with both collision bounds and the actual one-step
conditioning recurrence. The uniform iteration and critical high-order exponent plus positive epsilon are proved below; parameter costs still need quantitative bounds.
This is a classical finite congruencing ingredient, not a new VK growth
estimate or a larger proved zero-free region.

## Finite signed congruencing step

[VinogradovConditionedHigherMoment](../RiemannGaussian/VinogradovConditionedHigherMoment.lean)
injects `u` original conditioned blocks into one tuple of `u*k` actual
residue-window entries. Flattening preserves every signed power coordinate.
The original family is bounded by the full signed family **before** crossing
negative coordinates, so the proof does not assume that crossing preserves
within-block nonsingularity. For every full shifted target, this gives the
literal homogeneous majorant at the quotient length. In particular,

```math
\int |F_b^\tau(\alpha;\eta)|^{2u}\,d\alpha
\le J_{uk,k}\!\left(\left\lfloor X/p^b\right\rfloor+1\right).
```

Joint complex tuple weights bounded in norm by one receive the same shifted
majorant. The exact frequency identity remains available upstream.

[VinogradovCongruencingStep](../RiemannGaussian/VinogradovCongruencingStep.lean)
then constructs a zero-or-one image weight on full tail tuples. Its
polynomial equals `(F_b^tau)^u` exactly, retaining every original block
restriction and sign. Define the **actual** reverse mixed maximum by

```math
I_{b,kb}^{\tau}(\eta)=
\max_{0\le\zeta\lt p^{kb}}\int
 |F_b^\tau(\alpha;\eta)|^2
 |f_{p^{kb},1}(\alpha;\zeta)|^{2ku}\,d\alpha.
```

For prime `p`, `1<=k<p`, `a<b` and `u>=1`, the terminal theorem
`conditioned_congruencing_step` proves

```math
\boxed{\begin{aligned}
K_{a,b}^{\epsilon,\tau}(\xi,\eta)
&:=\int|F_a^\epsilon(\alpha;\xi)|^2
          |F_b^\tau(\alpha;\eta)|^{2u}\,d\alpha\\
&\le\Gamma_\epsilon\,
 J_{(u+1)k,k}\!\left(\left\lfloor X/p^b\right\rfloor+1\right)^{1-1/u}
 I_{b,kb}^{\tau}(\eta)^{1/u},\\
\Gamma_\epsilon
&=r_+!\,r_-!\,p^{(a+b)k(k-1)/2}\bigl(p^{kb-a}\bigr)^k.
\end{aligned}}
```

Here `r_+` and `r_-` count the signs in the first block. The two blocks
may have different sign patterns. Every original entry lies in `1,...,X`;
`eta` is reduced to its canonical class modulo `p^b`. Empty windows, quotient
rounding and the endpoint `u=1` are included. No moment bound is supplied
as a hypothesis.

This is the finite inequality underlying
[Wooley (2012), Lemma 6.1 and equations (6.7)–(6.8), pp. 1600–1602](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf),
with explicit finite-window conventions and the retained sign factorial.
The congruencing transfer and one-step conditioning recurrence are proved.
Both collision contributions have the explicit upper bounds below. The critical high-order exponent plus positive epsilon is proved below. Quantitative parameter costs and the required zeta growth estimate remain open. The Riesz bridge preserves its original weighted
moments; these are not identified with the unweighted conditioned moments
in this theorem. No larger zero-free region is claimed from this step.

## Explicit singular conditioning bound

[VinogradovSingularConditioning](../RiemannGaussian/VinogradovSingularConditioning.lean)
defines the literal mixed moment and proves its exact collision decomposition:

```math
I_{a,b}^{\epsilon}(\xi,\eta)
=\int |F_a^{\epsilon}(\alpha;\xi)|^2|f_{p^b,1}(\alpha;\eta)|^{2s}\,d\alpha
=T_1+T_2.
```

Every original entry lies in `1,...,X`. The two tail tuples together use
fewer than `k` next-digit classes in `T_1`, and at least `k` in `T_2`.
The full signed power equation is retained in both counts.
[Block selection](../RiemannGaussian/VinogradovConditioningSupport.lean)
keeps the induced signs and the exact frequency of the remaining variables;
selection may draw from either side of the original equation.

For the singular contribution, the support is covered by actual sets `S`
of `k-1` classes in `ZMod p`. Lean proves there are exactly `choose(p,k-1)`
such sets. [Exact next-digit refinement](../RiemannGaussian/VinogradovResidueDigits.lean)
retains the complete complex polynomial:

```math
P_S(\alpha)=\sum_{d\in S}
 f_{p^{b+1},1}(\alpha;\eta+p^b d),\qquad
\mathcal P_S(\alpha)=F_a^{\epsilon}(\alpha;\xi)P_S(\alpha)^s.
```

The equality uses canonical digit representatives. Its explicit finite-window
bijection includes the original endpoint. Only after these identities does
the finite Hölder inequality give the class-count cost. The terminal theorem
`singular_count_le_next_mixed_max` proves

```math
\boxed{\displaystyle
T_1\le {p\choose k-1}(k-1)^{2s}
\max_{0\le\zeta\lt p^{b+1}} I_{a,b+1}^{\epsilon}(\xi,\zeta).}
```

The displayed formula applies for nonzero base `p`, `1<=k<=p`, `s>=1` and
`0<=eta<p^b`; the theorem does not require primality or an assumed moment
budget. Continuity, integrability and every finite integral exchange are
proved for the actual functions. The original signed block, both tail
supports and the unchanged cutoff survive the reduction.

This supplies an explicit finite version of the singular estimate in
[Wooley (2012), equation (5.2), pp. 1597–1598](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf).
The nonsingular contribution and actual one-step conditioning recurrence
are proved next. High-moment iteration and the VK zero-free proof remain
open. No quantitative saving for the original weighted Riesz moments or
larger zero-free width is claimed here.

## Explicit finite conditioning recurrence

[VinogradovNonsingularSelection](../RiemannGaussian/VinogradovNonsingularSelection.lean)
selects an ordered block from the **joint support of both tails**. For each
position embedding `e`, an injection retains both original conditioned
blocks, the selected block with its induced signs, and every complementary
entry. Its target equation and complex polynomial remain exact:

```math
\mathcal P_e(\alpha)=
|F_a^\epsilon(\alpha;\xi)|^2 F_b^{\tau_e}(\alpha;\eta)
\prod_{j\notin e} f_{p^b,\sigma_j}(\alpha;\eta).
```

The [signed complement](../RiemannGaussian/VinogradovSignedComplement.lean)
keeps the original position and sign of each remaining variable. For
`s=k*u`, `u>=1`, write the actual conditioned mixed moment and colour maximum as

```math
K_{a,b}^{\epsilon,\tau}
=\int |F_a^\epsilon(\alpha;\xi)|^2
       |F_b^\tau(\alpha;\eta)|^{2u}\,d\alpha,
\qquad K_* = \max_\tau K_{a,b}^{\epsilon,\tau}.
```

[VinogradovNonsingularConditioning](../RiemannGaussian/VinogradovNonsingularConditioning.lean)
first retains the sum over all induced sign patterns in
`nonsingular_count_le_signed_moments`. Only its downstream maximum bound
pays the full ordered-selection cost:

```math
T_2\le D\,K_*^{1/(2u)}
          \bigl(I_{a,b}^\epsilon(\xi,\eta)\bigr)^{1-1/(2u)},
\qquad D=(2s)^{\underline{k}}=\frac{(2s)!}{(2s-k)!}.
```

All integrability and Hölder hypotheses hold for the actual polynomials.
The cost counts ordered embeddings and is not optimized. With

```math
A={p\choose k-1}(k-1)^{2s},\qquad
I_+=\max_{0\le\zeta\lt p^{b+1}}
       I_{a,b+1}^\epsilon(\xi,\zeta),
```

`conditioning_step` combines the proved singular bound, the nonsingular
bound and [explicit AM-GM absorption](../RiemannGaussian/VinogradovConditioningHolder.lean):

```math
\boxed{I_{a,b}^\epsilon(\xi,\eta)
       \le 2u\,A\,I_+ + D^{2u}K_*.}
```

This holds for every nonzero base `p`, `1<=k<=p`, `u>=1`, canonical
`0<=eta<p^b`, and every original endpoint `X`. The original colour and
coarse class remain fixed. No moment estimate is assumed. It supplies the
finite conditioning step in
[Wooley (2012), Lemma 5.1](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf)
with explicit constants; no historical novelty is claimed.

The uniform iteration and critical high-order exponent plus positive epsilon are proved below; quantitative parameter and resonance estimates remain. The original Riesz
moments retain their own complex weights and sampling costs; this
unweighted conditioning theorem does not establish their quantitative
saving or enlarge the proved zero-free region.

## Deep remainder with explicit power saving

[VinogradovConditioningRemainder](../RiemannGaussian/VinogradovConditioningRemainder.lean)
iterates the actual conditioning step. Set `s=k*u`, `q=k*(u+1)`, and let
`L_b` be the actual maximum of the original mixed moment over canonical
residues at level `b`; `Q_b` also maximizes over the conditioned block colour.
The fixed original colour, coarse class and endpoint `X` are retained.
With the exact costs

```math
S=2u{p\choose k-1}(k-1)^{2ku},\qquad
E=\bigl((2ku)^{\underline{k}}\bigr)^{2u},
```

`finite_conditioning_iteration` proves at every finite depth

```math
L_b\le S^H L_{b+H}+E\sum_{h=0}^{H-1}S^hQ_{b+h}.
```

The remainder receives the actual two-scale higher moments:

```math
L_{b+H}\le
J_{q,k}\bigl(\lfloor X/p^a\rfloor+1\bigr)^{1/(u+1)}
J_{q,k}\bigl(\lfloor X/p^{b+H}\rfloor+1\bigr)^{u/(u+1)}.
```

This uses the proved higher conditioned-moment comparison before any
sign crossing; no pointwise domination of a conditioned polynomial is
assumed. Every extra quotient endpoint is present.

[VinogradovConditioningPowerSaving](../RiemannGaussian/VinogradovConditioningPowerSaving.lean)
then inserts the proved elementary exponent and pays the rounding with
explicit constants:

```math
\lambda_0=k(2u+1),\qquad
C=2^{\lambda_0}k!,\qquad D=2u(k-1)^{2ku}.
```

For `k>=2`, `u>=k`, `a<=b`, `H>=1`, the exact conditions are

```math
b-a\le2H,\qquad p^{b+H}\le X,\qquad (CD)^2\le p.
```

The last condition also proves `k<p`. The base need not be prime for this
remainder theorem; later congruencing still uses its primality hypothesis.
Only when the full window fits does Lean use
`floor(X/p^j)+1 <= 2X/p^j`. The exact unabsorbed bound is

```math
S^H L_{b+H}\le
CD^H\left(\frac{X}{p^a}\right)^k
     \left(\frac{X}{p^b}\right)^{2ku}p^{-H}.
```

[Exact scaling and constant absorption](../RiemannGaussian/VinogradovRemainderScaling.lean)
then prove the terminal remainder estimate and its insertion into the
complete finite recurrence:

```math
\boxed{\displaystyle
S^H L_{b+H}\le
\left(\frac{X}{p^a}\right)^k
\left(\frac{X}{p^b}\right)^{2ku}p^{-H/2}.}
```

There is **no supplied moment-budget premise** in
`deep_remainder_power_saving` or `finite_conditioning_power_saving`.
The saving is relative to the displayed elementary normalization, within
the stated finite cutoff range. It is not a limit at fixed `X` as `H` grows.

The general theorem `deep_remainder_of_scaled_bounds` also retains any real
exponent at or above the critical value:

```math
\lambda\ge2k(u+1)-\frac{k(k+1)}2.
```

It explicitly requires the two actual homogeneous-moment bounds with a
common scaled constant `B>=1`. Under `(BD)^2<=p`, its normalization is

```math
\left(\frac{X}{p^a}\right)^{\lambda-2ku}
\left(\frac{X}{p^b}\right)^{2ku}p^{-H/2}.
```

The final unconditional specialization discharges those two bounds at
`lambda_0`; it does not establish a sharper moment exponent. This makes the
remainder step in
[Wooley (2012), equations (5.4)–(5.5) and Lemma 5.2](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf)
quantitative at the elementary starting exponent, while preserving the
interface needed for subsequent improvements. The next section couples this remainder to signed congruencing.
The uniform iteration now proves the critical high-order exponent plus positive epsilon below. The original Riesz moments still carry their own complex weights and
sampling costs. No VK growth estimate or new zero-free width follows yet.

## Normalized signed congruencing recurrence

[VinogradovIteratedCongruencing](../RiemannGaussian/VinogradovIteratedCongruencing.lean)
identifies the reverse maximum with the actual next conditioning maximum
at scales `b,k*b`, with the canonical original residue and both block
colours retained. The full finite conditioning sum and its deep remainder
therefore feed directly into the original signed congruencing inequality.
No supplied moment estimate occurs in `conditioned_le_finite_iteration`.

For a real exponent `lambda`, put

```math
\mathcal N_{a,b}(\lambda)=
\left(\frac X{p^a}\right)^{\lambda-2ku}
\left(\frac X{p^b}\right)^{2ku},\qquad
\delta_\lambda=\lambda-2k(u+1)+\frac{k(k+1)}2.
```

[VinogradovCongruencingScaling](../RiemannGaussian/VinogradovCongruencingScaling.lean)
proves the exact scale identity underlying the iteration:

```math
\begin{aligned}
&p^{(a+b)k(k-1)/2+k(kb-a)}
\left(\frac X{p^b}\right)^{\lambda(1-1/u)}
\mathcal N_{b,kb}(\lambda)^{1/u}\\
&\qquad=\mathcal N_{a,b}(\lambda)p^{-\delta_\lambda(b-a)}.
\end{aligned}
```

The actual integer congruence cost is transported into that identity with
its triangular division and truncated-subtraction conditions proved.
Every intermediate level also has the exact factor
`N_(a,b+h)=N_(a,b)*p^(-2kuh)`.

Write `Q_(a,c)` for the actual maximum of the conditioned moments over
canonical tail residues and induced tail-block colours, retaining the fixed
original coarse class and colour. Let `Qhat=Q/N`. The exact finite allowance
in [VinogradovNormalizedIteration](../RiemannGaussian/VinogradovNormalizedIteration.lean)
is

```math
\mathcal A_{a,b,H}(\lambda)=p^{-H/2}
 +E\sum_{h=0}^{H-1}S^hp^{-2kuh}\widehat Q_{a,b+h}(\lambda).
```

`allowance_scale_identity` proves that multiplying this by `N_(a,b)`
recovers exactly the proved remainder scale and the full intermediate sum.
No largest-level selection or omitted energy is hidden in this identity.
The general theorem `normalized_iteration_of_scaled_bounds` requires
`lambda` at or above the critical exponent and **two explicitly stated
actual homogeneous estimates**, at `floor(X/p^b)+1` and
`floor(X/p^(kb+H))+1`, with common `C>=1`. It does not assert those sharper
estimates.

The terminal `normalized_finite_iteration` supplies both estimates at
`lambda_0=k(2u+1)` using the proved rounded elementary bound. Under the
explicit conditions

```math
\begin{gathered}
k\ge2,\quad u\ge k,\quad a\lt b,\quad H\ge1,\\
(k-1)b\le2H,\quad p^{kb+H}\le X,\quad (CD)^2\le p,\\
C=2^{k(2u+1)}k!,\qquad D=2u(k-1)^{2ku},
\end{gathered}
```

with prime `p`, original canonical residue and both original block colours,
it proves

```math
\boxed{\displaystyle
K_{a,b}^{\epsilon,\tau}\le
c_\epsilon C^{1-1/u}\mathcal N_{a,b}(\lambda_0)
p^{-k(k-1)(b-a)/2}\mathcal A_{b,kb,H}(\lambda_0)^{1/u}.}
```

Here `c_epsilon=r+!*r-!` is the original sign factorial. There is **no
supplied moment-budget premise** in this specialization. Every `Qhat` is
still an actual conditioned energy at the original endpoint.

The companion terminal `conditioned_le_geometric_iteration` pays each
intermediate weight explicitly, before any largest-level selection:

```math
S^hp^{-2kuh}\le D^hp^{-(2ku-k+1)h},\qquad
2ku-k+1\ge\frac74ku.
```

It uses that complete geometric allowance in the same actual recurrence.
These are finite, quantitative ingredients of
[Wooley (2012), Lemma 6.3](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf).
The uniform finite profile iteration and critical high-order exponent plus positive epsilon are proved below.
The initial global mean-value conditioning is proved below. The displayed defect factor
alone does not prove the next energies small. The original Riesz moments
retain their own weights and sampling costs; they are not identified with
these unweighted conditioned moments. No VK zeta-growth estimate, larger
zero-free width or historical novelty is claimed here.

## Initial global mean-value conditioning

[`exists_initial_conditioning`](../RiemannGaussian/VinogradovInitialConditioning.lean)
now starts from the full original mean value, without an assumed upper
moment budget. For integers `k>=2`, `s>0`, `M>0`, `R>0`, suppose

```math
X\ge 4k^4,\qquad X^{k(k-1)}<M^R.
```

There are a prime and a canonical residue satisfying

```math
\boxed{M<p\le 2^R M,\quad 0\le\eta<p,\quad
J_{k+s,k}(X)\le (2R)^2p^{2s}I_{0,1}(X;0,\eta).}
```

Every interval endpoint and complete frequency constraint is original.
The proof proceeds through the following checked interfaces:

1. [Full complex cross moments](../RiemannGaussian/VinogradovCrossMoment.lean)
   retain every matching-frequency correlation. Nonzero integer dilation
   preserves arbitrary weighted even moments exactly.
2. [Repeated-coordinate moments](../RiemannGaussian/VinogradovRepeatedMoment.lean)
   and [original repeated solutions](../RiemannGaussian/VinogradovRepeatedSolutions.lean)
   bound the exceptional count by `k² J_r^(1-1/(2r))`. The actual diagonal
   lower bound `J_r>=X^r` then [absorbs it](../RiemannGaussian/VinogradovInitialExceptional.lean),
   giving `J_r<=2D` for the distinct-block count.
3. One [uniform prime packet](../RiemannGaussian/VinogradovPrimePacket.lean)
   covers every original distinct block. The ordered product of pairwise
   distances is positive and at most `X^(k(k-1))`; the product of all packet
   primes cannot divide it. A [finite cover and pigeonhole argument](../RiemannGaussian/VinogradovInitialPrimeTransfer.lean)
   gives `J_r<=2R D_p` at one common prime.
4. The [exact restricted complex correlation](../RiemannGaussian/VinogradovInitialEnergy.lean)
   precedes Cauchy, producing `(2R)²` times the original restricted self
   energy. [Exact block/tail factorization](../RiemannGaussian/VinogradovInitialFactor.lean)
   identifies it with `I_(0,0)` before residue refinement reaches `I_(0,1)`.

For `s=ku`, [the global finite-iteration theorem](../RiemannGaussian/VinogradovInitialIteration.lean)
then proves

```math
\boxed{J_{(u+1)k,k}(X)
 \le (2R)^2X^{k(2u+1)}\mathcal A_{0,1,H}(\lambda_0),
 \qquad \lambda_0=k(2u+1).}
```

Here the allowance is the complete actual finite allowance defined above,
including its `p^(-H/2)` remainder and every weighted intermediate
conditioned energy. The additional conditions are `u>=k`, `H>=1`,
`(2^R M)^(1+H)<=X`, and `(C D)^2<=M`. The initial factor `p^(2ku)` cancels
the fine-scale denominator exactly.

The hypotheses have explicit growing solutions: the companion theorem
`initial_finite_iteration_at_power_cutoff` takes `X=(2^R M)^(1+H)`, with
`R>2(1+H)k(k-1)` and sufficiently large `M` satisfying the displayed fixed
thresholds. It discharges the packet budget and finite-cutoff condition.

This closes the initial global entry and its connection to the actual finite
recurrence. The first independent bound on its remaining levels is proved
below. The original Riesz carrier has additional complex weights and
sampling costs; this entry theorem does not supply its missing saving,
VK zeta growth, or a larger zero-free region.

## First global high-moment exponent improvement

[`exists_global_first_exponent`](../RiemannGaussian/VinogradovFirstExponent.lean)
now proves an independent improvement over the elementary moment exponent.
For **every integer `k>=2` and `u>=k`**, there are `C>0` and a finite `X0`
such that, for every integer `X>=X0`,

```math
\boxed{J_{(u+1)k,k}(X)
 \le C X^{\,k(2u+1)-1/(3k)}.}
```

The baseline exponent was `k(2u+1)`. This theorem saves `1/(3k)` at every
sufficiently large endpoint. Its prime, packet and moment conditions are
discharged. **The terminal threshold has not been numerically evaluated.**
The companion `global_meanValue_first_exponent` exposes the constant and
threshold in terms of fixed admissible packet parameters.

The [initial saving](../RiemannGaussian/VinogradovInitialSaving.lean)
comes from paying the reverse elementary moment cost exactly. At coarse
level zero, the net exponent is

```math
\frac{k(k-1)}2-\frac{k(k-1)}{u+1}
 =\frac{k(k-1)(u-1)}{2(u+1)}\ge\frac13.
```

This bounds the **entire actual residue and colour maximum**. Consequently
the complete depth-one allowance, including its deep remainder, satisfies

```math
\mathcal A_{0,1,1}(\lambda_0)
 \le (1+E\,c_+C_{\rm elem})p^{-1/3}.
```

Here `E=selectionCost(k,u)`, `c_+` is the original all-positive block
factorial, and `C_elem=elementaryConstant(k,u)`. Initial global conditioning
transfers this to the original full mean value, with the fixed packet cost
retained. On the explicit cutoffs `X=(2^R M)^k`, exact scaling converts
`M^(-1/3)` into a fixed constant times `X^(-1/(3k))`.

The extension to all large endpoints preserves original solutions:
`meanValue_mono` injects every complete equal-frequency pair into the larger
interval. `exists_nearby_power_cutoff` places each eligible `X` below a
cutoff `Y<=2^k X`, so the exponent survives with a fixed additional constant.
Finally, the theorem constructs all packet and base parameters.

This is a first global exponent improvement in this formalization. It
does not claim a literature record or the critical mean-value exponent.
The stronger VK moment estimate, exponential-sum saving, near-one zeta
growth and zero detector remain to be proved. The improved exponent is now connected to the original weighted Riesz
carrier below. Its required combined arithmetic saving and the proved
zero-free region remain unchanged.

## Direct application to the original Riesz carrier

The [compiled Riesz bridge](../RiemannGaussian/ZetaRieszConditionedEnergy.lean)
now applies the actual mixed-moment theorem directly to the original
squarefree composite Riesz carrier. An exact polynomial Fourier lift keeps
the full complex zeta kernel and Riesz coefficient as weights; its phase-zero
value and the complete residue partition recover the original band exactly.
Pointwise evaluation pays its attained joint-frequency count, and an
explicit admissible block proves the normalization is nonzero when the
next-digit window fits. The unchanged source limit and exact signed Gram
identities remain available. The newer
[finite conditioning transfer](../RiemannGaussian/ZetaRieszConditioningTransfer.lean)
now averages the original complex weights on complete configuration-frequency
fibres. Its proved energy comparison reaches the actual unweighted mixed
moment, and then the explicit deep remainder and full normalized conditioned
sum. It pays the actual fibre-correlation maximum as well as sampling and
positive block mass; it assumes no missing weighted-moment estimate.
See the [full bound and its costs](zeta-riesz-conditioned-energy.md#direct-transfer-to-the-finite-conditioning-recurrence).
Quantitative control of the resulting original weighted mixed moments,
including all those costs, remains open. This interface does not enlarge
the proved zero-free region or complete the VK iteration.

## Improved exponent in the complete signed recurrence

[`VinogradovImprovedNormalization`](../RiemannGaussian/VinogradovImprovedNormalization.lean)
transports the global bound at `lambda1=k(2u+1)-1/(3k)` through every eligible
padded quotient. `rounded_actual_meanValue` pays the rounding by `2^lambda`
for any proved eventual homogeneous bound. `exists_improved_rounded_budget`
constructs one constant and threshold for all these scales.

`exists_improved_mixed_iteration` discharges both homogeneous estimates
in the complete finite conditioning inequality. The deeper quotient
threshold also covers the coarse quotient by monotonicity.
`exists_improved_normalized_iteration` then supplies the full signed
congruencing recurrence at `lambda1`, with defect
`k(k-1)/2-1/(3k)`. Both block colours and the full intermediate sum survive.
Finite depth, prime size and actual quotient conditions remain explicit.

[`ZetaRieszImprovedMoment`](../RiemannGaussian/ZetaRieszImprovedMoment.lean)
puts this result directly into the original signed Riesz carrier. Its
terminal theorem retains the actual complex fibre correlations, sampling
cost and proved positive lower block mass. A companion theorem gives the
explicit improved two-quotient moment bound.

The exact `allowance_exponent_shift_identity` audits the improvement:
after restoring the source scale, lowering the exponent by `epsilon`
multiplies the deep remainder by `(X/p^a)^(-epsilon)` and leaves **every
intermediate energy identical**. `scaled_allowance_exponent_mono` proves
the complete scaled allowance is no larger when `X>=p^a,epsilon>=0`.
The [full original-band formulas and conditions](zeta-riesz-conditioned-energy.md#the-improved-global-exponent-in-the-original-band)
make this distinction explicit. No saving for the retained energy sum,
VK growth estimate, or wider zero-free region follows from rescaling it.

## Uniform negative profiles and global exponent bootstrap

[`VinogradovConditionedUpper`](../RiemannGaussian/VinogradovConditionedUpper.lean)
bounds both actual signed blocks through their higher moments and retains
the exact two-scale normalization. Write

```math
\lambda_c=2k(u+1)-\frac{k(k+1)}2,\quad
\delta=\lambda-\lambda_c,\quad q_{a,b}=K_{a,b}/M_{a,b}(\lambda).
```

For `k>=2,u>=k` and any proved rounded homogeneous budget at
`lambda>=lambda_c`,
[`uniform_profile_iteration`](../RiemannGaussian/VinogradovProfileIteration.lean)
proves, for every finite `n`,

```math
q_{a,b}\le B_n p^{\delta a+\beta_n b},\qquad
\beta_0=ku,\qquad
\beta_{n+1}=\frac{k}{u}\beta_n-\left(1-\frac1u\right)\delta.
```

The estimate holds for every original residue and both colours, with
`a<b`, `p^(T_n*b)<=X`, the actual deepest padded quotient at least `N0`,
and the existing prime budget `(CD)^2<=p`. The induction constructs
`T_n>=1,B_n>=1`; it assumes no later-energy bounds. At a step with
`H=d_n*b`, its depth becomes `T_(n+1)=T_n*(k+d_n)`, covering every
descendant and both actual moment premises.

Before estimating the intermediate energies, their full singular weights
factor exactly into a geometric ratio
`singularCost(p,k,u)*p^(beta_n-2ku)`. The existing prime budget bounds it
by `1/2`, so the whole finite sum costs at most two, independently of its
depth. The original colour factorial survives until the final uniform
constant. No factor counting the levels is introduced.

If `delta>0`, `exists_negative_affineProfile` proves that some finite
`beta_n<0`, including the endpoint `u=k`. The
[negative-profile terminals](../RiemannGaussian/VinogradovNegativeProfile.lean)
use the independently proved `lambda1=k(2u+1)-1/(3k)` to discharge every
homogeneous budget. The complete initial level therefore receives an
independent negative prime-power bound.

[`VinogradovProfileSaving`](../RiemannGaussian/VinogradovProfileSaving.lean)
caps that exponent at `-1/2` and bounds the entire initial depth-one
allowance, including its deep remainder. The exact identity
`p^(2ku)*M_01(lambda)=X^lambda` transfers it through the actual prime
packet to

```math
J_{(u+1)k,k}(X)\le(2R)^2 B X^\lambda M^\beta,\qquad \beta<0.
```

[`exists_smaller_admissible_exponent`](../RiemannGaussian/VinogradovExponentBootstrap.lean)
constructs power cutoffs that pay every packet, prime-size and quotient
condition. Collision-preserving monotonicity extends the saving to every
sufficiently large original endpoint. Its general conclusion is

```math
\left[J_{(u+1)k,k}(X)\ll X^\lambda,\ \lambda>\lambda_c\right]
\quad\Longrightarrow\quad
\exists\mu\in(\lambda_c,\lambda),\quad J_{(u+1)k,k}(X)\ll X^\mu.
```

Here each bound means an actual positive constant and finite threshold
valid at every larger natural endpoint. `exists_beyond_first_exponent`
specializes this to a proved exponent strictly below `lambda1`, with no
supplied analytic premise. Constants, exponents and terminal thresholds
are existential and not numerically evaluated.

Separate strict improvements would not establish convergence to
`lambda_c`. The uniform improvement and infimum argument below now close
that gap for every positive epsilon in the displayed high-order range.
The [original Riesz application](zeta-riesz-conditioned-energy.md#critical-exponent-in-the-original-initial-profile)
retains its signed correlation, sampling and normalization costs; their
required combined saving remains open. No historical novelty, VK growth
estimate or wider zero-free region is claimed.

## Critical high-moment exponent and actual product sum

[`VinogradovUniformProfile`](../RiemannGaussian/VinogradovUniformProfile.lean)
fixes a positive lower defect before choosing the actual source exponent,
homogeneous constant or quotient threshold. One finite depth works for
all of them, preserving the original residues, colours and whole finite
sum. [`VinogradovUniformSaving`](../RiemannGaussian/VinogradovUniformSaving.lean)
then supplies one negative profile and complete initial allowance before
those source parameters are chosen.

[`exists_uniform_exponent_improvement`](../RiemannGaussian/VinogradovUniformExponent.lean)
proves that for each `d>0`, one `0<epsilon<=d/2` improves **every**
proved eventual exponent with `lambda-lambda_c>=d`. All prime-packet,
actual quotient and original-interval endpoint conditions are paid.
The [infimum argument](../RiemannGaussian/VinogradovCriticalExponent.lean)
therefore proves

```math
\boxed{\forall k\ge2,\ u\ge k,\ \varepsilon>0,\quad
 \exists C>0,\ X_0,\quad
 J_{(u+1)k,k}(X)\le
 C X^{2k(u+1)-k(k+1)/2+\varepsilon}\quad(X\ge X_0).}
```

Here `k,u,X` are natural numbers. No homogeneous moment budget remains as
a premise. The nonempty set of permissible exponents is bounded below by
`lambda_c`; a positive gap above it would contradict the uniform
improvement. This is the critical exponent **with every positive epsilon**
at orders `(u+1)k>=k(k+1)`. It does not assert `epsilon=0` or the same
result at all smaller moment orders.

[`VinogradovCriticalNormalization`](../RiemannGaussian/VinogradovCriticalNormalization.lean)
pays every eligible padded quotient at that exponent, and the
[actual Riesz profile](zeta-riesz-conditioned-energy.md#critical-exponent-in-the-original-initial-profile)
uses it with its independent negative initial allowance.

[`VinogradovCriticalKorobov`](../RiemannGaussian/VinogradovCriticalKorobov.lean)
also replaces **both** homogeneous factors in the actual product-sum bound.
For orders `r=(u+1)k`, `s=(v+1)k` with `u,v>=k`, a positive interval of
length `M`, and the original finite set `B` contained in `{1,...,Y}`,
it uses `C*M^(2r-k(k+1)/2+epsilon)` and
`D*Y^(2s-k(k+1)/2+epsilon)`. A frequency-preserving injection retains
every original collision. The containing interval length `Y` is kept;
no unproved cardinality-only critical estimate for an arbitrary sparse set
is substituted. The original `B`, exact phase coefficients, attainable
support, quartered Gaussian exponent and whole joint resonance envelope
remain in the product-sum theorem.

The constants and thresholds are **not numerically evaluated**, including
their dependence on degree, order and epsilon. The [Gaussian resonance
continuation](vinogradov-gaussian-power-saving.md) now proves an explicit
all-eligible-degree allowance and a net saving for the literal imaginary-power
product sum at `t=M^(2k),z=M^4`, for every `k>=4` and all sufficiently large
`M`. Every shift subset of `[1,M]` is covered. Wider parameter ranges and
uniform quantitative degree costs are still needed for the zeta growth estimate. This formalizes the displayed high-order moment result;
it is not a claim of historical novelty, RH or a new zero-free region.

## Shifted correlations and bounded complex weights

[VinogradovShiftedMoment](../RiemannGaussian/VinogradovShiftedMoment.lean)
identifies the entire complex coefficient

```math
G_w(h)=\sum_{v_i=v_j+h}w_i\overline{w_j}
=\int_{(\mathbb R/\mathbb Z)^d}
 \left|\sum_i w_i e^{2\pi i\langle v_i,\alpha\rangle}\right|^2
 e^{-2\pi i\langle h,\alpha\rangle}\,d\alpha.
```

It proves `|G_w(h)|≤G_w(0)` for every integer vector `h`. Applied to tuple
frequencies, this gives

```math
\#\{(x,y):\sum_jv_{x_j}-\sum_jv_{y_j}=h\}\le J_s(v).
```

The weighted even moment, and the norm of each of its shifted Fourier
coefficients, are also bounded by `J_s(v)` whenever every `|w_i|≤1`.
These are integral and correlation bounds; the original complex weights
remain in the exact expansion. `monomial_shift_le_meanValue` specializes
to the literal equal-power-sum system on `1,...,N`.

## Two Hölder steps for the actual product polynomial

[VinogradovMomentReduction](../RiemannGaussian/VinogradovMomentReduction.lean)
proves the finite reduction underlying
[Ford, Lemma 5.1, equation (5.3)](https://arxiv.org/pdf/1910.08209v1).
For any finite integer-frequency family `v_a` and torus samples `theta_b`,
let

```math
U=\sum_b\sum_a e^{2\pi i\langle v_a,\theta_b\rangle},\qquad
\mathcal C_r=\left\{\sum_{j=1}^r v_{a_j}\right\}.
```

For `F_b = sum_a exp(2*pi*i*<v_a,theta_b>)`, the weights are explicitly
`epsilon_b = |F_b^r| / F_b^r`, with value zero when `F_b=0`.
`two_holder_bound` keeps this formula in its statement, so later arguments
can use the weights' dependence on the original phases. Lean proves
`|epsilon_b|≤1` and, for every `r,s≥1`,

```math
|U|^{2rs}\le
|B|^{(r-1)2s}|A|^{r(2s-2)}J_r(v)T_{r,s},\qquad
T_{r,s}=\sum_{c\in\mathcal C_r}
 \left|\sum_b\epsilon_b e^{2\pi i\langle c,\theta_b\rangle}\right|^{2s}.
```

The literal multiplicity `n(c)` satisfies `sum n(c)=|A|^r` and
`sum n(c)^2=J_r(v)`. Both identities are proved. The support is the **joint
set of attainable tuple frequencies**, so its coordinate correlations
remain available before any later rectangular enlargement.

[VinogradovKorobovMoment](../RiemannGaussian/VinogradovKorobovMoment.lean)
identifies the original product polynomial with precisely these samples:

```math
v_a=(a,a^2,\ldots,a^k),\qquad
\theta_{b,j}=\frac{(-1)^j t\,b^j}{2\pi j z^j}\pmod1
\quad(1\le j\le k).
```

`polynomial_bound` applies to arbitrary finite shift sets, and
`interval_bound` uses the existing literal `meanValue r k M` on
`1,...,M`. The coefficient vector is exact; no rational approximation or
phase-independence premise is introduced. A saving still requires
quantitative bounds for `T_(r,s)` and `J_r`.

## Gaussian smoothing with the complete signed correlations

[VinogradovGaussianKernel](../RiemannGaussian/VinogradovGaussianKernel.lean)
now proves a Gaussian bound for that actual dual moment. Choose arbitrary
positive scales `a_j`. Put

```math
g_a(n)=\exp\!\left(-\pi\sum_j a_j n_j^2\right),\qquad
K_a(x)=\prod_j\left\{a_j^{-1/2}
  \sum_{m\in\mathbb Z}e^{-\pi(m-x_j)^2/a_j}\right\}.
```

Lean proves genuine absolute convergence on the full integer lattice,
then obtains the exact multivariate Poisson identity

```math
\sum_{n\in\mathbb Z^k}g_a(n)e^{2\pi i\langle n,x\rangle}=K_a(x).
```

The scalar transformation uses Mathlib's proved Gaussian Poisson theorem.
The product construction, translated spatial series and all sum exchanges
are checked here; the spatial kernel is proved strictly positive. Every
integer translate and every coordinate of `x` is retained.
For arbitrary complex weights, the exact Gram identity is

```math
\sum_n g_a(n)\left|\sum_b w_b e^{2\pi i\langle n,x_b\rangle}\right|^2
=\sum_{b,c}w_b\overline{w_c}\,K_a(x_b-x_c).
```

The left side is nonnegative; **individual cross terms on the right can
have either sign or be complex**. Positivity of the spatial kernel does
not justify deleting them. The theorem keeps their full complex sum.

For the original support `C_r`, define its exact finite maximum cost

```math
Q_a(\mathcal C_r)=\max\!\left(\{0\}\cup
 \left\{\pi\sum_j a_j c_j^2:c\in\mathcal C_r\right\}\right).
```

For ordered tuples `b=(b_1,...,b_s)`, write
`W_b=prod_l epsilon_(b_l)` and `X_b=sum_l x_(b_l)`. The compiled theorem
`dualMoment_le_gaussian_gram` proves

```math
T_{r,s}\le e^{Q_a(\mathcal C_r)}
 \mathrm{Re}\sum_{b,c}W_b\overline{W_c}\,K_a(X_b-X_c).
```

The Gaussian factor pays for the full support majorization. There is no
unproved cost premise: `supportCost` is computed from the literal finite
support, including the empty case. The Gaussian majorant adds weighted integer frequencies outside that
support; the original restricted moment remains available upstream in
`dualMoment`. Its maximum cost does not retain the support's holes or
multiplicities. The bound holds for every positive scale vector and
every complex weight family.

`VinogradovKorobovMoment.interval_gaussian_bound` composes this with the
two Hölder steps for the **actual interval product polynomial**, retaining
the exact sample coordinates above and the explicit phase-dependent
alignment weights. Its two remaining factors are the homogeneous mean
value and this complete signed Gaussian tuple Gram form. Near-integer
differences of the actual polynomial coordinates are now visible to an
independent spacing or correlation estimate. No such saving, or historical
novelty of the Gaussian identities, is claimed by this formalization.

## Complete power-sum difference fibres

[VinogradovGaussianResonance](../RiemannGaussian/VinogradovGaussianResonance.lean)
now groups that same Gram form by the full integer vector

```math
h=\sum_{\ell=1}^s v_{b_\ell}-\sum_{\ell=1}^s v_{c_\ell},\qquad
\mathcal D_s(v)=\{\text{all such }h\}.
```

For samples `x_b=gamma*v_b`, with coordinatewise multiplication, the
exact identity is

```math
G_s=\sum_{h\in\mathcal D_s(v)}C_w(h)K_a(\gamma h),\qquad
C_w(h)=\sum_{\substack{b,c\\\sum v_b-\sum v_c=h}}
  W_b\overline{W_c}.
```

`momentGram_eq_fibres` retains each complete complex coefficient `C_w(h)`.
The original polynomial samples have exactly this form;
`coordinates_eq_linearSample` proves it using their literal coefficients.
For every bounded complex weight family, the already proved shifted-count
majorant gives `|C_w(h)|≤J_s(v)`. The downstream theorem therefore proves

```math
\mathrm{Re}G_s\le J_s(v)\,\mathcal R_s(a,\gamma,v),\qquad
\mathcal R_s=\sum_{h\in\mathcal D_s(v)}K_a(\gamma h).
```

All coordinates, attainable differences and Gaussian translates remain in
`R_s`. Taking norms of the fibre coefficients loses their relative phases;
the exact signed identity remains available for a sharper estimate.
`interval_resonance_bound` now places the **actual interval product sum**
below its explicit cardinality factors, Gaussian support cost, both
homogeneous moments and this one joint resonance sum. No spacing premise
or unproved mean-value estimate is assumed in that reduction.

## Explicit translated tails and a centered support

[VinogradovGaussianBounds](../RiemannGaussian/VinogradovGaussianBounds.lean)
pays the complete one-coordinate translated series. With `r=fract(-x)`,
the uniform bound is

```math
K_a(x)\le E_a(x):=
\frac{e^{-\pi r^2/a}+e^{-\pi(1-r)^2/a}}
 {\sqrt a\,(1-e^{-\pi/a})},\qquad a>0.
```

The proof uses Mathlib's geometric bounds for the periodic Hurwitz
Gaussian kernel. Every translate is covered by the denominator, which is
proved strictly positive. The result holds for all real `x` and all
positive `a`, so it applies to phases changing with the height and the
original polynomial coefficients. For `d(x)=min(r,1-r)`, Lean also proves

```math
K_a(x)\le
\frac{2e^{-\pi d(x)^2/a}}{\sqrt a\,(1-e^{-\pi/a})}.
```

The full resonance sum is therefore bounded by the finite expression
`sum_(h in D_s) prod_j E_(a_j)(gamma_j h_j)`. Its entire joint attainable
support remains intact; it still needs an arithmetic spacing estimate.

[VinogradovGaussianCentering](../RiemannGaussian/VinogradovGaussianCentering.lean)
also permits centering the Gaussian on the actual support. For any integer
vector `m`, the exact complex identity is

```math
\sum_b w_b e^{2\pi i\langle c,x_b\rangle}
=\sum_b \bigl(w_b e^{2\pi i\langle m,x_b\rangle}\bigr)
 e^{2\pi i\langle c-m,x_b\rangle}.
```

Every weight keeps its norm, and its forced phase twist stays in the
signed Gram theorem. The downstream bounded-weight resonance majorant
can thus pay `Q_a(C_r-m)` while retaining the same resonance envelope.

For the actual interval `1,...,M`, the coordinate endpoints are
`r` and `r M^j`. The canonical integer midpoint is
`m_j=floor((r+r M^j)/2)`. Lean proves all rounding allowances and

```math
Q_a(\mathcal C_r-m)
\le\pi\sum_{j=1}^k a_j
 \left(\frac{rM^j-r+1}{2}\right)^2
\le\frac14 Q_a(\mathcal C_r),\qquad r,M\ge1.
```

Here the original maximum is exactly
`Q_a(C_r)=pi sum_j a_j (r M^j)^2`, attained by the all-upper-endpoint
tuple. `interval_quarter_envelope_bound` applies this improvement to the
literal product sum. This quarters the **Gaussian exponent cost**; it
does not quarter the whole estimate, establish the needed arithmetic
power saving, or enlarge the current zero-free region.

`interval_explicit_moment_bound` now inserts these elementary estimates
for **both** homogeneous moments in the actual product sum. For any
nonempty first interval of length `M` and any finite second shift set `B`,
it retains the exact phase coefficients, quartered Gaussian exponent and
whole joint resonance envelope. The signed Gram identities and original
moment expressions remain available upstream. No phase-spacing condition
is assumed or silently discharged by this substitution.

## Remaining analytic proof obligations

The averaging, boundary, Taylor and damping steps, shifted-moment majorants
and two-Hölder reduction are now proved for the actual terms, followed by
the complete Gaussian smoothing, centered exponent improvement and explicit
weighted-fibre and tail bounds. Elementary homogeneous moment costs are
now proved and inserted into the actual product-sum theorem. The next
step bounds the joint resonance sum through coefficient spacing and
makes the proved critical high-order mean-value bounds quantitative in the parameters required by the VK argument. The
stronger signed fibre identity also remains available. Preserve
the exact alignment weights and coordinate correlations while developing
that estimate. The identities and smoothing bound alone give no
power saving. Quantitative
mean-value estimates must imply the required logarithmic exponential-sum
saving, then a proved near-one zeta growth estimate, then the zero detector
with all constants and height ranges paid. These are substantial analytic
obligations, not just numerical constant checks.

Only after that chain is discharged can a VK width join the
[complete proved region](zeta-unified-zero-free.md). Comparisons between
benchmark width functions do not supply their analytic proofs. Consult the
[literature-frontier audit](zero-free-literature-frontier.md) for source
versions and reported constants; no world-best claim follows from the
present approximation and exact-moment theorems.
