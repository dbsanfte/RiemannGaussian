# Exact hyperbola split and the remaining quotient estimate

The completed current reconstruction and the original uniform weighted
arithmetic bound remain the active objective. The bound, full logarithmic
arithmetic decay, and RH are still open. The new research direction tests
the zero-dependent source reductio suggested in
`/home/dbsanfte/riemann/RiemannGaussian_hyperbola_reductio_steer-1.md`.
The memo is a research proposal, not an input to Lean's proof kernel.

The newest estimate controls the **norm of the full complex first mean**
through divisor cutoff `D=u³` on physical windows `A=L=u⁴`. Its allowance
is `C_rho*u^(2-4*sigma)` and tends to zero for `sigma>1/2`. A direct
parity shift and complex-power derivative supply this estimate, separately
from the existing quadratic sampler. The same windows now support a
simultaneous growing prime sieve with allowance
`C_rho*P²*u^(2-4*sigma)`. Its explicit cofinal schedule makes the whole
allowance vanish, and the surviving first mean still tends to the nonzero
source. **An independent upper bound for that mean with a fixed positive
gap below the source norm remains open.** These are complex first-mean
results; the whole-carrier mean-square range is still the earlier cubic schedule.
The single clipped fibre now has its own quartic bound: completing it
adds at most `u²` divisors, with norm at most
`C_term*u^(2-4*sigma)` and a vanishing boundary mean square. The complete
quotient first mean has source error at most
`(C_term+C_mean)*u^(2-4*sigma)`.
This completion now also works after simultaneous prime exclusion: its
boundary costs at most `C_term*P*u^(2-4*sigma)`. The complete sieved mean
has source error at most `(C_term+C_mean)*P²*u^(2-4*sigma)`, and the same
explicit growing schedule makes it vanish. The exact quotient sum
retains coprimality on both factors.
The final section records the exact new theorems and remaining target.

## Earlier cubic mean-square route

The checked result now controls the original divisor aggregate through
`A^(2/3)` on a physical window of starting cutoff and length `A`, under a
hypothetical right-half-zero assumption. Keeping the complete sampling
cost extends the earlier square-root range. The remaining source has at
most `2*A^(1/3)` quotient indices. The single clipped boundary now has
vanishing mean square, and completing it leaves the same source limit.
The complete blocks are grouped into exact dyadic shells with all cross
terms retained. The original parity recurrence now factors their full
energy through two odd-divisor channels at the original and halved physical
cutoffs, retaining the same quotient cap and the complex mixed correlation.
Abel summation now also identifies every capped shell with an alternating
Möbius bilinear sum and both boundary terms. The high aggregate uses one
fixed product coefficient sequence across its physical window, and its
entire energy has an explicit overlap matrix. The original hyperbolic
collision bound applies to the alternating coefficients, but does not
bound their full signed quadratic form.
The subsequent finite coprime sieve now removes every odd prime through
a growing threshold together, including all intersections and mixed
terms. A uniform polynomial modulus cost is paid by an explicit cofinal
sequence of original cubic scales. The surviving energy still has the
source-square limit; its products can carry growing odd prime factors.
**An independent bound with a fixed positive gap below
the source square is not proved.** A full decay or power rate is a stronger
sufficient target, not a requirement. No theorem excluding right-half
zeros or proving RH has been added. The earlier splits are recorded first,
followed by the boundary removal and shell target.

## Actual carrier and a necessary correction to the memo

For an actual nontrivial zero `rho`, write

\[
 T_\rho(M,d)=\mu(d)d^{-\rho}X_\rho(\lfloor M/d\rfloor),\qquad
 X_\rho(q)=\operatorname{completion}(\rho)
             \sum_{n\le q}(-1)^{n+1}n^{-\rho}.
\]

These are the existing `pairedEtaCompletedMoebiusTerm` and completed
unpaired eta prefix, including its original odd endpoint. The existing
finite identity gives

\[
 \sum_{d\le M}T_\rho(M,d)=S_\rho\ne0\quad(M\ge2),\qquad
 S_\rho=\operatorname{completion}(\rho)(1-2\,2^{-\rho}).
\]

Define `low(M,D)=sum_(d≤D) T(M,d)` and
`high(M,D)=sum_(D<d≤M) T(M,d)`. The new
`pairedEtaCompletedMoebiusPartial_add_large` and
`pairedEtaCompletedMoebiusLargeAggregate_eq_source_sub` in
[EtaMoebiusHyperbolaSplit](../RiemannGaussian/EtaMoebiusHyperbolaSplit.lean)
prove their exact split and `high=S-low`.

The memo's proposed full-block reindexing is not valid under just `D<M`.
A quotient fibre can straddle that cut. For example, at `M=4,D=3`,
`floor(M/(D+1))=1`, whose complete fibre is `{3,4}`; the actual large
range is only `{4}`. Changing the upper quotient endpoint alone does not
generally supply the missing clipped block.

On the intended square-root range, however, a stronger fact resolves
this completely. `moebiusHyperbola_boundary_quotient_lt` proves

\[
 \left\lfloor\frac M{D+1}\right\rfloor
 <\left\lfloor\frac MD\right\rfloor
 \quad(D\ge1,\ D^2\le M).
\]

Hence each retained quotient fibre is wholly in the large range. With
the existing exact arithmetic block

\[
 B_{\rho,M}(q)=
 \left(\sum_{M/(q+1)<d\le M/q}\mu(d)d^{-\rho}\right)X_\rho(q),
\]

`pairedEtaCompletedMoebiusLargeAggregate_eq_quotientBlocks` proves

\[
 \operatorname{high}(M,D)
 =\sum_{1\le q\le\lfloor M/(D+1)\rfloor}B_{\rho,M}(q).
\]

This is equality of the original complex sums, with no omitted endpoint
or absolute-value estimate. On `D²≤M<2D²`, the upper quotient is below
`2D`. The fixed family sets a block to zero when its quotient exceeds the
actual upper quotient. Its reconstruction is checked at every point of
the window. [EtaMoebiusHyperbolaSchedule](../RiemannGaussian/EtaMoebiusHyperbolaSchedule.lean)
specializes this to `D_k=2^k`, `A_k=D_k²`, `M=A_k+n`, `0≤n<A_k`.

## The small half is controlled on the full square window

Let `sigma=Re(rho)` and let `C_rho` be the existing nonnegative
`pairedEtaCompletedMoebiusOriginalQuadraticConstant`. The new
`pairedEtaCompletedMoebiusOriginalMeanSquare_square_le` in
[EtaMoebiusHyperbolaLowMeanSquare](../RiemannGaussian/EtaMoebiusHyperbolaLowMeanSquare.lean)
specializes the existing quadratic sampler exactly at `A=L=D²`:

\[
 L_D:=\frac1{D^2}\sum_{n<D^2}
       |\operatorname{low}(D^2+n,D)|^2
 \le U_D:=C_\rho(1+\log D)D^{1-4\sigma}.
\]

The complete growing small-half mean square tends to zero whenever
`sigma>1/4`. This is proved both as `D→∞` and on the specified dyadic
schedule by `pairedEtaCompletedMoebiusOriginalMeanSquare_square_tendsto_zero`
and `pairedEtaCompletedMoebiusOriginalMeanSquare_hyperbola_tendsto_zero`.
In particular it applies under the hypothetical right-half-zero
assumption, without a simplicity premise. The `1/4` here is a threshold
for this auxiliary convergence theorem, not a newly proved zero-free
boundary.

## The full quotient quadratic form is retained

Let `F_D(M,q)` denote the zero-extended block family. Define the actual
complex window correlation

\[
 \operatorname{Corr}_D(q,r)
 =\frac1{D^2}\sum_{n<D^2}
     F_D(D^2+n,q)\overline{F_D(D^2+n,r)}.
\]

`pairedEtaCompletedMoebiusLargeMeanSquare_eq_quotientCorrelations` in
[EtaMoebiusHyperbolaLargeMeanSquare](../RiemannGaussian/EtaMoebiusHyperbolaLargeMeanSquare.lean)
proves the exact identity, including the complex embedding of the real
energy,

\[
 H_D:=\frac1{D^2}\sum_{n<D^2}
       |\operatorname{high}(D^2+n,D)|^2
 =\sum_{q,r\le2D}\operatorname{Corr}_D(q,r).
\]

Every cross term, the moving boundary, the completion factors, and the
normalization by the physical window length remain present. Neither
independence nor replacement by a complete period is used.

## What the large half must retain

The complex small-half average `a_D` satisfies `|a_D|²≤L_D`. The exact
source expansion in
[EtaMoebiusHyperbolaSourceLimit](../RiemannGaussian/EtaMoebiusHyperbolaSourceLimit.lean)
retains its signed mixed term:

\[
 H_D=|S_\rho|^2+L_D-2\Re(S_\rho\overline{a_D}).
\]

`pairedEtaCompletedMoebiusLargeMeanSquare_square_source_error_le` gives
the explicit downstream estimate, for `D≥2`,

\[
 |H_D-|S_\rho|^2|\le U_D+2|S_\rho|\sqrt{U_D}.
\]

Thus `pairedEtaCompletedMoebiusLargeMeanSquare_hyperbola_tendsto_source`
proves `H_(D_k)→|S_rho|²` for `sigma>1/4`. Under `sigma>1/2`, the theorem
`pairedEtaCompletedMoebiusLargeMeanSquare_hyperbola_pos_eventually`
in particular gives `H_(D_k)>|S_rho|²/2` eventually.

This is consistent with the existing full off-diagonal source diagnostic.
It does not defeat the proposed reductio: a separately proved decay
estimate under a right-half-zero assumption would contradict it and
exclude that zero. It does show that quotient reindexing and small-half
decay have not themselves removed the coherent nonzero contribution.
The contradiction has not been obtained.

## The open arithmetic target and an exponent audit

The full sampling cost can be useful even when it is larger than the
window length. The new
`pairedEtaCompletedMoebiusOriginalMeanSquare_le_window` in
[EtaMoebiusWindowMeanSquare](../RiemannGaussian/EtaMoebiusWindowMeanSquare.lean)
proves, for `A≥1`, `L>0`, and `1≤T≤A`,

\[
 \frac1L\sum_{n<L}|\operatorname{low}(A+n,T)|^2
 \le C_\rho\left[
       \left(1+\frac{4T^2}{L}\right)T(1+\log T)
       +\frac{T^4}{A^2}\right] A^{-2\sigma}.
\]

Both endpoint errors and the entire window loss remain explicit. No
condition `T²≤L` is imposed on this theorem. Setting `A=L=u³` and `T=u²`
gives the genuinely larger controlled range in
[EtaMoebiusTwoThirdsMeanSquare](../RiemannGaussian/EtaMoebiusTwoThirdsMeanSquare.lean):

\[
 L^{(2/3)}_u:=\frac1{u^3}\sum_{n<u^3}|\operatorname{low}(u^3+n,u^2)|^2
 \le V_u:=11C_\rho(1+\log u)u^{3-6\sigma}.
\]

The theorem `pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_le`
includes every original divisor through `u²`. The allowance and the
entire mean square tend to zero when `sigma>1/2`; this is also checked
for `u=2^k`, so `A=8^k` and the divisor cutoff is `4^k`. The new bound
controls the sum over the full enlarged range, not individual terms
estimated independently. It remains a theorem under a zero-location
hypothesis, and does not establish a new zero-free strip.

The larger divisor cut can bisect a quotient fibre. The new
[clipped block module](../RiemannGaussian/EtaMoebiusClippedQuotientBlocks.lean)
proves the exact general arithmetic formula

\[
 D_{\rho,M,T}^{\rm clip}(q)
 =P_\rho(\lfloor M/q\rfloor)
  -P_\rho\!\left(\max\{T,\lfloor M/(q+1)\rfloor\}\right),
 \quad P_\rho(x)=\sum_{d\le x}\mu(d)d^{-\rho},
\]

for `1≤q≤floor(M/(T+1))`. The completed block is this arithmetic
difference times the unchanged `X_rho(q)`. At `T=u²` and `M<2u³`, the
upper quotient is strictly below `2u`; the clipped blocks are already
zero beyond the actual quotient boundary. Thus no endpoint cell is
dropped when using a fixed family of size `2u`.

Let `H^(2/3)_u` be the full large-half mean square beyond `u²` on
`[u³,2u³)`. In
[EtaMoebiusTwoThirdsQuotientEnergy](../RiemannGaussian/EtaMoebiusTwoThirdsQuotientEnergy.lean),
`pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_eq_quotientCorrelations`
identifies it with the complete complex double correlation sum on
`q,r≤2u`, retaining all signed cross terms and the clipped boundary.
The source comparison is quantitatively preserved:

\[
 |H^{(2/3)}_u-|S_\rho|^2|
 \le V_u+2|S_\rho|\sqrt{V_u}.
\]

`pairedEtaCompletedMoebiusLargeMeanSquare_twoThirds_tendsto_source`
and its dyadic specialization prove the nonzero source limit for this
smaller remaining quotient form under `sigma>1/2`.

A stronger sufficient estimate considered in the original steer is

\[
 H^{(2/3)}_{u_k}\le C_{\rho,\varepsilon}
          A_k^{1-2\sigma+\varepsilon}
 \quad\text{eventually, for every }\varepsilon>0,
 \qquad u_k=2^k,\quad A_k=u_k^3.
\]

For `sigma>1/2`, choose `epsilon=(2*sigma-1)/2`. The exponent is negative,
so such a bound would contradict the positive source limit. Reflection
would then address the opposite half of the critical strip. This is a
mathematical account of the proposed completion, not a compiled theorem
asserting that the missing estimate holds. No placeholder module or
axiom for the estimate is present.

The following checks determine what further work is necessary:

| Candidate input | What it currently supplies | Why the proposed decay does not yet follow |
| --- | --- | --- |
| Exact quotient factorization | Original arithmetic prefix differences times the completed eta prefix. | Equality preserves the source contribution as well as the oscillation. |
| Individual term bound | Each original term has norm at most `K_rho M^(-sigma)`. | A triangle sum over order `M` terms permits an energy of order `M^(2-2*sigma)`, one full power above the requested scale. This exponent comparison is an audit calculation, not a new Lean estimate. |
| Existing power-remainder block cancellation | For every fixed positive tolerance, a uniform block bound at its natural `M^(1-sigma)` scale with a remainder. | An arbitrarily small coefficient on a positive power is not an arbitrary saving in that power. Its sum over a growing quotient family remains uncontrolled. |
| Existing divisor Fourier sampler | The full `4*T²+L` cost is now retained and absorbed through `T=A^(2/3)` when `sigma>1/2`. | At `T` of order `A`, the remaining order-`A` window loss still prevents the needed decay. |
| Quotient transposition | The newly checked complement has only order `A^(1/3)` quotient indices, with exact clipping. | Its arithmetic block coefficients themselves vary with the physical cutoff. The fixed-coefficient divisor sampler does not become a uniform estimate for this moving family merely by renaming its indices. |
| Product-fibre collision energy | A proved coefficient-energy bound with logarithmic factors. | This alone does not bound the moving physical correlation operator or remove its window-dependent cost. |

The current target is weaker than that power estimate. The user's revised
priority is to remove the single clipped boundary, use complete quotient
blocks, group them into dyadic shells, and attack the entire shell form.
Any fixed gap below the source square suffices. The present sampler is
already at its critical low-divisor exponent; extending that range is
not the current research task.

## The single clipped boundary is now negligible

For a general divisor cut `T≤M`, put

\[
 Q=\left\lfloor\frac{M}{T+1}\right\rfloor,\qquad
 R=\left\lfloor\frac{M}{Q+1}\right\rfloor,\qquad
 E_\rho(M,T)=\sum_{R<d\le T}T_\rho(M,d),\qquad
 C_\rho(M,T)=\sum_{1\le q\le Q}B_{\rho,M}(q).
\]

The module [EtaMoebiusBoundaryFibre](../RiemannGaussian/EtaMoebiusBoundaryFibre.lean)
proves `R≤T` and the exact complex identity

\[
 C_\rho(M,T)=E_\rho(M,T)+\operatorname{high}_\rho(M,T).
\]

The theorem
`pairedEtaCompletedMoebiusBoundaryFibre_eq_block_sub_clipped` identifies
`E` with the complete last block `q=Q` minus its clipped version, for
`T<M`. Thus only one fibre has changed. No boundary is discarded by an
algebraic approximation.

At `T=u²`, `u≥1`, `M≥u³`, the theorem
`moebiusTwoThirds_boundary_card_le` proves `T-R≤u`. Applying the existing
uniform estimate for each original completed term gives

\[
 |E_\rho(M,u^2)|\le e_u:=K_\rho u^{1-3\sigma}.
\]

This is `norm_pairedEtaCompletedMoebiusBoundaryFibre_twoThirds_le`.
It holds uniformly over the entire physical window, indeed for every
`M≥u³`. The module
[EtaMoebiusBoundaryFibreDecay](../RiemannGaussian/EtaMoebiusBoundaryFibreDecay.lean)
proves `e_u→0` when `sigma>1/3`, and

\[
 \frac1{u^3}\sum_{n<u^3}|E_\rho(u^3+n,u^2)|^2\le e_u^2\longrightarrow0.
\]

The terminal boundary theorem is
`pairedEtaCompletedMoebiusBoundaryMeanSquare_twoThirds_tendsto_zero`.
The threshold `1/3` concerns this auxiliary boundary, not a zero-free strip.

The full signed identity remains available as
`pairedEtaCompletedMoebiusCompleteQuotientAggregate_sub_source`:

\[
 C_\rho(M,T)-S_\rho=E_\rho(M,T)-\operatorname{low}_\rho(M,T).
\]

With `U_u=2V_u+2e_u²`, its mean-square error is at most `U_u`. The complete
block energy `H^C_u=mean_(u³≤M<2u³)|C_rho(M,u²)|²` therefore satisfies

\[
 |H^C_u-|S_\rho|^2|\le U_u+2|S_\rho|\sqrt{U_u}\longrightarrow0
 \qquad(\sigma>1/2).
\]

Both the explicit bound and the limit are checked in
`pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_source_error_le`
and `pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_tendsto_source`.
The boundary is removed as an obstruction; the complete-block source
itself has not been bounded below its required limiting value.

## Exact dyadic shells and the weaker sufficient target

Let `u=2^k`, and retain the actual moving cutoff in each complete block:

\[
 F_k(M,q)=\mathbf1_{q\le Q(M,u^2)}B_{\rho,M}(q),\qquad
 Z_{k,j}(M)=\sum_{2^j\le q<2^{j+1}}F_k(M,q),\quad 0\le j\le k.
\]

The module [EtaMoebiusQuotientShells](../RiemannGaussian/EtaMoebiusQuotientShells.lean)
proves `C=sum_j Z_(k,j)` exactly. Define

\[
 \Gamma_k(j,l)=\frac1{u^3}\sum_{n<u^3}
 Z_{k,j}(u^3+n)\overline{Z_{k,l}(u^3+n)}.
\]

The theorem
`pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_shellCorrelations`
proves the full complex equality

\[
 H^C_{2^k}=\sum_{j,l\le k}\Gamma_k(j,l).
\]

Each `Gamma` is also exactly the sum of the original block correlations
inside that shell pair, as proved by
`pairedEtaCompletedMoebiusQuotientShellCorrelation_eq_blockCorrelations`.
All cross terms, phases, completion factors, arithmetic endpoints, and the
original averaging length remain present.

The immediate open estimate is any `delta_rho>0`, independent of `k`, with

\[
 \Re\sum_{j,l\le k}\Gamma_k(j,l)
 \le |S_\rho|^2-\delta_\rho
 \quad\text{for arbitrarily large }k,
 \qquad\sigma>1/2.
\]

A uniform eventual bound would suffice in particular. The checked theorem
`pairedEtaCompletedMoebiusQuotientShellForm_eventually_above_sub_source`
states that every such fixed threshold is eventually exceeded under the
right-half-zero hypothesis. The proposed independent upper bound would
contradict that theorem. No upper bound of this kind is assumed or proved
in the new modules. An inequality strictly below the source at each finite
cutoff with a gap tending to zero is not sufficient.

The next estimate must address the **whole** shell form. Separate diagonal
bounds do not control it, and decay only of `C-S` has already been proved.
Dependence on the zero, shell sizes, moving arithmetic coefficients, and
physical window must remain explicit. A route should not be rejected for
failing to deliver the earlier full power rate if it can yield the fixed
gap instead.

## The parity recurrence inside the full shell form

The user pointed to the exact recurrence in
[EtaMoebiusParityRecurrence](../RiemannGaussian/EtaMoebiusParityRecurrence.lean).
Its term-level identity is

\[
 T_\rho(M,2d)=-a_\rho\mathbf1_{d\ \mathrm{odd}}
                 T_\rho(\lfloor M/2\rfloor,d),\qquad a_\rho=2^{-\rho}.
\]

The new module
[EtaMoebiusQuotientParityRecurrence](../RiemannGaussian/EtaMoebiusQuotientParityRecurrence.lean)
uses the finite even-divisor bijection and the exact identity
`floor(M/(2d))=floor(floor(M/2)/d)`. Thus the quotient index is unchanged.
If `B^odd_rho(M,q)` is the odd-divisor part of a complete quotient block,
the theorem `pairedEtaCompletedMoebiusQuotientBlock_eq_odd_sub_half` gives

\[
 B_{\rho,M}(q)=B^{\rm odd}_{\rho,M}(q)
                 -a_\rho B^{\rm odd}_{\rho,\lfloor M/2\rfloor}(q).
\]

For the actual cap `Q(M,T)=floor(M/(T+1))`, define

\[
 O_{Q,j}(N)=\sum_{2^j\le q<2^{j+1}}\mathbf1_{q\le Q}
                                      B^{\rm odd}_{\rho,N}(q).
\]

The actual shell recurrence is exactly

\[
 Z_j(M)=O_{Q(M,T),j}(M)
          -a_\rho O_{Q(M,T),j}(\lfloor M/2\rfloor).
\]

This is `pairedEtaCompletedMoebiusQuotientShell_eq_odd_sub_half`.
**Both terms use the cap selected by the original `M`.** Replacing the
second cap by `Q(floor(M/2),T)`, or silently changing the divisor cut,
would change the carrier. The whole complete quotient aggregate has the
same recurrence before any energy estimate.

The new module
[EtaMoebiusQuotientParityMatrix](../RiemannGaussian/EtaMoebiusQuotientParityMatrix.lean)
defines the two odd scale channels `O_(j,0)(M)` and `O_(j,1)(M)` above.
For the original cubic window and `j,l≤k`, retain

\[
 G^{bc}_{jl}=\frac1{u^3}\sum_{n<u^3}
       O_{j,b}(u^3+n)\overline{O_{l,c}(u^3+n)},\qquad
 G^{bc}=\sum_{j,l\le k}G^{bc}_{jl}.
\]

The theorem `pairedEtaCompletedMoebiusQuotientShellCorrelation_eq_parityMatrix`
proves, for every shell pair and every physical window,

\[
 \Gamma(j,l)=G^{00}_{jl}-\overline{a_\rho}G^{01}_{jl}
                         -a_\rho G^{10}_{jl}+|a_\rho|^2G^{11}_{jl}.
\]

The full two-scale entries are proved to equal the physical averages of
the **whole** odd shell sums. Their diagonal entries therefore retain all
within-channel shell cross terms, rather than only individual shell squares.
The exact Hermitian relation is
`conj(G^bc)=G^cb`, and both diagonal entries are nonnegative.

The terminal theorem
`pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_parityEnergy`
gives

\[
 H^C_{2^k}=E_{0,k}+2^{-2\sigma}E_{1,k}
               -2\Re(\overline{2^{-\rho}}B_k),\qquad
 E_{b,k}=\Re G^{bb},\quad B_k=G^{01}.
\]

This transports the original recurrence to the current remaining
quadratic form with no unproved arithmetic hypothesis. It supplies a
specific mixed correlation to study jointly with the two odd-channel
energies. The small multiplier alone does not close the bound: the
existing global odd recurrence is forced by the nonzero source,
`Odd(M)=S_rho+a_rho*Odd(floor(M/2))`. The new shell identities do not
turn that forced recurrence into homogeneous decay.

The immediate arithmetic target remains a fixed gap below `|S_rho|²`
for the **entire displayed combination**, on arbitrarily large scales.
No sign, independence, or vanishing limit for `B_k` is assumed. A bound
only on `2^(-2*sigma)`, either diagonal alone, or a fixed shell pair
would not establish this target. The divisor exponent remains unchanged.

## Abel transport to fixed alternating product coefficients

The user's subsequent steer proposed an Abel transform to an alternating
bilinear Möbius sum. This is now checked for the actual complete shells;
the parity matrix remains available, without assuming that its mixed
correlation has a helpful sign or a vanishing limit.

Write `X_rho` for the completion factor, `F(q)=sum_(r<=q) eta(r)r^(-rho)`,
and `P(x)=sum_(d<=x) mu(d)d^(-rho)`, where `eta(r)=(-1)^(r+1)`.
[EtaMoebiusQuotientAbel](../RiemannGaussian/EtaMoebiusQuotientAbel.lean)
proves the complex identity

\[
 \sum_{L<q\le U}B_{\rho,M}(q)
 =X_\rho\left[
   \sum_{L<q\le U}\eta(q)q^{-\rho}P(\lfloor M/q\rfloor)
   +F(L)P(\lfloor M/(L+1)\rfloor)
   -F(U)P(\lfloor M/(U+1)\rfloor)\right]
 \qquad(L\le U).
\]

For the actual shell, the theorem
`pairedEtaCompletedMoebiusQuotientShell_eq_abel` uses
`L=min(Q,2^j-1)` and `U=min(Q,2^(j+1)-1)`, with the original
`Q=floor(M/(D+1))`. Empty shells and both clipped endpoints are included.
The complete prefix has only its upper boundary left; that boundary must
not be discarded when estimating the alternating bulk.

[EtaMoebiusQuotientBilinear](../RiemannGaussian/EtaMoebiusQuotientBilinear.lean)
absorbs this boundary exactly. For any quotient cap `Q`, put
`R=floor(M/(Q+1))`. The remaining uncompleted sum is

\[
 \sum_{\substack{q,d\ge1\\qd\le M\\q\le Q,\ d>R}}
                  \eta(q)\mu(d)(qd)^{-\rho}.
\]

The theorem `pairedEtaMoebiusQuotientBilinearRegion_eq_divisor_cut`
proves that `q<=Q` already follows from `qd<=M` and `d>R`. Thus this is a
literal divisor-cut subregion of the existing
`pairedEtaInverseHyperbolicRegion M`, not an approximate rectangular
replacement. `pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_bilinear`
identifies it with the actual complete carrier after multiplication by
`X_rho`.

[EtaAlternatingHyperbolicCoefficients](../RiemannGaussian/EtaAlternatingHyperbolicCoefficients.lean)
groups by the product while keeping both signs. The generic alternating
region coefficient is exactly the existing odd-quotient inverse-region
coefficient minus its even-quotient counterpart. The proved divisor
second moment gives

\[
 b_D(n)=\sum_{\substack{qd=n\\d>D}}\eta(q)\mu(d),\qquad
 \sum_{n\le M}b_D(n)^2\le M(1+\log M)^3.
\]

The terminal coefficient bound is
`sum_sq_pairedEtaMoebiusHighProductCoefficient_le_log_cube`.
Also `b_D(n)=0` for `n<=D`, and
`pairedEtaMoebiusHighProductCoefficient_eq_moebius` proves
`b_D(n)=mu(n)` on `D<n<=2D`. The first product band therefore contains a
literal Möbius sum; the rest of the form and its cross terms remain present.

[EtaMoebiusBilinearEnergy](../RiemannGaussian/EtaMoebiusBilinearEnergy.lean)
then proves, for every physical endpoint and fixed divisor cutoff,

\[
 \mathrm{High}_\rho(M,D)=X_\rho V_{\rho,D}(M),\qquad
 V_{\rho,D}(M)=\sum_{n\le M}b_D(n)n^{-\rho}.
\]

This is `pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix`.
The coefficient sequence `b_D` is fixed while `M` ranges over the window.
The complete quotient sum is exactly `X_rho*V+Boundary`, not an
independently modified candidate. On `D=u²`, `M>=u³`, the difference has
norm at most the existing `K_rho*u^(1-3*Re(rho))`. The exact energy identity
also keeps `2 Re(X_rho V conj(Boundary))` before that error is bounded.

[EtaMoebiusBilinearWindow](../RiemannGaussian/EtaMoebiusBilinearWindow.lean)
counts which physical cutoffs contain both product indices. With both
subtractions truncated at zero, its explicit kernel is

\[
 K_{A,L}(n,m)=\frac{[L-[\max(n,m)-A]_+]_+}{L}.
\]

The compiled theorem
`pairedEtaCompletedMoebiusLargeMeanSquare_eq_bilinear_window` gives the
whole complex matrix identity

\[
 H^{\rm High}_{A,L,D}
 =|X_\rho|^2\sum_{n,m\le A+L}
 K_{A,L}(n,m)b_D(n)b_D(m)n^{-\rho}\overline{m^{-\rho}}.
\]

All ordered pairs are included. The kernel is proved to lie in `[0,1]`,
and for `L>0` it is **one on the entire square `n,m<=A`**, including its
off-diagonal entries. Neither physical averaging nor the coefficient
collision bound makes this initial contribution diagonal. The next
estimate must use the actual Möbius coefficients and their signed
correlations against this explicit matrix, jointly across the product
bands. On `A=L=u³`, `D=u²`, any fixed positive gap below `|S_rho|²` on
arbitrarily large scales still suffices. No such gap or decay of this
uncentered form has been proved. No extension of the low-divisor range
is part of this slice.

## Uniform product-diagonal and growing short-shift decay

The next estimate uses the fixed coefficient sequence to remove a genuine
part of the whole product matrix. Put `sigma=Re(rho)` and

\[
 Z(p)=\sum_{n\ge1}\tau(n)^2 n^{-p},\qquad
 C_\rho=|X_\rho|^2 Z(\sigma+1/2).
\]

[NatDivisorSquareDirichlet](../RiemannGaussian/NatDivisorSquareDirichlet.lean)
proves `summable_card_divisors_sq_mul_rpow_neg`: `Z(p)` is a genuinely
convergent series for every `p>1`. The proof uses the checked full
`M*(1+log M)^3` divisor-square mean bound and Abel summation through
Mathlib's `LSeriesSummable_of_sum_norm_bigO_and_nonneg`. For
`1<p<=s`, `D>=1`, every finite upper endpoint satisfies the explicit bound

\[
 \sum_{D<n\le M}\tau(n)^2n^{-s}\le Z(p)D^{p-s}.
\]

This is `sum_Ioc_card_divisors_sq_mul_rpow_neg_le`. Since `b_D(n)=0`
for `n<=D` and `|b_D(n)|<=tau(n)`, it applies to the actual signed
coefficients without a moving-endpoint loss. In
[EtaMoebiusBilinearDiagonal](../RiemannGaussian/EtaMoebiusBilinearDiagonal.lean),
`pairedEtaCompletedMoebiusBilinearDiagonal_le_power` bounds the **entire
actual product diagonal**, with its physical overlap weights, by

\[
 \mathrm{Diag}_{\rho,A,L,D}
 \le |X_\rho|^2 Z(p)D^{p-2\sigma}.
\]

Taking `D=u²`, `p=sigma+1/2`, and `sigma>1/2` gives
`Diag<=C_rho*u^(1-2*sigma)` uniformly for every `A,L`. Its convergence
to zero is proved even for arbitrary sequences of physical windows.
The exact companion theorem
`pairedEtaCompletedMoebiusLargeMeanSquare_eq_diagonal_add_offDiagonal`
keeps the signed complex sum of all distinct products.

[EtaMoebiusBilinearShortShifts](../RiemannGaussian/EtaMoebiusBilinearShortShifts.lean)
goes beyond that diagonal. Define the actual completed near form by the
same full matrix, restricted only to `abs(n-m)<=H`; define the far form
by the complementary strict inequality. Both contain the original
complex coefficients and phases. The theorem
`pairedEtaCompletedMoebiusLargeMeanSquare_eq_near_add_far` proves

\[
 H^{\rm High}_{A,L,D}=\mathrm{Near}_{A,L,D,H}
                         +\mathrm{Far}_{A,L,D,H}
\]

as a complex identity, before taking real parts. Each band row has at
most `2H+1` entries. The finite quadratic estimate and the weighted
coefficient bound give

\[
 |\mathrm{Near}_{\rho,A,L,D,H}|
 \le (2H+1)|X_\rho|^2Z(p)D^{p-2\sigma}.
\]

In particular, for the mathematically defined radius

\[
 H_\rho(u)=\lfloor u^{\sigma-1/2}\rfloor,
\]

the compiled theorem
`norm_pairedEtaCompletedMoebiusBilinearNearForm_twoThirds_le` proves

\[
 |\mathrm{Near}_{\rho,A,L,u^2,H_\rho(u)}|
 \le 3C_\rho u^{1/2-\sigma}\longrightarrow0.
\]

The companion `pairedEtaMoebiusBilinearNearRadius_tendsto_atTop` proves
that this radius tends to infinity when `sigma>1/2`. Thus the estimate
removes an unbounded family of cross terms together with the diagonal;
it is not an assumption about the sign of any individual correlation.
The bound is uniform in `A,L`, including the original cubic windows.

The terminal source transport
`pairedEtaCompletedMoebiusBilinearFarForm_twoThirds_tendsto_source`
proves that the real part of the exact remaining long-shift form still
tends to `|S_rho|²` under the hypothetical right-half-zero assumption.
The next arithmetic target is a fixed positive gap below this source
square for that **whole signed far form**, on arbitrarily large original
scales. Near-form decay supplies no such gap by itself. A power rate for
the far form is sufficient but remains optional. No extension of the
low-divisor sampler, shifted-Möbius cancellation hypothesis, or RH-level
upper bound was used in the proved short-shift estimate.

## Growing reduced-ratio control among the long shifts

The next selection acts inside the surviving long-shift form, so it is
disjoint from the short band above. Write `g=gcd(n,m)` and retain the
pairs satisfying

\[
 H<|n-m|,\qquad n/g\le R,\quad m/g\le R.
\]

[EtaMoebiusBilinearRatioBands](../RiemannGaussian/EtaMoebiusBilinearRatioBands.lean)
proves `card_pairedEtaBilinearSmallRatio_le`: for each positive `n`, there
are at most `R²` such partners, uniformly in the endpoint. The injection
sends `m` to the pair `(n/g,m/g)`; equality of the first reduced factor
and the fixed positive `n` recovers `g`, then the second recovers `m`.
This bounds the row count even for long-range interactions such as
`m=2n`, which need not be in any short additive band.

Let `Ratio` be this actual completed complex selection and `Remainder`
the selection with `H<abs(n-m)` and at least one reduced factor greater
than `R`. The exact theorem
`pairedEtaCompletedMoebiusBilinearFarForm_eq_ratio_add_remainder`
proves `Far=Ratio+Remainder`, with all original matrix weights, Möbius
signs and Mellin phases. The finite quadratic estimate gives

\[
 |\mathrm{Ratio}_{\rho,A,L,D,H,R}|
 \le R^2|X_\rho|^2Z(p)D^{p-2\sigma}.
\]

Set

\[
 R_\rho(u)=\left\lfloor u^{(\sigma-1/2)/2}\right\rfloor.
\]

For `sigma>1/2`, this ratio bound is proved to tend to infinity, and
`norm_pairedEtaCompletedMoebiusBilinearRatioForm_twoThirds_le` gives

\[
 |\mathrm{Ratio}_{\rho,A,L,u^2,H,R_\rho(u)}|
 \le C_\rho u^{1/2-\sigma}\longrightarrow0
\]

uniformly in `A,L,H`. Thus an unbounded collection of long-range
rational product interactions is controlled as a whole, without making
an assumption about its individual signs. The combined terminal bound
`norm_pairedEtaCompletedMoebiusLargeMeanSquare_sub_ratioRemainder_twoThirds_le`
is the explicit estimate on the **original full physical energy**:

\[
 \left|H^{\rm High}_{\rho,A,L,u^2}
       -\mathrm{Remainder}_{\rho,A,L,u^2,H_\rho(u),R_\rho(u)}\right|
 \le 4C_\rho u^{1/2-\sigma}.
\]

The exact remainder is neither a new trial coefficient family nor a
substitute carrier. Both removed complex selections and their vanishing
allowance are proved. Its real part still tends to the nonzero source
square on the actual cubic windows, by
`pairedEtaCompletedMoebiusBilinearRatioRemainder_twoThirds_tendsto_source`.
The outstanding arithmetic task is an independent fixed sub-source gap
for this **whole signed remainder**, whose pairs have both long shifts
and a large reduced ratio factor. No uniform upper bound for it is
proved here. The divisor schedule and the original RH objective are
unchanged.

### Exploratory diagnostics for the remaining correlations

Floating-point probes used the actual fixed coefficient arrays through
`2*u³` for `u=32,64,128`, with mpmath approximations to the first two
critical-line zeros. They are exploration, not Lean certificates or
asymptotic estimates. An FFT evaluation grouped the exact physical
matrix by additive product shift and reconstructed the directly averaged
prefix energy to within `2e-13` in these samples. The positive and negative
shift totals were much larger than their signed difference: at the first
sampled zero and `u=128`, after division by the source square, they were
about `506.37` and `-506.22`, leaving about `0.151` off diagonal.

A separate gcd-ratio probe retained both reduced factors through `32`.
The remaining normalized contribution at `u=128` was about `-0.0178`
for the first sampled zero and `0.1071` for the second. These diagnostics
give no universal sign for the omitted ratio groups. In particular, the
proved vanishing selections above must not be used to discard the phase
or replace the remaining signed form by a sum of independently estimated
absolute correlations. The next estimate still needs a bound on that
whole remaining form; no numerical observation here supplies it.

The prior logarithmic Möbius family remains available as a separate
arithmetic program. Its complete growing head and quadratic tail decay,
and `p_M log M→1`; the band `floor(log M)<L≤M²` is still uncontrolled.
See the [arithmetic residual assessment](eta-parity-endgame-assessment.md).
Neither that gap nor the original weighted-current objective is closed
by this hyperbola package. No sharper numerical zero strip or novelty
claim about an RH-level theorem is made.

## Arithmetic cancellation across whole odd-prime product families

The next estimate uses the actual Möbius coefficients, rather than a
uniform bound for arbitrary vectors in the product matrix. For any odd
prime `p`,
[EtaMoebiusPrimeProduct](../RiemannGaussian/EtaMoebiusPrimeProduct.lean)
proves the exact coefficient identity

\[
 b_D(pn)=-\sum_{qd=n\atop D/p<d\le D,\ p\nmid d}\eta(q)\mu(d).
\]

The proof separates the two positions of `p` in the product. Its oddness
preserves the eta sign on the quotient, and Möbius multiplication gives
`mu(p*d)=-mu(d)` when `p` does not divide `d`, and zero otherwise. Both
divisor bijections retain the complete finite antidiagonal. In particular,
the square-factor zero is part of the proof, not an independence model.

Let `U_(p,D)(M)` be the original completed product prefix restricted to
`p|n`. The compiled theorem
`pairedEtaCompletedMoebiusPrimeProductAggregate_eq_annulus` identifies
this entire family, when `D<=M/p`, with

\[
 U_{p,D}(M)=-p^{-\rho}
   \sum_{D/p<d\le D\atop p\nmid d} T_\rho(M/p,d).
\]

[EtaMoebiusSelectedFamily](../RiemannGaussian/EtaMoebiusSelectedFamily.lean)
proves the full physical-window estimate uniformly for any fixed
selection `S` of original divisors through `D`. Both complex endpoint
errors remain in its allowance, and the weighted Fourier sampler retains
the complete factor `(4D²+L)/L`. No extension of the low-divisor sampling
range is asserted.

On the original schedule `u=p*v`, `D=u²`, `A=L=u³`, each divided
physical endpoint occurs exactly `p` times. The normalized sampling
identity retains the factor `p^(-2*sigma)`. The theorem
`pairedEtaMoebiusPrimeProductCubicEnergy_le` in
[EtaMoebiusPrimeProductDecay](../RiemannGaussian/EtaMoebiusPrimeProductDecay.lean)
proves

\[
 \frac1{u^3}\sum_{t<u^3}|U_{p,u^2}(u^3+t)|^2
 \le C_{\rho,p}(1+\log v)^2v^{3-6\sigma},
 \qquad \sigma=\operatorname{Re}\rho,
\]

where, with the existing physical and endpoint error constants `B,H`,

\[
 C_{\rho,p}=
 \bigl(10|X_\rho|^2C_{\rm sampling}+2(B+2H)^2\bigr)
 p^4(1+\log p)^2.
\]

The terminal `pairedEtaMoebiusPrimeProductCubicEnergy_tendsto_zero`
proves decay for every fixed odd prime and hypothetical `sigma>1/2`.
These are arbitrarily large members of the original cubic windows; the
theorem is stated along `u=p*v`, not along powers of two.

The removal includes the mixed terms. Write `H(v)` for the original
whole-window high energy and `P(v)` for the energy above. Define `W(v)`
as the complex average of the original full high prefix times the
conjugate of its entire prime-divisible part. The exact complementary
prefix keeps products with `p` not dividing `n`.
[EtaMoebiusPrimeExclusion](../RiemannGaussian/EtaMoebiusPrimeExclusion.lean)
proves

\[
 H_{p\nmid n}(v)=H(v)+P(v)-2\operatorname{Re}W(v),
 \qquad |W(v)|^2\le H(v)P(v).
\]

The original source limit and `P(v)->0` give `W(v)->0`. Consequently
`pairedEtaMoebiusLargeMeanSquare_sub_primeFree_tendsto_zero` proves that
deleting every row and column divisible by this fixed prime has vanishing
total signed cost. The actual complementary full energy still tends to
`|S_rho|²`, by `pairedEtaMoebiusPrimeFreeCubicEnergy_tendsto_source`.
No sign has been assigned to an individual cross term.

This controls dense divisibility classes of products by arithmetic
cancellation. It does not supply a fixed gap below the source for the
complement. The constant depends on `p`, and this theorem treats
one fixed odd prime at a time. The simultaneous extension below separately
accounts for the overlaps and accumulated error of a growing prime set.
The oddness condition is essential to this identity. None of these
statements proves the original uniform weighted bound or a new zero strip.

As a diagnostic only, floating-point samples at the first two
critical-line zeros gave normalized prime-product energies for `p=3`,
`v` replaced here by the original `u`, of about `0.00197` and `0.00822`
at `u=16`, and `0.0000719` and `0.0000976` at `u=128`. The numerical
test used the actual coefficient arrays and checked the prime coefficient
recurrence exactly as integer arrays. The Lean identities and bounds
above do not depend on those samples; no off-critical zero was sampled.

## Checked simultaneous growing odd-prime exclusion

The new terminal theorem is
`pairedEtaMoebiusLargeMeanSquare_sub_growingCoprime_tendsto_zero` in
[EtaMoebiusCoprimeExclusion](../RiemannGaussian/EtaMoebiusCoprimeExclusion.lean).
It controls a growing selection of original product rows and columns,
including their full complex mixed correlation. The proof uses finite
Möbius inversion and the actual selected-divisor Fourier estimate, with
no assumption about shifted Möbius correlations.

For an odd positive modulus `P`, let

\[
 G_{\rho,P,D}(M)=\chi_\rho
   \sum_{n\le M\atop (n,P)=1}b_D(n)n^{-\rho},\qquad
 S_{P,D}=\{1\le d\le D:(d,P)=1\}.
\]

These are the literal original product coefficients and their complex
completion. The theorem
`pairedEtaCompletedMoebiusCoprimeLowAggregate_eq_sieve` in
[EtaMoebiusCoprimeProduct](../RiemannGaussian/EtaMoebiusCoprimeProduct.lean)
identifies the whole sieved low family as

\[
 L_{\rho,P,D}(M)=\sum_{e\mid P}\mu(e)e^{-\rho}
   \sum_{d\in S_{P,D}}T_\rho(\lfloor M/e\rfloor,d).
\]

All intersections appear in this finite sum. For `M>=2`, `D<=M`,
`pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source` proves
exactly `L+G=S_rho`. Oddness preserves both dyadic source coefficients;
there is no squarefree-modulus hypothesis.

Write `sigma=Re(rho)` and

\[
 C_\rho=10|\chi_\rho|^2 C_{\rm sampling}+2(B_\rho+2H_\rho)^2.
\]

The constant uses the existing physical and endpoint error constants and
is independent of `P` and every cutoff. On the original schedule
`D=u²`, `A=L=u³`, whenever `u>=1` and `P|u`, the theorem
`pairedEtaMoebiusCoprimeLowCubicEnergy_le_divisors` in
[EtaMoebiusCoprimeWindow](../RiemannGaussian/EtaMoebiusCoprimeWindow.lean)
proves the precise modulus allowance

\[
 \frac1{u^3}\sum_{t<u^3}|L_{\rho,P,u^2}(u^3+t)|^2
 \le C_\rho\,\tau(P)\!\sum_{e\mid P}e^2\,
             (1+\log u)^2u^{3-6\sigma}
 \le C_\rho P^4(1+\log u)^2u^{3-6\sigma}.
\]

The individual divided term has cost at most `C_rho*e²` times the common
logarithmic and physical factors. Its complex multiplier exactly cancels
the rescaled physical power. The full window cost `(4D²+L/e)/(L/e)` and
the endpoint cost at `A/e` remain in the proof. Finite Cauchy--Schwarz
then controls all interactions between divisor terms together. This
does not extend the underlying sampler's critical low-divisor range.

[EtaMoebiusCoprimeGrowth](../RiemannGaussian/EtaMoebiusCoprimeGrowth.lean)
constructs the actual growing schedule

\[
 P_v=\prod_{j=0}^{v}(2j+1),\quad
 m_\rho=\left\lceil\frac8{6\sigma-3}\right\rceil_++1,\quad
 u_v=P_v^{m_\rho}.
\]

For a hypothetical `sigma>1/2`, its complete allowance is at most

\[
 C_\rho m_\rho^2(1+\log P_v)^2
          P_v^{4+m_\rho(3-6\sigma)}\longrightarrow0.
\]

Lean proves the exponent strictly negative, the scales cofinal, and
`P_v|u_v`. It also proves every odd prime through `2*v+1` divides the
modulus, and every fixed odd prime eventually excludes all its product
multiples. Thus the growing selection and the accumulated error are
both discharged on these explicit scales.

Let `R=High-G` be the entire excluded prefix. Its exact alternative
expression is `L-Low`, so its mean square tends to zero using the new
low sieve bound and the original low-family decay. Write `Q_R` for that
removed mean square, `E` for the original high energy, and `W` for the
complex mean of `High*conj(R)`. Lean proves

\[
 |W|^2\le E Q_R,\qquad E_G=E+Q_R-2\operatorname{Re}W.
\]

Consequently `Q_R->0`, `W->0`, `E-E_G->0`, and
`E_G->|S_rho|²`. Every mixed term is accounted for; no sign is assigned
to an individual matrix entry.

The remaining step is an **independent upper bound with a fixed positive
gap below `|S_rho|²`** for this surviving energy on arbitrarily large
scales. The schedule can grow very rapidly as `sigma` approaches one
half. Products with growing odd prime factors remain, and pointwise
exclusion of every fixed prime does not permit exchanging the sieve
limit with the growing product sum. Sparsity alone gives no signed
energy contraction. The original uniform weighted estimate, full
arithmetic residual decay, and RH remain unproved; this slice adds no
concrete zero bound.

## Research audit of the surviving products

This section records exploration after the checked growing sieve. It adds
no Lean theorem, arithmetic decay estimate, or zero bound. The reproducible
probe is [probe_eta_coprime_products.py](../scripts/probe_eta_coprime_products.py).
For example, run

```sh
python scripts/probe_eta_coprime_products.py --scales 32 64 128 \
  --zeros 1 2 --thresholds 1 7 --odd-factor-gram \
  --output /tmp/eta-coprime-products.json
```

The script constructs the original integer `b_D(n)`, checks selected entries
against their direct divisor definition, and averages every physical
endpoint `u³ <= M < 2*u³`, with `D=u²`. A threshold `y` keeps products
having no odd prime divisor at most `y`. All reported energies are divided
by the source square; the common completion factor cancels in this ratio.
The sampled points are the first two **critical-line zeros**, computed in
floating point. These cutoffs are not the proved `P_v,u_v` schedule and
these samples do not satisfy the hypothetical `Re(rho)>1/2` assumption.

At `u=128` the probe gives the following rounded values. The retained
fraction counts nonzero product coefficients through `2*u³`; it is not an
energy fraction. Write `G` for the surviving prefix and `R=High-G`.

| Sampled zero | Threshold `y` | Retained fraction | Surviving energy / source square | Removed energy / source square | Sum of root energies / source norm |
| --- | ---: | ---: | ---: | ---: | ---: |
| First | 7 | 0.575882 | 0.954596 | 0.000900 | 1.007028 |
| Second | 7 | 0.575882 | 0.945343 | 0.001824 | 1.015000 |
| First | 128 | 0.372572 | 0.135343 | 0.581073 | 1.130172 |
| Second | 128 | 0.372572 | 0.379997 | 0.204825 | 1.069015 |

Thus the small retained product count does not justify multiplying the
energy by that density. The aggressive sieve lowers the surviving energy
in these samples but leaves a substantial removed contribution. A bound
on `G` at that threshold cannot be transferred to the full form without
controlling `R` and its mixed term on the same scales. The script checks
the entire identity `E_High=E_G+E_R+2*Re mean(G*conj(R))`; it does not
assume the cross term is negative. This finite diagnostic neither refutes
nor proves the required bound at a hypothetical right-half zero.

### Retain cancellation between different factor counts

Let `omega_odd(n)` count the distinct odd prime divisors of `n`, and let
`F_j(M)` be the original completed surviving prefix restricted to
`omega_odd(n)=j`. The probe computes the full complex matrix

\[
 \Gamma_{jk}=\frac{1}{u^3|S_\rho|^2}
   \sum_{t<u^3}F_j(u^3+t)\overline{F_k(u^3+t)}.
\]

It checks both the prefix reconstruction and the sum of all matrix entries.
The grouping includes repeated prime factors and every original endpoint.
The following are rounded floating-point diagnostics at `u=128`:

| Sampled zero | Threshold | Sum of group energies | Sum of all cross terms | Whole energy |
| --- | ---: | ---: | ---: | ---: |
| First | 1 | 5.329146 | -4.329043 | 1.000103 |
| Second | 1 | 2.729281 | -1.729111 | 1.000170 |
| First | 7 | 2.093436 | -1.138840 | 0.954596 |
| Second | 7 | 1.243061 | -0.297718 | 0.945343 |

In the first sample without exclusions, the two- and three-factor group
energies are about `2.953824` and `1.949935`; their combined mutual cross
term is about `-4.603166`. This cancellation is lost if the groups are
estimated separately. In contrast, after the threshold `128` exclusion,
the sum of cross terms is positive in both samples. Neither the individual
entries nor their sum has an established universal sign.

An arithmetic recurrence through the least odd prime is therefore a more
specific next candidate than a density-only estimate. The existing
`pairedEtaMoebiusHighProductCoefficient_prime_mul` preserves the negative
Möbius annulus `D/p < d <= D` and the exclusion `p` not dividing `d`.
Regrouping by the least odd prime would make these product families
disjoint, while retaining every interaction between them. A useful next
theorem must estimate their **combined signed form**, with the changing
divided endpoints and the growing prime range still present. Another
partition identity or a favourable sign in these numerical matrices would
not discharge that estimate.

### Least-prime regrouping keeps a further signed matrix

The follow-up [least-prime probe](../scripts/probe_eta_least_prime_groups.py)
groups the same actual products by their least odd prime. Within each
prime family it also retains the complete matrix of factor counts. It
integrates the finite prefix step functions by their exact integer event
lengths, and independently checks that result against the sum of the
factor-count matrix entries. Only the arithmetic event lengths are exact;
the complex arithmetic and reported energies remain floating point.

```sh
python scripts/probe_eta_least_prime_groups.py --scale 128 --zeros 1 2 \
  --thresholds 1 7 128 --output /tmp/eta-least-prime-groups.json
```

Writing `H_p` for the surviving family with least odd prime `p`, this
distinguishes the nonnegative sum `sum_p mean(abs(H_p)^2)` from the full
energy, which also contains every interaction between different primes.
At `u=128` it gives these rounded source-normalized values:

| Sampled zero | Threshold | Sum of least-prime family energies | Cross terms between different primes | Whole energy |
| --- | ---: | ---: | ---: | ---: |
| First | 1 | 0.752261 | 0.247842 | 1.000103 |
| Second | 1 | 0.700827 | 0.299343 | 1.000170 |
| First | 7 | 0.751339 | 0.203258 | 0.954596 |
| Second | 7 | 0.698924 | 0.246419 | 0.945343 |
| First | 128 | 0.520138 | -0.384795 | 0.135343 |
| Second | 128 | 0.496867 | -0.116870 | 0.379997 |

In particular, the first two diagonal sums being below one is not a
sub-source bound for the whole form. The omitted cross terms raise the
energy back to approximately one. Their sign changes with the exclusion
threshold in these samples. The zero-dependent, uniform bound on the
complete matrix remains open.

There is also an exact obstruction to a generic contraction argument
based on the signs of an individual Möbius/eta pair. With `D=2`, the
literal product coefficients are `b_2(3)=-1` and `b_2(6)=2`. Set

\[
 s=\frac34+\frac{\pi}{\log2}i,\qquad
 a=-3^{-s},\qquad b=2\,6^{-s}.
\]

Then `2^(-s)=-2^(-3/4)`, so both terms have the same complex direction:
`b=-2^(1/4)*3^(-s)`. Consequently

\[
 |a+b|^2-|a|^2-|b|^2
   =2\,2^{1/4}|3^{-s}|^2>0.
\]

The temporary Lean audit
`EtaPrimePairingAudit.actual_pairing_contraction_fails` checks the literal
coefficient statement, `1/2<Re(s)<1`, and this strict failure of the pair
energy bound. Its transitive axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. This is a check of a proposed auxiliary inequality;
it is not an added library frontier theorem. The test exponent has no
zeta-zero hypothesis. A contraction using `zeta(s)=0`, or an estimate that
pays for positive pairs using other signed interactions, remains open.

### Why uniform harmonic Möbius control does not yet close this route

Tao's [A remark on partial sums involving the Möbius function](https://arxiv.org/abs/0908.4323)
proves the classical uniform estimate

\[
 A_P(x)=\sum_{n\le x,\ (n,P)=1}\frac{\mu(n)}n,
 \qquad |A_P(x)|\le1.
\]

The paper also explains that convergence for a fixed prime selection is
not uniform over changing selections. This is external prior work, not a
new project theorem or an imported Lean dependency.

For `X>=1` and `sigma=Re(s)<1`, ordinary Abel summation gives

\[
 \sum_{n\le X,\ (n,P)=1}\mu(n)n^{-s}
 =A_P(X)X^{1-s}+(s-1)\int_1^X A_P(t)t^{-s}\,dt.
\]

Taking absolute values using that harmonic estimate yields only

\[
 \left|\sum_{n\le X,\ (n,P)=1}\mu(n)n^{-s}\right|
 \le X^{1-\sigma}
   +\frac{|s-1|}{1-\sigma}\bigl(X^{1-\sigma}-1\bigr).
\]

The positive cutoff power survives. Applying this estimate separately to
the quotient endpoints supplies no fixed gap below the source square.
Any successful use of harmonic cancellation here must keep additional
signed cancellation through the Abel kernel or between the complete
arithmetic groups. Tightening only the already vanishing sieve allowance
does not control the surviving form.

## Direct first-mean cancellation and quartic windows

For a selected divisor set `E⊆[1,D]`, define the unchanged complex mean

\[
 \mathcal L_{\rho,E}(A)
 =\frac1A\sum_{t<A}\sum_{d\in E}T_\rho(A+t,d).
\]

The new theorem
`norm_pairedEtaCompletedMoebiusSelectedFirstMean_le` in
[EtaMoebiusFirstMean](../RiemannGaussian/EtaMoebiusFirstMean.lean)
proves, for `1≤A` and `D≤A`,

\[
 \left|\mathcal L_{\rho,E}(A)\right|
 \le C^{(1)}_\rho D^2 A^{-\sigma-1},\qquad
 C^{(1)}_\rho=B_\rho+2H_\rho+
       \frac{|\chi_\rho|}{2}(2+|\rho|).
\]

Here `B_rho` and `H_rho` are the existing physical and phase error
constants. They are not changed or assumed to vanish. The completion
factor is `chi_rho`; the constant depends on the actual zero but not
on the selected set, modulus, or physical cutoff.

The proof pairs `f_d(t)=(A+t)^(-rho)*eta(floor((A+t)/d))` with
`f_d(t+d)`. The parity flips exactly. Their difference in complex-power
weights is bounded by the existing derivative estimate. Shifting the
window leaves two boundary intervals of length `d`, giving

\[
 \left|\sum_{t<A} f_d(t)\right|
 \le (2+|\rho|)d A^{-\sigma}.
\]

The two normalization errors cost at most
`(B_rho+2*H_rho)*d*A^(-sigma)` in the whole physical sum. Only after this
signed cancellation is proved are norms summed over the divisor family.
This supplies `D²*A^(-sigma-1)` for the mean.

For `A=u⁴`, `D=u³`, the theorem
`norm_pairedEtaCompletedMoebiusSmallAverage_quartic_le` in
[EtaMoebiusQuarterQuotientMean](../RiemannGaussian/EtaMoebiusQuarterQuotientMean.lean)
specializes the allowance to

\[
 |\mathrm{LowMean}_\rho(u)|\le C^{(1)}_\rho u^{2-4\sigma}
 \longrightarrow0\quad(\sigma>1/2).
\]

The exact source split therefore gives
`pairedEtaCompletedMoebiusLargeFirstMean_quartic_tendsto_source`:
the entire high first mean tends to `S_rho≠0`. The quotient bound
`pairedEtaMoebiusHighQuotientCap_quartic_lt` is
`floor((u⁴+t)/(u³+1))<2*u` for every `t<u⁴`. This includes the clipped
endpoint. The separate quartic boundary theorem below now controls its
completion; the earlier cubic theorem is not used outside its range.

The high mean also has the exact single-sum formula
`pairedEtaCompletedMoebiusLargeFirstMean_eq_product_window`:

\[
 \mathrm{HighMean}_\rho(A,D)
 =\chi_\rho\sum_{1\le n\le2A}
      \frac{[A-(n-A)_+]_+}{A}\,b_D(n)n^{-\rho}.
\]

The weight is the diagonal evaluation of the existing physical prefix
window kernel, used here to count one prefix's occurrence. The coefficient
`b_D(n)` is unsquared; this is the entire complex mean, not a diagonal
approximation to the quadratic energy. All product phases remain in the
sum. No variance or mean-square decay is asserted on quartic windows.

### Combining the first mean with the growing prime sieve

For an odd modulus `P` dividing `u`, exact division into complete windows
gives

\[
 \left|\frac1{u^4}\sum_{t<u^4}e^{-\rho}
   \operatorname{Selected}_{\rho,E}
        \left(\left\lfloor\frac{u^4+t}{e}\right\rfloor\right)\right|
 \le C^{(1)}_\rho e\,u^{2-4\sigma}\quad(e\mid P).
\]

This is
`norm_pairedEtaCompletedMoebiusSelectedFirstMean_divided_quartic_le`
in [EtaMoebiusCoprimeFirstMean](../RiemannGaussian/EtaMoebiusCoprimeFirstMean.lean).
The factor `e` includes the change in the starting cutoff and window
length. Summing the actual Möbius sieve intersections gives the sharper
budget `C_rho*(sum_(e|P)e)*u^(2-4*sigma)` and then the uniform bound

\[
 |\mathrm{LowCoprimeMean}_\rho(P,u)|
 \le C^{(1)}_\rho P^2 u^{2-4\sigma}.
\]

The theorem `norm_pairedEtaMoebiusCoprimeLowQuarticFirstMean_le`
proves this with no fixed-modulus restriction. On the existing explicit
schedule

\[
 P_v=\prod_{j=0}^{v}(2j+1),\qquad
 m=\left\lceil\frac8{6\sigma-3}\right\rceil+1,\qquad u_v=P_v^m,
\]

the complete allowance is at most
`C_rho*P_v^(2+m*(2-4*sigma))`. The exponent is proved negative for
`sigma>1/2`; the entire low mean tends to zero. Every odd prime through
`2*v+1` is excluded simultaneously, with all intersections accounted for.
The same source survives exactly under odd coprimality. Consequently

\[
 \mathrm{CoprimeHighMean}_\rho(P_v,u_v)\longrightarrow S_\rho\ne0.
\]

The terminal theorem is
`pairedEtaMoebiusCoprimeQuarticFirstMean_growing_tendsto_source`.
The theorem
`pairedEtaCompletedMoebiusLargeFirstMean_sub_growingCoprime_tendsto_zero`
also proves that removing this entire growing prime family changes the
original high first mean by a quantity tending to zero. These assertions
are linear mean statements, not extensions of the old mixed-energy bounds.
The exponent and scale depend on the hypothetical zero; uniformity as
`sigma` tends down to `1/2` is not claimed.

### The remaining arithmetic target

Write `G_v` for this full surviving complex mean. For a fixed hypothetical
right-half zero, it would suffice to prove independently that some
`delta_rho>0` satisfies

\[
 |G_v|\le |S_\rho|-\delta_\rho
\]

on arbitrarily large indices `v`. A source-directed signed bound
`Re(G_v*conj(S_rho))≤|S_rho|²-delta_rho` on arbitrarily large indices
would also contradict the checked source limit. Full decay is sufficient
but unnecessary. Neither inequality is proved. Growing odd prime factors
remain in the actual sum; their sparsity does not control its coherent
complex contribution.

The new estimate reduces the retained quotient count for the first-mean
route from the cubic scale's order `A^(1/3)` to order `A^(1/4)`, and proves
that the growing sieve is compatible with this change. It does not supply
the independent arithmetic inequality needed to rule out a right-half
zero. No new zero bound, full residual decay, original weighted absolute
moment bound, or RH proof is claimed.

## Audit of the logarithmic contribution to the surviving first mean

The next investigation targets the surviving sum itself. The reproducible
[first-mean shell probe](../scripts/probe_eta_first_mean_shells.py)
counts complete quotient fibres and their clipped boundary over every
integer physical endpoint in `[u⁴,2*u⁴)`. Its separate fixed-product ramp
sum checks the original high mean. Optional exclusion of odd primes is
imposed on both arithmetic factors. The two formulas agreed in all 24
cases with `u=8,16,24,32`, the first two numerical critical-line zeros,
and prime thresholds `1,3,7`. Direct enumeration of every physical
endpoint and complete fibre also checked eight cases at `u=2`, including
empty surviving product families.

These are floating-point checks at critical-line zeros, not off-critical
examples or bounds. They do not implement the formal growing-modulus
schedule. The completion factor cancels in the reported ratios. Some
representative **complex** high means divided by the source are:

| Zero | `u` | Odd-prime threshold | Actual high mean / source |
| --- | ---: | ---: | ---: |
| First | 32 | 1 | `1.000082 - 0.000144 i` |
| Second | 32 | 1 | `0.999873 - 0.000044 i` |
| First | 32 | 3 | `1.000289 + 0.000735 i` |
| Second | 32 | 3 | `1.000497 - 0.000964 i` |
| First | 32 | 7 | `0.863026 - 0.018307 i` |
| Second | 32 | 7 | `0.834921 - 0.031203 i` |

The apparent finite gap at threshold seven needs particular care. An
explicit comparison input produces a similar finite gap while its full
limiting response is the source itself.

### Exact logarithmic response

Let `F_rho(q)` be the unchanged unpaired eta prefix and set

\[
 \mathcal H_\rho(Q)=\sum_{q=1}^{Q}F_\rho(q)
                    \log\frac{q+1}{q}.
\]

This is the complete quotient operator acting on a hypothetical weighted
Möbius prefix `B(x)=log x`: the prefix difference on the real complete
fibre is exactly `log((q+1)/q)`. It is a comparison input, not an asserted
formula for the actual arithmetic prefix, and it does not replace the
integer endpoint corrections in the original carrier.

Finite Abel summation gives exactly

\[
 \mathcal H_\rho(Q)
 =F_\rho(Q)\log(Q+1)
       -\sum_{n\le Q}\eta(n)n^{-\rho}\log n.
\]

The checked eta endpoint estimate makes the first term tend to zero.
The second term is the derivative of the literal finite eta polynomial;
its paired partial sums tend to the genuine eta derivative. The temporary
Lean audit `EtaLogarithmicModeAudit.logarithmicMode_even_tendsto_deriv`
therefore proves

\[
 \mathcal H_\rho(2N)\longrightarrow\eta'(\rho).
\]

At an actual zero, differentiating the existing local identity
`eta(s)=(1-2*2^(-s))*zeta(s)` gives
`eta'(rho)=(1-2*2^(-rho))*zeta'(rho)`. Thus, in the simple-zero case
`zeta'(rho)≠0`, the audit's terminal theorem
`EtaLogarithmicModeAudit.normalized_logarithmicMode_tendsto_source`
proves

\[
 \frac{\chi_\rho}{\zeta'(\rho)}\mathcal H_\rho(2N)
       \longrightarrow S_\rho\ne0.
\]

The audit is `/tmp/EtaLogarithmicModeAudit.lean` in the working environment.
It imports the compiled root library and passes direct elaboration with
warnings treated as errors. Both terminal axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. This diagnostic has not
been added to the library inventory or advertised as a new upper bound.
Its simple-zero normalization is explicit; no conclusion for multiple
zeros is inferred from dividing by a derivative that may vanish.

### Prime sieving preserves this comparison response

For a fixed odd prime selection, write
`E_P(s)=product_(p|P)(1-p^(-s))`. The coprime eta series is
`eta_P(s)=E_P(s)*eta(s)`. At a zero,
`eta_P'(rho)=E_P(rho)*eta'(rho)`. The comparison coefficient

\[
 \kappa_P=\frac1{\zeta'(\rho)E_P(\rho)}
\]

cancels that factor. Hence the logarithmic model again gives the same
source response. This derivative calculation explains why prime deletion
can redistribute this contribution across quotient shells without
eliminating its limiting amplitude. It is not an asymptotic theorem for
the actual coprime Möbius prefix or a uniform estimate for growing `P`.

The probe evaluates this model on the literal quotient-cap weights. At
threshold seven the first zero's model response divided by the source is
`0.869986 - 0.022943 i` at `u=32`, then
`0.999999965 - 0.000000010 i` at `u=4096`. For the second zero the
corresponding values are `0.838028 - 0.004709 i` and
`0.999999966 + 0.000000048 i`. The large-scale calculations here evaluate
only the explicit model; no actual Möbius sum at `u=4096` was computed.
They are reproducible with `--model-scales 32 128 512 4096`.

The remaining task therefore needs an arithmetic estimate that controls
this possible logarithmic contribution in the **actual** weighted Möbius
prefix. The zero equation, completed eta-tail decay, smoothness of a
comparison prefix, and fixed-prime exclusion are compatible with the
nonzero response just evaluated. They cannot by themselves justify a
bound below the source. No such independent bound was proved in this
audit. The full arithmetic decay and RH remain open.

## Completing the quartic boundary and auditing available arithmetic rates

The theorem `moebiusQuartic_boundary_card_le` in
[EtaMoebiusQuarticBoundary](../RiemannGaussian/EtaMoebiusQuarticBoundary.lean)
proves, for `u≥1` and `M≥u⁴`,

\[
 \#\left\{d:\left\lfloor
   \frac{M}{\lfloor M/(u^3+1)\rfloor+1}
   \right\rfloor<d\le u^3\right\}\le u^2.
\]

These are exactly the divisors added by completing the final quotient
fibre. Summing the existing completed-term norm bound over this actual
interval gives
`norm_pairedEtaCompletedMoebiusBoundaryFibre_quartic_le`:

\[
 |\mathrm{Boundary}_\rho(M,u^3)|
 \le C_{\mathrm{term},\rho}u^{2-4\sigma}.
\]

The estimate is uniform over every integer `M≥u⁴`, with the original
completion, Möbius coefficients, and physical decay. It does not invoke
any unproved arithmetic cancellation. On `[u⁴,2*u⁴)`, the boundary's
whole mean square is at most
`C_term²*u^(4-8*sigma)` and is proved to tend to zero for `sigma>1/2`.

The signed identity for the first mean is retained:

\[
 \mathrm{CompleteMean}=\mathrm{BoundaryMean}+\mathrm{HighMean}.
\]

The entire complete-quotient mean therefore satisfies

\[
 |\mathrm{CompleteMean}_\rho(u)-S_\rho|
 \le(C_{\mathrm{term},\rho}+C^{(1)}_\rho)u^{2-4\sigma}
 \longrightarrow0\quad(\sigma>1/2).
\]

The terminal theorem is
`pairedEtaCompletedMoebiusCompleteQuotientFirstMean_quartic_tendsto_source`.
This closes the boundary transport needed to apply the existing complete
quotient, Abel, and dyadic-shell identities on the quartic first-mean
route. Only the boundary's mean square is bounded here. A mean-square
estimate for the whole quartic carrier, and an independent first-mean
bound below the source norm, remain open. This theorem concerns the
unsieved boundary. The subsequent section proves its coprime extension
with the full modulus cost included.

The accompanying primary-source review found no ready-to-apply estimate
closing the surviving arithmetic gap. Inoue's
[Some explicit formulas for partial sums of Möbius functions](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1162.pdf)
gives unconditional explicit formulas retaining zero residues and
multiplicities, but its square-root-scale upper estimate in Theorem 3
assumes GRH, simplicity away from the central point, and a negative
derivative-moment bound. Those hypotheses are unavailable here.
Ng's [distribution theorem](https://arxiv.org/abs/math/0310381) likewise
assumes RH and a derivative-moment conjecture.

Tao and Teräväinen's
[quantitative Gowers-uniformity theorem](https://doi.org/10.4171/JEMS/1404)
provides unconditional, normalized uniformity estimates with doubly
logarithmic decay; the paper also records the stronger lower-order rates
and distinguishes normalized from unnormalized norms. My inference for
the present direct transfer is that a logarithmic rate cannot absorb a
remaining fixed positive physical-cutoff power. A new structural
estimate eliminating that power could make such results useful, but no
such transfer has been proved. None of these external results has been
imported as a Lean premise.

The repo's own finite complex Möbius estimate similarly retains
`(M+1)^(1-sigma)*exp(-h/2)` above a cutoff exponential in `h³`; its
Gaussian cancellation is normalized by `X^(1-sigma)`. Those precise
scales do not currently control the logarithmic contribution exposed by
the preceding audit. The independent bound below the source and the
original uniform weighted goal remain open.

## Completing the boundary after the growing coprime sieve

The module [EtaMoebiusCoprimeBoundary](../RiemannGaussian/EtaMoebiusCoprimeBoundary.lean)
closes the corresponding boundary estimate after imposing coprimality
on both original factors. For odd `P>0`, and `gcd(d,P)=1`, define the
literal term

\[
 T_{\rho,P}(M,d)=\mu(d)d^{-\rho}\chi_\rho
       \sum_{\substack{r\le M/d\\(r,P)=1}}\eta(r)r^{-\rho}.
\]

The theorem `pairedEtaCompletedMoebiusCoprimeTerm_eq_sum_mul` proves
the exact identity

\[
 T_{\rho,P}(M,d)=\sum_{e\mid P}T_\rho(M,de).
\]

Finite inclusion-exclusion accounts for every intersection. The original
coprimality selection implies `gcd(d,e)=1`, so Möbius multiplicativity
retains the actual coefficient. Terms with `de>M` are zero. Each term
with `de≤M` has the existing norm bound `C_term*M^(-sigma)`. Therefore
the whole sieved divisor term costs at most
`C_term*P*M^(-sigma)`, uniformly in `P` and `d`.

Completing the quartic fibre adds at most `u²` divisors, even before
coprimality is imposed. The theorem
`norm_pairedEtaCompletedMoebiusCoprimeBoundaryFibre_quartic_le` gives

\[
 |\mathrm{Boundary}_{\rho,P}(M,u^3)|
       \le C_{\mathrm{term},\rho}P u^{2-4\sigma}
       \qquad(M\ge u^4).
\]

The exact cutoff change is
`pairedEtaCompletedMoebiusCoprimeAggregate_complete_eq_boundary_add`.
The theorem
`pairedEtaCompletedMoebiusCoprimeAggregate_complete_eq_quotient_sum`
reindexes the resulting original product prefix into complete quotient
fibres, keeping both coprimality selections. The further
`sum_pairedEtaCompletedMoebiusCoprimeTerm_fibre_eq_prefix_mul` factors
each fibre into its signed Möbius block and its sieved eta prefix; no
complex phase is removed from this identity.

Combining the boundary norm with the already proved low-sieve estimate
gives `norm_pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_sub_source_le`:

\[
 |\mathrm{CompleteCoprimeMean}_\rho(P,u)-S_\rho|
 \le(C_{\mathrm{term},\rho}+C^{(1)}_\rho)P^2u^{2-4\sigma}
 \qquad(P\mid u,\ u\ge2).
\]

The same `P_v` and `u_v=P_v^m` satisfy
`2+m*(2-4*sigma)<0`. The terminal theorem
`pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_growing_tendsto_source`
therefore proves that the complete sieved first mean tends to `S_rho≠0`
at every hypothetical right-half zero. No fixed-modulus limit is
substituted for this simultaneous estimate.

The remaining target is now an independent estimate for this actual
complete coprime sum with a fixed positive gap below the source norm,
or below the source square in its source-directed real projection, on
arbitrarily large schedule indices. The logarithmic-response audit still
applies as a warning about comparison inputs: completion and sieve
transport do not themselves control the corresponding possible actual
arithmetic contribution. This slice proves no upper bound of that kind,
no whole quartic mean-square estimate, and no new zero exclusion.

## Quadratic Möbius factorization and the second eta factor

This investigation tests a different use of Möbius multiplicativity
inside the surviving arithmetic sum. Write `mu_U` for the actual
Möbius coefficients truncated at `U`, write `1_arith(n)=1` for `n≥1`,
and use `*` for Dirichlet convolution. The classical `K=2` Heath--Brown
identity states, for `n≤U²`,

\[
 \mu(n)=2\mu_U(n)-(1_{\rm arith}*\mu_U*\mu_U)(n).
\]

The identity and its short-factor range are given in Section 2 of
Helfgott and Thompson's
[Summing μ(n): a faster elementary algorithm](https://doi.org/10.1007/s40993-022-00408-8).
This is an existing arithmetic identity, not an original RH estimate.

Let `a(n)=eta(n)` and `b=a*mu`, so `b` has the original two source
coefficients at one and two. Convolving the identity with `a` yields

\[
 (a*1_{\rm arith}*\mu_U*\mu_U)(n)
       =2(a*\mu_U)(n)-b(n)\qquad(n\le U^2).
\]

Thus the completed source can be rewritten using two short Möbius
factors and the inner kernel with Dirichlet series `eta(s)*zeta(s)`.
The latter has an explicit smooth pole term. The probe subtracts that
term as a rank-one matrix, retaining its exact dependence on the
harmonic prefix `(sum_(a≤U) mu(a)/a)²`. It separately subtracts the
analytic constant as a complex rank-one matrix. These are actual
matrix subtractions, not removal of their diagonal entries alone.

### A second eta factor does not remove the arithmetic source

Multiplying by the second eta factor removes the smooth pole through
the exact dyadic identity

\[
 C_{\eta^2}(M)=C_{\eta\zeta}(M)
        -2^{1-s}C_{\eta\zeta}(\lfloor M/2\rfloor).
\]

But the truncated Möbius tail has no coefficients through `U`, so its
convolution square has no coefficients through `U²`. Expanding this
vanishing square gives the exact identity

\[
 (a*a*\mu_U*\mu_U)(n)
   =2\bigl(b*(a*\mu_U)\bigr)(n)-(b*b)(n)
       \qquad(n\le U^2).
\]

The temporary root-importing audit `/tmp/EtaQuadraticMobiusAudit.lean`
proves this as `EtaQuadraticMobiusAudit.eta_square_repeats_source`.
It also proves the classical coefficient identity as
`EtaQuadraticMobiusAudit.heathBrown_coefficient` and identifies `b`
with the unchanged project source in `EtaQuadraticMobiusAudit.etaSource_apply`.
Direct compilation with warnings as errors, all 14 declaration linters,
and the three terminal axiom reports pass. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. This is an unsieved
arithmetic diagnostic; it is not imported into the library inventory or
advertised as a new upper bound.

The Dirichlet polynomial of `b*b` is the square of
`alpha(s)=1-2*2^(-s)`. Consequently the second eta factor does not
annihilate the forced source. This explains algebraically why iterating
the eta factor is insufficient by itself. A further arithmetic
inequality for the actual short Möbius factors would still be needed.

### Full-matrix numerical audit

The new [quadratic Möbius probe](../scripts/probe_eta_quadratic_moebius.py)
uses `A=u⁴`, `U=ceil(sqrt(2*A))`, and **every** integer physical
endpoint `A≤M<2*A`. It checks the integer Heath--Brown identity for
every coefficient through `2*A-1` separately from the complex matrix
evaluation. It retains every pair `a,b≤U`. Optional odd-prime
exclusion is imposed on all original factors.

The 48 cases use `u=4,8,12,16`, the first two numerical zero ordinates,
real parts `1/2` and `3/4`, and odd-prime thresholds `1,3,7`.
The `3/4` samples are **not zeros**; their zeta values are recorded.
Both real matrices obtained by projection in the source direction have
positive and negative eigenvalues in all 48 cases, before and after
the second eta factor. This is finite numerical evidence against a
generic sign argument, not a theorem about a hypothetical off-critical
zero. Eight independent small-scale enumerations check both complete
quadratic sums directly using integer divisors, including the case
where all odd primes in the finite range are excluded. Odd-window
handling was checked separately.

For the first zero ordinate with no prime exclusion, representative
results are:

| `u` | Real part | Regularized first kernel / `alpha` | Regularized second kernel / `alpha²` | Second-kernel operator-norm allowance |
| ---: | ---: | --- | --- | ---: |
| 4 | `1/2` | `-0.996869 + 0.002100 i` | `-1.011649 - 0.005392 i` | `3.219596` |
| 8 | `1/2` | `-1.000070 + 0.000001 i` | `-1.000051 + 0.000054 i` | `8.707061` |
| 16 | `1/2` | `-1.000034 + 0.000006 i` | `-1.000009 + 0.000014 i` | `31.819717` |
| 4 | `3/4` | `-0.166425 + 0.022830 i` | `-0.170651 + 0.021050 i` | `0.827958` |
| 8 | `3/4` | `-0.087466 + 0.000815 i` | `-0.087465 + 0.000826 i` | `1.156663` |
| 16 | `3/4` | `-0.041871 + 0.003315 i` | `-0.041869 + 0.003316 i` | `2.128970` |

The operator allowance includes the full squared Euclidean norm of the
actual Möbius vector. Its finite value below one at `u=4`, real part
`3/4`, does not persist across these larger sample scales. No cofinal
upper bound is inferred. At `u=16` on the critical-line sample, the
second form's projected diagonal is about `-0.010302`; its off-diagonal
contribution is about `-0.989707`. Dropping the cross terms would remove
nearly the entire arithmetic response in this example.

The apparent decay at the nonzero `3/4` samples has a precise further
check. If `B_U(s)=sum_(a≤U) mu(a)*a^(-s)`, the second form after its
analytic constant is subtracted is exactly

\[
 -\bigl(1-\zeta(s)B_U(s)\bigr)^2
       +\text{the retained linear eta-tail error}
\]

after division by `alpha(s)²`. With coprimality, `zeta(s)` is replaced
by `E_P(s)*zeta(s)` and `B_U` by its coprime prefix. The probe checks
this equality as well. At the first ordinate, `u=16`, real part `3/4`,
the inverse-prefix defect square is
`0.041868713 - 0.003314359 i`; the linear error is only
`-0.000000187 + 0.000001269 i`. At a true zero the inverse-prefix
defect equals one, for every truncation, so this identity supplies no
independent decay estimate there.

The smooth-pole removal is therefore exact, but the arithmetic
difficulty persists in the whole quadratic form. This audit does not
reject the route for lacking a full power saving: it has not supplied
even the weaker fixed gap below the source on arbitrarily large scales.
The original complete-first-mean route remains the primary target.
Its next useful input must bound the actual Möbius correlations or
their source-directed signed contribution; repeated eta factorization
and generic matrix norms alone have not supplied that input. No new
library upper estimate, zero bound, full residual decay, or RH proof
was obtained in this investigation.

## Logarithmic correlation estimates and the resonant weight

The next primary-source review asks whether known cancellation in Möbius
correlations can supply the missing independent estimate. Tao's
[logarithmically averaged two-point Chowla and Elliott theorem](https://arxiv.org/pdf/1509.05422)
gives cancellation after division by the logarithmic length of the
averaging interval, for fixed nondegenerate affine forms. Its quantitative
threshold depends on the forms and the desired normalized error. The
paper does not provide the power estimate needed by the direct weighted
transfer considered here. In particular, its growing logarithmic interval
must not be replaced silently by one fixed dyadic interval.

Matomäki, Radziwiłł, and Tao's
[averaged form of Chowla's conjecture](https://arxiv.org/pdf/1503.05121)
also controls the average of absolute correlations over shifts. The
quantitative error in Theorem 1.1 is logarithmic in the shift range and
the physical cutoff, after normalization by their product. This is
substantial cancellation for that statistic. It does not by itself
control the differently normalized weighted form in this project.

### The direct transfer still has a positive power cost

The first band of the project's unchanged product coefficients is
`b_D(n)=mu(n)` for `D<n≤2D`. Its full weighted square contains

\[
 2\operatorname{Re}\sum_{h=1}^{D-1}
   \sum_{n=D+1}^{2D-h}
      \mu(n)\mu(n+h)n^{-\rho}(n+h)^{-\overline\rho},
\]

as well as its diagonal. The weights have size comparable to
`D^(-2*sigma)` on this band. A direct absolute correlation budget of
size `epsilon(D)*D²`, **if also available with the partial-sum uniformity
needed for the weights**, therefore gives an allowance of size

\[
 C_\rho\,\epsilon(D)D^{2-2\sigma}.
\]

Likewise, directly transferring a one-variable normalized cancellation
error leaves an allowance proportional to
`epsilon(A)*A^(1-sigma)` in the weighted first sum. Both displayed
powers are positive for `sigma<1`. A normalized error tending to zero,
even one with the cited logarithmic rates, does not ensure that either
allowance is eventually below a fixed source threshold. This audit is
not demanding full decay where a fixed gap would suffice: the direct
allowance has not yet supplied that weaker gap either.

There is a further uniformity issue beyond this rate cost. The full
`b_D` is a truncated convolution, rather than a bounded multiplicative
function. Expanding it into Möbius factors and applying the growing
coprime selection creates varying affine parameters and arithmetic
conditions. Fixed-parameter correlation results do not automatically
cover those expressions with uniform constants. Moreover, the existing
library already removes a growing band of short product shifts. A new
argument must control the surviving longer shifts and all their cross
terms, or estimate their full source-directed sum together.

### A Lean diagnostic distinguishes correlation decay from weighted decay

The temporary root-importing file `/tmp/EtaLogCorrelationAudit.lean`
checks a comparison sequence, for any `s` with `Re(s)<1`:

\[
 a_s(n)=n^{s-1}\qquad(n\ge1).
\]

The theorem `EtaLogCorrelationAudit.resonantCoefficient_mul` proves
complete multiplicativity, and
`EtaLogCorrelationAudit.norm_resonantCoefficient_le_one` proves
`|a_s(n)|≤1` on positive integers. Nevertheless, the exactly matched
Dirichlet weight satisfies `a_s(n)*n^(-s)=1/n`. Thus
`EtaLogCorrelationAudit.weightedPrefix_eq_harmonic` identifies its
weighted prefix with the actual harmonic sum, and
`EtaLogCorrelationAudit.norm_weightedPrefix_tendsto_atTop` proves
divergence. The stronger local check
`EtaLogCorrelationAudit.one_half_le_norm_weightedDyadicBlock` proves

\[
 \left|\sum_{N<n\le2N}a_s(n)n^{-s}\right|\ge\frac12
       \qquad(N\ge1).
\]

At the same time, every logarithmic correlation satisfies the bound

\[
 \left|\sum_{n=1}^{M}
   \frac{a_s(n)\overline{a_s(n+h)}}{n}\right|
 \le \sum_{n=1}^{\infty}n^{2\operatorname{Re}(s)-3}<\infty,
\]

uniformly in **both** `M` and `h`. The terminal theorem
`EtaLogCorrelationAudit.normalized_logarithmicCorrelation_tendsto_zero`
therefore proves that its norm divided by `log(M+2)` tends to zero,
even for an arbitrary shift function `h(M)`. The full complex correlation
is retained as a definition before taking this downstream norm bound.

This example shows that bounded complete multiplicativity and even this
uniform normalized correlation decay do not imply decay of the matched
weighted dyadic block. It is **not** the Möbius function: its prime
values, coefficient magnitudes, and convolution identities differ.
No equality with the actual arithmetic residual is asserted, and this
does not rule out a stronger argument using those additional arithmetic
properties. It identifies a precise limitation of using only the
compressed correlation statistic.

Direct compilation with warnings as errors passes. All 14 declaration
linters pass on 13 declarations and 8 automatically generated declarations;
the three terminal axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. This diagnostic is not imported
into the library or counted as a new frontier estimate.

The independent bound for the actual complete Möbius first mean remains
open. The next candidate must exploit an additional Möbius-specific
identity or inequality while preserving the whole complex weighted
carrier. A logarithmically normalized cancellation theorem alone is
insufficient for the transfer audited here. This investigation adds no
zero bound, full arithmetic decay theorem, or proof of RH.

## Polynomially growing prime families in the original complex mean

The next arithmetic slice uses the actual Möbius prime identity, rather
than a normalized correlation statistic. The new module
[EtaMoebiusPrimeFirstMean](../RiemannGaussian/EtaMoebiusPrimeFirstMean.lean)
removes the scale-divisibility restriction from the prime-class
first-mean estimate. This permits simultaneous control of a polynomially
growing family of prime classes on **every** quartic scale.

Write `F_p(rho;A,D)` for the complex physical mean of the original high
product prefix restricted to `p|n`, over every integer endpoint
`A≤M<2A`. The coefficients remain the literal `b_D(n)` from the full
hyperbola. The exact prime identity gives, for `p*D≤M`,

\[
 \operatorname{PrimeAggregate}_\rho(p,D,M)
   =\sum_{D/p<d\le D,\ p\nmid d} T_\rho(M,pd).
\]

This is
`pairedEtaCompletedMoebiusPrimeProductAggregate_eq_original_annulus`.
It uses `mu(p*d)=-mu(d)` when `p` does not divide `d`, the complete
complex power of `p*d`, and the exact identity
`floor(floor(M/p)/d)=floor(M/(p*d))`. The physical endpoint itself is
unchanged. Thus the already checked direct parity estimate applies at
the original index `p*d`; there is no divided physical window whose
endpoints have to be multiples of `p`.

The original first-mean constant already includes both normalization
errors and the derivative cost. Summing its bound over the annulus gives
`norm_pairedEtaMoebiusPrimeProductFirstMean_le`:

\[
 |F_p(\rho;A,D)|\le C_\rho\,pD^2A^{-\sigma-1}
       \qquad(pD\le A,\ A\ge1).
\]

In particular, on `A=u⁴`, `D=u³`, every odd prime `p≤u` satisfies

\[
 |F_p(\rho;u^4,u^3)|\le C_\rho\,p\,u^{2-4\sigma}.
\]

This is `norm_pairedEtaMoebiusPrimeProductFirstMean_quartic_le`.
Unlike the earlier divided-window estimate, it has no hypothesis
`p|u`. Its prime dependence is explicit and linear.

### The whole growing family has a vanishing norm sum

Set

\[
 R_\rho(u)=\left\lfloor u^{\sigma-1/2}\right\rfloor.
\]

At a hypothetical right-half zero, this cutoff tends to infinity.
Since every nontrivial zero has `sigma<1`, it is at most `u` for `u≥1`.
The elementary finite estimate `sum_(p≤R) p≤R²` therefore gives

\[
 \sum_{\substack{p\le R_\rho(u)\\p\text{ odd prime}}}
       |F_p(\rho;u^4,u^3)|
 \le C_\rho u^{1-2\sigma} \longrightarrow 0
        \qquad(\sigma>1/2).
\]

The quantitative theorem is
`sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_le`; the
terminal limit is
`sum_norm_pairedEtaMoebiusPrimeProductFirstMean_growing_tendsto_zero`.
This controls the **sum of the norms of all class means**, rather than
proving a separate fixed-prime limit and then exchanging quantifiers.
It also does not require a common scale divisible by all the primes.

Consequently any complex weights `w_u(p)` of norm at most one, chosen
separately at each scale, satisfy

\[
 \left|\sum_{p\le R_\rho(u),\ p\text{ odd prime}}
            w_u(p)F_p(\rho;u^4,u^3)\right|
 \le C_\rho u^{1-2\sigma}\longrightarrow0.
\]

These are the checked
`norm_pairedEtaMoebiusWeightedPrimeFirstMean_growing_le` and
`pairedEtaMoebiusWeightedPrimeFirstMean_growing_tendsto_zero`.
The weights may depend on the scale, the zero, or arithmetic data,
provided their displayed norm bound is proved.

### Exact residual and the next arithmetic obligation

The theorem
`pairedEtaCompletedMoebiusLargeFirstMean_sub_weightedPrime_eq_products`
retains the exact subtraction from the original high mean:

\[
 \frac1A\sum_{M=A}^{2A-1}\chi_\rho
     \sum_{n\le M}b_D(n)n^{-\rho}
       \left(1-\sum_{\substack{p\le R,\ p\text{ odd prime}\\p\mid n}}
                        w(p)\right).
\]

Every original physical endpoint and every overlap survives this
identity. In particular, unit weights give `1-omega_R(n)`, where
`omega_R` counts the distinct selected odd primes dividing `n`.
A product divisible by two selected primes has residual multiplier
`-1`, not zero. The result is a weighted arithmetic residual, **not**
hard removal of the union of prime divisibility classes.

The terminal theorem
`pairedEtaCompletedMoebiusLargeFirstMean_sub_weightedPrime_growing_tendsto_source`
proves that this residual still tends to the original nonzero source,
uniformly in the stated sense over the scale-dependent bounded weights.
It applies to the original product carrier; it does not silently combine
the weighted family with the separate complete coprime carrier.

The next task is to choose and estimate weights for which this **whole
signed residual** admits an independent bound below the source. The
new allowance pays for the entire selected prime family, but does not
prove that remaining estimate. It also gives no mean-absolute-value
bound, whole quartic mean-square bound, new zero exclusion, full
arithmetic decay theorem, or proof of RH.

The module's 12 public theorems pass direct compilation with warnings
as errors, the focused build, and the full 9,709-job build. The whole
project passes all 14 declaration linters on 12,216 declarations and
5,912 automatically generated declarations. The root-importing audit
`/tmp/EtaPrimeFirstMeanAudit.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for all 12 new public theorems.
The source placeholder scan and whitespace check pass. The regenerated
inventory is byte-identical on repeat and records 862 compiled project
modules, no project axioms, no placeholder-dependent declarations, and
`rhImplied=false`. These checks were performed locally.

## Exact harmonic weights at the larger prime cutoff

The next slice chooses mathematically defined coefficients and pays their
entire first-mean cost at a larger prime cutoff. In
[EtaMoebiusPrimeSieveWeights](../RiemannGaussian/EtaMoebiusPrimeSieveWeights.lean),
define

\[
 H_R=\sum_{\substack{p\le R\\p\text{ odd prime}}}\frac1{p-1},
 \qquad
 w_R(p)=\frac{p}{(p-1)(1+H_R)}.
\]

These are exact real coefficients, not fitted decimals. The theorems
`pairedEtaPrimeSieveWeight_nonneg`, `pairedEtaPrimeSieveWeight_le_one`,
and `pairedEtaPrimeSieveWeight_le_harmonic` prove, on the selected primes,

\[
 0\le w_R(p)\le1,
 \qquad w_R(p)\le\frac2{1+H_R}.
\]

The normalizer tends to infinity by
`pairedEtaPrimeSieveHarmonicMass_tendsto_atTop`. Its proof uses Mathlib's
checked divergence of the sum of prime reciprocals, removes the single
prime two, and compares `1/p` with `1/(p-1)`. No prime number theorem or
unproved rate for that divergence is used.

### The exact coefficients pay for twice the previous cutoff exponent

The preceding prime-family theorem gives
`sum_(p≤R) |F_p| ≤ C_rho R² u^(2-4*sigma)` for `R≤u`. Applying the
common weight bound **before** removing its harmonic factor yields
`norm_pairedEtaMoebiusWeightedPrimeFirstMean_harmonic_le`:

\[
 \left|\sum_{p\le R,\ p\text{ odd prime}}
            w_R(p)F_p(\rho;u^4,u^3)\right|
 \le\frac{2C_\rho R^2u^{2-4\sigma}}{1+H_R}.
\]

Now take `R=floor(u^(2*sigma-1))`, instead of the earlier
`floor(u^(sigma-1/2))`. This cutoff is at most `u` because `sigma<1`.
The polynomial factors cancel:

\[
 R^2u^{2-4\sigma}\le1.
\]

Thus `norm_pairedEtaMoebiusHarmonicPrimeFirstMean_le` proves the
finite bound `2*C_rho/(1+H_R)` for the **entire** weighted prime
correction. Both `R` and `H_R` tend to infinity when `sigma>1/2`, so
`pairedEtaMoebiusHarmonicPrimeFirstMean_tendsto_zero` proves that this
correction tends to zero. No extra power saving is required to pay for
this larger weighted family.

This extension is for the specified harmonic weights. It is not a claim
that all arbitrary unit weights have vanishing cost at the larger
cutoff. The earlier uniform arbitrary-weight theorem retains its
original smaller cutoff. The new module estimates a complex first mean;
it makes no assertion about the whole quartic mean square.

### Why the density calculation is only a candidate-selection input

Choosing sieve coefficients by quadratic optimization is a standard
method; see Tao's
[sieve theory notes](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/).
Their upper-bound sieve framework uses nonnegative underlying weights.
That hypothesis does not hold for the project's complex signed product
coefficients. The implementation therefore keeps the counting calculation
separate from the actual Möbius carrier and does not apply a positive
sieve inequality to the latter.

For a finite prime family, the complete-period divisor Gram matrix is
`G_pq=1/lcm(p,q)`. The associated counting quadratic is

\[
 Q_R(w)=1-2\sum_p\frac{w_p}{p}
            +\sum_{p,q}\frac{w_pw_q}{\operatorname{lcm}(p,q)}.
\]

The [new probe](../scripts/probe_eta_prime_sieve_weights.py) checks the
normal equations `G*w=(1/p)_p`, the unit weight bounds, and the value
`Q_R(w)=1/(1+H_R)` using **exact rational arithmetic** at every tested
prime cutoff. For primes `3,5,7`, the weights are exactly
`18/23,15/23,14/23` and this counting value is `12/23`.
These rational checks motivate the choice of coefficients. They are
distinct from both the Lean theorem for the actual weighted correction
and an unproved bound for the remaining Möbius sum.

The probe separately evaluates the full actual complex first mean and
the whole physical mean square, using every integer endpoint in
`[u⁴,2*u⁴)`. Its Gram calculation retains all prime-class cross terms
and every mixed term with the original high aggregate. A literal product
ramp independently checks the residual multiplier
`1-sum_(p|n) w_R(p)`. The finite counting quadratic is also checked
using the exact integer counts `floor(N/lcm(p,q))`, so a complete-period
statistic is not silently substituted for a finite interval.

The 80 cases use `u=8,16,24,32`, the first two numerical zero ordinates,
real parts `1/2` and `3/4`, and available prime thresholds
`3,7,13,31`, together with the exact endpoint cutoffs at these parameters.
Sixteen cases use the corresponding endpoint cutoff. The real-part
`3/4` samples are **not zeros**, and their zeta values are recorded.
Twelve independent small-scale checks enumerate the original integer
divisors and Möbius coefficients directly, then accumulate every physical
prefix and its full energy. All checks pass.

For the first critical-line zero and the fixed prime family `3,5,7`,
the representative values are:

| `u` | Finite counting mean square | Actual residual first mean / source | Actual residual energy / source square | Direct Cauchy allowance / source norm |
| ---: | ---: | --- | ---: | ---: |
| 8 | `0.521856` | `0.802230 - 0.024427 i` | `0.652548` | `36.326883` |
| 16 | `0.521740` | `0.937593 - 0.024786 i` | `0.883651` | `161.676265` |
| 32 | `0.521739` | `1.000393 - 0.000256 i` | `1.001506` | `705.042344` |

The counting improvement persists while the finite gap below the source
disappears in these samples. The direct Cauchy estimate also grows over
these scales. These are finite critical-line observations, not a
counterexample to an estimate whose hypotheses include `sigma>1/2`.
The off-critical samples likewise provide no evidence of an off-critical
zero: at real part `3/4`, the same Cauchy allowance grows from about
`6.066052` at `u=8` to `37.075490` at `u=32`, despite the small actual
residual there.

The terminal theorem
`pairedEtaCompletedMoebiusLargeFirstMean_sub_harmonicPrime_tendsto_source`
proves that the exact signed residual with these larger-cutoff weights
still tends to the original nonzero source at a hypothetical right-half
zero. All overlaps remain in its multiplier, and the coefficients retain
their original complex phases. The next independent estimate must bound
that entire arithmetic residual, including its prime/composite
interference, below the source. A counting quadratic alone has not
supplied even that weaker fixed gap. The new slice proves decay of the
enlarged **weighted prime correction**, not full arithmetic decay, a new
zero bound, or RH.

All ten new public theorems pass direct compilation with warnings as
errors, the focused build, and the full 9,710-job build. The whole
project passes all 14 declaration linters on 12,231 declarations and
5,917 automatically generated declarations. The root-importing audit
`/tmp/EtaPrimeSieveWeightsAudit.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for all ten public theorems.
The source placeholder scan, probe syntax check, and whitespace check
pass. The regenerated inventory is byte-identical on repeat and records
863 compiled project modules, no project axioms, no placeholder-dependent
declarations, and `rhImplied=false`. The 80 probe cases are recorded in
`/tmp/eta-prime-sieve-weights.json`; the twelve independent enumerations
are in `/tmp/eta-prime-sieve-weights-direct-checks.json`. These checks were
performed locally.

## Prime/composite audit of the surviving weighted carrier

The next audit concerns the **remaining carrier**, rather than enlarging
the already controlled weighted correction. It separates products with
one distinct odd prime from products with at least two. The first group
includes all dyadic companions and all odd prime powers allowed by the
original coefficient; it is not just a sum over primes.

### Exact support checks

The root-importing diagnostic `/tmp/EtaPrimeRayAudit.lean` proves the
following statements for the actual integer coefficient `b_D(n)`:

- If `b_D(2^a*p^b) != 0`, then `D < 2*p`. Every contributing squarefree
  divisor divides `2*p`, so otherwise no divisor exceeds the cutoff.
- If `2*R <= D`, every selected odd prime through `R` has zero weight
  on each such active ray. Consequently **any** weighted sieve with that
  prime support leaves its full coefficient unchanged, including its sign.
  Lean checks that the current harmonic endpoint cutoff satisfies this
  condition for `D=u^3` and `u>=2`.
- If `u>=3`, `b>=2`, and `2^a*p^b <= 2*u^4`, that coefficient is zero.
  Indeed, nonvanishing would force `u^3 < 2*p` while the physical window
  forces `p^2 <= 2*u^4`; together these contradict `u^2 > 8`.
- For an odd prime `p`, a cofactor `m<=D` with `p` not dividing `m`
  satisfies the exact recurrence `b_D(p*m) = -b_(D/p)(m)`. This follows
  directly from the existing prime-removal annulus identity.
- If additionally `p>D`, the last coefficient is the negative complete
  eta source, supported only at cofactors `1` and `2`. Lean checks the
  resulting window statement: if `p>u^3` divides an active product
  `n<=2*u^4`, then `n=p` or `n=2*p`.

Thus every active product with at least two distinct odd primes has all
its prime factors at most `D`. The small-prime sieve acts only on this
composite group; it leaves the complete single-odd-prime group unchanged.
These are exact support statements, **not estimates for either group's
sum or for their mixed term**.

The diagnostic passes warning-as-error elaboration and all 14 declaration
linters on 13 declarations plus 12 automatically generated declarations.
The three terminal axiom audits report only `propext`, `Classical.choice`,
and `Quot.sound`. It remains a local diagnostic; it has not been added to
the root library or counted as a dashboard milestone.

### The complete physical Gram, with an independent prime formula

The [weighted-prime probe](../scripts/probe_eta_prime_sieve_weights.py)
now forms three actual physical prefix vectors: odd prime products, their
single-odd-prime companions, and products with at least two distinct odd
primes. The last group retains the literal residual multiplier
`1-sum_(p|n) w_R(p)`. All nine entries of their complex Gram matrix are
retained. Summing every entry recovers the whole residual energy;
summing all three complex means recovers its first mean.

All 80 cases pass these checks. Twelve independent small-scale checks use
direct divisor enumeration and separate prime factorizations, reconstruct
every physical prefix, and verify each complex mean and each of the nine
Gram entries. The checks include `u=2`, where higher powers of the sole
odd prime need not vanish. The pure-prime formula below is applied only
for `u>=3`.

For the first critical-line zero and the fixed weights on `3,5,7`, let
`P` denote the whole single-odd-prime group and `C` the weighted composite
group. The full physical energy decomposition is:

| `u` | `mean |P|^2 / |source|^2` | `mean |C|^2 / |source|^2` | `2 Re mean(P conj C) / |source|^2` | Whole residual energy / source square |
| ---: | ---: | ---: | ---: | ---: |
| 8 | `0.159482` | `0.167995` | `0.325071` | `0.652548` |
| 16 | `0.040772` | `0.565550` | `0.277329` | `0.883651` |
| 32 | `0.364841` | `0.273824` | `0.362841` | `1.001506` |

All 40 tested critical-line mixed terms are positive. The 40 off-critical
cases have 33 positive and seven negative mixed terms. This is finite
evidence about these parameters only: it neither establishes an eventual
sign nor refutes a theorem specific to hypothetical right-half zeros.
The off-critical samples are not zeros.

There is also an independent formula using only actual primes. Put
`A=u^4`, `D=u^3`, and
`r_A(n)=max(0,A-max(0,n-A))/A`, the literal first-mean product ramp.
For `u>=3`, the uncompleted single-odd-prime first mean is exactly

\[
 P_s(u)=
 \sum_{p>D}\bigl[-r_A(p)p^{-s}+2r_A(2p)(2p)^{-s}\bigr]
 +\sum_{D/2<p\le D}\left[
 r_A(2p)(2p)^{-s}-\sum_{a\ge2}r_A(2^ap)(2^ap)^{-s}\right].
\]

Only odd primes occur, and the ramp makes every sum finite. This follows
by listing the possible nonzero squarefree divisors `1,2,p,2*p`.
For `p>D`, the coefficients at `p,2*p,4*p,...` are `-1,2,0,...`;
for `D/2<p<=D`, they are `0,1,-1,-1,...`. Higher odd prime powers
have already vanished on this window. The probe checks the formula
against the original Möbius coefficients and every physical endpoint,
independently of the Gram reconstruction.

### Classical analytic consequence, not a Lean decay theorem

The classical prime number theorem with remainder gives
`pi(x)=Li(x)+O(x*exp(-c*sqrt(log x)))` for some `c>0`; a primary
formalization of this input is Song and Yao's
[Isabelle AFP entry](https://isa-afp.org/entries/PNT_with_Remainder.html).
That external result is **not imported into this Lean project**.
The following consequence is our analytic deduction from that input
and the finite formula above, not a new kernel-checked asymptotic.

Fix `s` with `0<sigma=Re(s)<1`, and write `z=1-s`. Partial summation
and two integrations by parts give

\[
 B_s(x):=\sum_{p\le x,\ p\text{ odd}}p^{-s}
 =\frac{x^z}{z\log x}+\frac{x^z}{z^2(\log x)^2}
   +O_s\!\left(\frac{x^{1-\sigma}}{(\log x)^3}\right).
\]

The prime pair cancels the first term, but leaves

\[
 -B_s(x)+2^{1-s}B_s(x/2)
 =\frac{\log2}{1-s}\frac{x^{1-s}}{(\log x)^2}
   +O_s\!\left(\frac{x^{1-\sigma}}{(\log x)^3}\right).
\]

All lower-cutoff and middle-prime dyadic contributions are
`O_s(D^(1-sigma))`, even using the integer-count bound for primes and
the convergent dyadic geometric series. Averaging the leading term over
the actual integer window `[A,2*A)` therefore yields

\[
 P_s(u)=c_s\frac{A^{1-s}}{(\log A)^2}
 +O_s\!\left(\frac{A^{1-\sigma}}{(\log A)^3}+D^{1-\sigma}\right),
 \qquad
 c_s=\frac{\log2\,(2^{2-s}-1)}{(1-s)(2-s)}\ne0.
\]

Here `D=A^(3/4)`, so both error terms are smaller than the leading
amplitude as `u` tends to infinity. Nonvanishing of the constant follows
from `|2^(2-s)|=2^(2-sigma)>1`. Thus the norm of this first mean
eventually grows like `|c_s|*A^(1-sigma)/(log A)^2`. The nonzero completion
factor at a nontrivial zero changes its coefficient, not that conclusion. The asymptotic is
for fixed `s`; no uniformity in the height or across the strip is claimed.

The probe records this eventual main term separately. The current finite
scales are far from a useful relative approximation to it. It is not
treated as a finite error allowance, and agreement with it is not a
criterion for the numerical checks.

This eliminates **separate decay of the single-prime group** as a viable
intermediate target. At a hypothetical right-half zero, the already
proved total first-mean limit forces the composite first mean to cancel
that growing group down to the fixed source plus a vanishing error.
Even an eventual relative cancellation tending to one would be too weak
for the proposed contradiction: an independent bound strictly below the
source requires absolute, constant-scale control of their full sum.
This discussion concerns the first means, not an asserted quartic
mean-square limit or an eventual sign of the physical Gram cross term.

The next useful estimate must therefore couple the prime group and the
remaining composite group **before** taking norms. The checked recurrence
`b_D(p*m)=-b_(D/p)(m)` for admissible cofactors gives a concrete way to
retain the prime phase and the original smaller-cutoff Möbius sum together.
No bound below the source has yet been proved for that joint expression.
This audit supplies no new zero bound and does not close arithmetic decay
or RH. At this audit stage the harmonic-weight theorem was the latest
verified library estimate; this diagnostic did not change the
README/dashboard frontier.

The 80 full-window cases are in `/tmp/eta-prime-composite-channels.json`;
the twelve independent checks are in
`/tmp/eta-prime-composite-channels-direct-checks.json`; the Lean audit log
is `/tmp/eta-prime-ray-audit.log`.

## A vanishing error for the joint large-prime product group

The prime-removal recurrence now gives an estimate for a group containing
both primes and composites. The root-imported module
[EtaMoebiusLargePrimeFirstMean](../RiemannGaussian/EtaMoebiusLargePrimeFirstMean.lean)
proves this result for the original coefficient and every physical
endpoint. No prime-density approximation or external analytic theorem
enters this Lean slice.

For `u>=2`, put `A=u^4`, `D=u^3`, and select the odd primes
`P_u={p : 2*u^2 < p <= 2*u^4}`. Write `K_u(M)` for the original completed
high-product sum restricted to products containing one of these primes,
and define the explicit prime model

\[
 V_u(M)=\chi(\rho)\left[
   2\sum_{p\in P_u,\ 2p\le M}(2p)^{-\rho}
   -\sum_{p\in P_u,\ p\le M}p^{-\rho}\right].
\]

Every product at most `2*A` contains at most one prime from `P_u`, so
the large-prime classes are exactly disjoint. In particular, `K_u`
contains each of its composite products once. It has not been replaced
by a sum that silently double-counts products with two selected primes.

For each selected prime, the exact divided-cofactor identity applies:
`M/p <= D` and `M < p^2`. The theorem
`pairedEtaCompletedMoebiusPrimeProductAggregate_eq_divided_large`
keeps the whole smaller-cutoff Möbius aggregate, including all its signs
and composite coefficients. Adding its low-divisor part then leaves
the complete eta source at `floor(M/p)`. The model theorem checks the
exceptional divided cutoffs `0` and `1` explicitly, so no missing upper
prime boundary is hidden in the source formula.

Let `L_u(M)` be the original completed low-divisor sum over
`d<=D` that carry a prime from `P_u`. The terminal exact identity is

\[
 K_u(M)-V_u(M)=-L_u(M),\qquad D\le M\le2A.
\]

This is
`pairedEtaMoebiusLargePrimeProductAggregate_sub_model`. Its first-mean
version retains every integer endpoint in `[A,2*A)`. Applying the
existing selected-divisor parity estimate gives

\[
 \left|\frac1A\sum_{M=A}^{2A-1}(K_u(M)-V_u(M))\right|
 \le C_\rho u^{2-4\sigma},\qquad \sigma=\Re(\rho).
\]

The checked theorem is
`norm_pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_le`.
`pairedEtaMoebiusLargePrimeProductFirstMean_sub_model_tendsto_zero`
proves that this allowance tends to zero at a hypothetical right-half
zero. The estimate applies to the **combined large-prime product group
minus its explicit model**, not to the model itself. It controls a
complex first mean, not a mean absolute value or a mean square.

### The coupled carrier that still needs an upper bound

Let `Q_u(M)` keep every complementary original product, containing no
prime from `P_u`. On this physical window all its prime factors are
at most `2*u^2`. The exact product partition gives
`High_u(M)=K_u(M)+Q_u(M)`. Consequently the retained joint mean is

\[
 J_u=\frac1A\sum_{M=A}^{2A-1}(V_u(M)+Q_u(M))
     =\operatorname{HighMean}_u+\operatorname{LowLargePrimeMean}_u.
\]

The definition `pairedEtaMoebiusPrimeSmoothFirstMean` takes this sum
before any norm. Lean proves both its exact relation to the original
high mean and the bounds

\[
 |J_u-\operatorname{HighMean}_u|\le C_\rho u^{2-4\sigma},
 \qquad |J_u-S_\rho|\le2C_\rho u^{2-4\sigma}.
\]

The terminal theorem `pairedEtaMoebiusPrimeSmoothFirstMean_tendsto_source`
therefore retains the nonzero source limit at a hypothetical right-half
zero. This gives a concrete next target: independently bound the **full
signed prime model plus complementary product mean** below the source,
or bound its source-directed real projection below the source square.
The model/complementary cross term must remain in that estimate.

This slice uses the original unweighted carrier. The earlier harmonic
prime correction has its separately proved vanishing cost. No bound for
a weighted subregion is inferred by restricting that earlier correction
to the new groups. Neither the new joint carrier nor either of its two
components has an independent bound below the source. Full arithmetic
decay, the original uniform weighted bound, and RH remain open; this is
not a new zero bound.

### Verification and finite probes

The [new probe](../scripts/probe_eta_large_prime_split.py) first checks
the disjointness and the **integer coefficient identity** across every
product through `2*A`. It then forms every original physical prefix,
checks the retained joint mean against the literal product ramp, and
retains the complete complex `2x2` Gram of the model and complementary
group. All mixed entries are included in the reported energy.

Sixteen cases use `u=4,8,16,32`, the first two numerical zero ordinates,
and real parts `1/2` and `3/4`. The latter samples are **not zeros**, and
their zeta values are recorded. Three independent small-scale coefficient
checks enumerate all divisors and prime factors directly at `u=2,3,4`;
six corresponding complex checks reconstruct every mean and all four
Gram entries without the array slicing used by the main probe. All pass.

For the first critical-line zero, representative whole-window values are:

| `u` | Joint large-prime error / source | Retained paired mean / source | Retained paired energy / source square |
| ---: | --- | --- | ---: |
| 4 | `0.020361 - 0.002850 i` | `0.983178 - 0.001112 i` | `0.970793` |
| 8 | `-0.000603 - 0.000506 i` | `0.998108 + 0.000920 i` | `0.997327` |
| 16 | `0.000014 - 0.000064 i` | `1.000129 - 0.000020 i` | `1.000557` |
| 32 | `0.000042 - 0.000080 i` | `1.000040 - 0.000064 i` | `1.000259` |

The small errors do not supply an independent source gap. In particular,
the finite gap seen at the smaller critical-line scales does not persist
in the larger samples. These finite critical-line observations neither
prove nor refute an estimate restricted to hypothetical right-half zeros.

All fourteen public theorems pass direct warning-as-error compilation,
the 4,389-job focused build, and the 9,711-job full build. The entire
root library passes all 14 declaration linters on 12,261 declarations
and 5,934 automatically generated declarations. The root-importing
`/tmp/EtaLargePrimeFirstMeanAudit.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for each new public theorem.
The numerical records are `/tmp/eta-large-prime-split.json` and
`/tmp/eta-large-prime-split-direct-checks.json`. Build, lint, and audit
logs use the `/tmp/eta-large-prime-first-mean-` prefix.

The regenerated inventory is byte-identical on repeat and records 864
compiled project modules, 18,214 compiled project declarations, 15,650
project theorems, no project axioms, no placeholder-dependent declarations,
and `rhImplied=false`. The source placeholder scan, all six research-probe
syntax checks, generated SVG parsing, README constraints, and whitespace
checks pass. The README and dashboard display the joint large-prime error
estimate and explicitly retain the remaining independent source-gap
obligation.

## Second prime removal: the rough model retains its unit source

The second removal was audited before attempting a rough-number decay
estimate. It reveals a normalization obstruction: the model excludes the
integer `1`, and that omission leaves exactly the original nonzero source.
This is a diagnostic of the proposed estimate, not a new bound for the
full signed carrier.

### The checked source identity and its modulus cost

For an odd positive integer `P`, define

\[
 E_P(M)=\sum_{\substack{1\le n\le M\\(n,P)=1}}
          (-1)^{n+1}n^{-\rho},\qquad
 R_P(M)=\sum_{\substack{1\le n\le M\\n\text{ odd},\ (n,P)=1}}n^{-\rho}.
\]

Write `R_P^>(M)=R_P(M)-1` for the nonunit prefix when `M>=1`.
The literal rough-number model is

\[
 V_P(M)=\chi(\rho)\left[
   2\,2^{-\rho}R_P^>(\lfloor M/2\rfloor)-R_P^>(M)\right].
\]

The root-importing local diagnostic `/tmp/EtaRoughSourceAudit.lean`
proves the positive-prefix odd/even split, keeps its complex dyadic
factor, and removes the unit explicitly. Its theorem
`EtaRoughSourceAudit.roughModel_sub_source` states, for `M>=2`,

\[
 \boxed{\quad V_P(M)=S_\rho-G_P(M),\qquad
 G_P(M)=\chi(\rho)\left[E_P(M)-2^{-\rho}E_P(\lfloor M/2\rfloor)\right].\quad}
\]

The theorem `norm_completed_coprimeEta_le` uses the compiled coprime
term estimate at divisor `1`, including the vanishing terms beyond the
physical cutoff. It yields

\[
 |\chi(\rho)E_P(M)|\le C_{\rm term}(\rho)P M^{-\sigma},\qquad
 |V_P(2N)-S_\rho|\le2C_{\rm term}(\rho)P N^{-\sigma}\quad(N\ge1).
\]

The latter is `norm_roughModel_even_sub_source_le`. Since every actual
nontrivial zero has `sigma>0`, `roughModel_even_fixed_tendsto_source`
proves convergence to the source for each **fixed** positive odd `P`.
`roughModel_even_fixed_not_tendsto_zero` then proves that this model
cannot tend to zero for fixed `P`. Neither conclusion requires the
stronger hypothetical condition `sigma>1/2`.

For a growing prime threshold `y`, the intended modulus is the product
of the odd primes at most `y`. The exact identity holds at each such
modulus, but the displayed allowance still contains that whole `P`.
No growing-modulus convergence theorem follows by treating `P` as
constant. More fundamentally, any independent proof that `G_P` tends
to zero would make `V_P` approach the **source**, not zero. Removing
the unit before a density approximation cannot erase this constant.

### The actual growing-cutoff coefficient calculation

The [rough-model probe](../scripts/probe_eta_rough_model.py) implements
the second removal at `y=2*u`, as well as the already checked
`y=2*u^2` case. At `A=u^4`, `D=u^3`, each product is classified using
its actual prime factors. Let `K_y` contain the original products with
a prime above `y`, `Q_y` the complementary original products, and
`L_y` the original low-divisor family whose divisors carry such a prime.
The rough model has coefficient `-1` at every nonunit odd `y`-rough
integer `r`, and coefficient `2` at `2*r`.

The working coefficient calculation is

\[
 K_y(M)-V_y(M)=-L_y(M),\qquad y=2u,\quad D\le M\le2A.
\]

Here is the arithmetic reason for the formula. If `n<=2*A` has a prime
above `y`, write `n=m*r` with all prime factors of `m` at most `y` and
all prime factors of `r` above `y`. Then `r` is odd and nonunit, and
`m<=n/p<D` for any prime `p>y` dividing `r`. The divisors of `n`
containing no large prime are exactly the divisors of `m`, and all are
within the low cutoff. Their complete Möbius--eta convolution is
`delta_(m=1)-2*delta_(m=2)`. The full convolution at `n` is zero,
leaving precisely the stated model and selected low-divisor error.
This general growing-cutoff calculation has **not** been added as a
Lean theorem. The probe checks its integer coefficients on every
tested product before applying floating-point powers.

At `y=2*u`, at most three rough prime factors fit, **counting
multiplicity**, since `(2*u)^4>2*u^4`. Consequently the model includes
prime squares, prime cubes when they fit, and mixed prime products.
It is a rough-number counting model; assigning it extra Möbius signs
would change the identity. The numerical carrier has four channels:
one, two, or three rough prime factors, and `Q_y`. All sixteen complex
Gram entries are retained.

### What an effective next bound would have to prove

Combining the model with its complement leaves

\[
 J_y=\operatorname{mean}(V_y+Q_y)
     =S_\rho+\operatorname{mean}(Q_y-G_y).
\]

Thus a sufficient independent bound would be, for some fixed
`delta>0`, on arbitrarily large admissible scales at a hypothetical
right-half zero,

\[
 \Re\!\left(\overline{S_\rho}\,
       \operatorname{mean}(Q_y-G_y)\right)
 \le-\delta|S_\rho|^2.
\]

The corresponding inequality for the already compiled `y=2*u^2`
carrier would contradict its proved source limit. Using `y=2*u` in
that chain also requires formalizing the displayed growing-cutoff
decomposition and transferring the selected low-divisor estimate.
An estimate tending to zero for `Q_y-G_y` would only reconstruct the
source again; separate rough density estimates or relative cancellation
are not a substitute for the fixed negative source projection.

Thirty-two floating-point cases use `u=4,8,16,32`, both thresholds,
the first two numerical zero ordinates, and real parts `1/2` and `3/4`.
The `3/4` samples are **not zeros**; their zeta values are recorded.
For the first critical-line zero and `y=2*u`:

| `u` | Rough model mean / source | Complementary mean / source | Retained joint mean / source | Joint energy / source square |
| ---: | --- | --- | --- | ---: |
| 4 | `0.903621 - 0.010986 i` | `0.100849 + 0.012954 i` | `1.004470 + 0.001968 i` | `1.009860` |
| 8 | `0.960941 + 0.043632 i` | `0.038631 - 0.043593 i` | `0.999573 + 0.000039 i` | `0.999299` |
| 16 | `1.000464 + 0.043976 i` | `-0.000496 - 0.043993 i` | `0.999968 - 0.000018 i` | `0.999990` |
| 32 | `0.999123 - 0.025869 i` | `0.000862 + 0.025895 i` | `0.999985 + 0.000026 i` | `0.999997` |

These values show the importance of the complete signed sum and its
unit term. They do not establish a uniform gap, and critical-line
samples do not refute an estimate restricted to right-half zeros.

The diagnostic passes warning-as-error Lean compilation and all 14
linters on 14 declarations plus 16 automatically generated ones. Its
four terminal axiom checks use only `propext`, `Classical.choice`, and
`Quot.sound`; the log is `/tmp/eta-rough-source-audit.log`. The main
records are `/tmp/eta-rough-model.json`. An independent direct-divisor
checker passes six complete integer windows and twelve complete
complex mean/Gram cases at `u=2,3,4`, recorded in
`/tmp/eta-rough-model-direct-checks.json`. This diagnostic does not
change the root-imported theorem inventory or its displayed frontier.
The independent signed upper bound, full arithmetic decay, and RH
remain open.

## Smooth-divisor audit: inverse defects and a growing first band

The next test keeps the actual smooth Möbius coefficients and checks what
the apparent off-critical source gaps measure. It also checks whether
separate cancellation of smooth divisor bands is a viable intermediate
bound. Both checks retain the source identified above.

### Exact link to the compiled joint carrier

For a finite divisor selection `S`, put

\[
 a(s)=1-2\,2^{-s},\qquad
 B_S(s)=\sum_{d\in S}\mu(d)d^{-s},
\]
\[
 W_S(s)=\frac1A\sum_{M=A}^{2A-1}\sum_{d\in S}\mu(d)d^{-s}
       \left[F_s(\lfloor M/d\rfloor)-a(s)\zeta(s)\right].
\]

The root-importing diagnostic `/tmp/EtaSmoothInverseAudit.lean` proves
`source_sub_selected_eq_inverse_defect` by exact finite summation.
It then takes `S` to be the complement of the compiled large-prime low
divisors inside `[1,u^3]`. The theorem
`primeSmoothFirstMean_eq_source_sub_selected` proves that the **actual
compiled** joint first mean is source minus this single selected low
family. No extra triangle bound or model assumption enters that step.

The terminal theorem
`primeSmoothFirstMean_eq_inverse_defect_sub_centered` gives

\[
 J_u=S_\rho\bigl(1-\zeta(\rho)B_S(\rho)\bigr)
                  -\chi(\rho)W_S(\rho).
\]

Here `selectedInverseDefect_at_zero` proves the parenthesized finite
defect is exactly `1` for **every actual zero**, regardless of the
selected divisors. Meanwhile `norm_completed_centered_firstMean_le`
transfers the already checked allowance
`C_rho*D^2*A^(-sigma-1)` to `chi(rho)*W_S(rho)`. Its decay recovers
the source. It does not bound the finite defect below one.

The compiled-carrier link in this diagnostic uses the existing
`y=2*u^2` selection. For `y=2*u`, the general finite inverse identity
also applies to its selected low divisors, while the separate general
rough-product reconstruction still has the formalization status stated
in the previous section.

### The first smooth product band has a nonzero main term

The root theorem `pairedEtaMoebiusHighProductCoefficient_eq_moebius`
identifies every coefficient on `D<n<=2*D` with `mu(n)`. The new local
theorem `smoothHighBand_eq_moebius` retains the actual smooth restriction
and complex powers in this equality. On quartic windows `2*D<=A`, so
this entire band lies inside every physical prefix.

For `M(x,y)=sum_(n<=x, P+(n)<=y) mu(n)`, Corollary 1.3 of
[de la Bretèche–Tenenbaum, *Friable averages of oscillating arithmetic functions*](https://arxiv.org/abs/2207.04777)
gives, in its admissible range,
`M(x,y)=x*omega'(log(x)/log(y))/(log y)^2+O(x/(log y)^3)` on the
compact smoothness range used here. This is an external asymptotic,
not a Lean theorem.

Our partial-summation calculation at `D=u^3`, `y=2*u` consequently gives,
for fixed `s` with `0<Re(s)<1`,

\[
 \sum_{\substack{D<n\le2D\\P^+(n)\le y}}\mu(n)n^{-s}
 =c_s\frac{D^{1-s}}{(\log y)^2}
       +O_s\!\left(\frac{D^{1-\Re(s)}}{(\log y)^3}\right),
 \qquad
 c_s=\frac{1/2-\log2}{9}\frac{2^{1-s}-1}{1-s}\ne0.
\]

Indeed `log(D)/log(y)` approaches `3` from below, where
`omega(v)=(1+log(v-1))/v`. This first band grows in norm. Any fixed
order of the separated logarithmic expansion still leaves a positive
power in its remainder allowance. This inference does not exclude a
bound for the complete signed sum.

The local theorem `hasDerivAt_buchstabMiddle_three` checks the displayed
derivative from its elementary logarithmic formula;
`buchstabSlopeThree_neg` and `smoothBandLeadingCoefficient_ne_zero`
check its sign and the nonvanishing complex dyadic factor. The theorem
`smoothBand_power_over_logPower_tendsto_atTop` proves that
`x^(1-sigma)/(log x)^k` tends to infinity for every fixed natural `k`
when `sigma<1`. These Lean checks validate the coefficient and the
exponent audit. They do **not** formalize the external Möbius asymptotic.
In particular, a triangle bound that estimates this band separately
cannot yield the desired fixed upper bound for the whole carrier.

### Whole-window checks and the resulting next target

The [smooth-inverse probe](../scripts/probe_eta_smooth_inverse.py)
computes every divisor's physical mean by complete quotient blocks,
checks their integer counts before applying complex powers, and retains
the complex centered eta error. All 32 cases reconstruct the earlier
full-product means, including every physical endpoint. The first zero
ordinate at `u=32`, `y=64` gives:

| Sample | Finite inverse defect | Centered eta error / source | Whole joint mean / source |
| --- | --- | --- | --- |
| `1/2+14.134725…i` | `1` to numerical precision | `0.000014733 - 0.000026396 i` | `0.999985267 + 0.000026396 i` |
| `3/4+14.134725…i` (**not a zero**) | `0.224176032 - 0.022018660 i` | `0.000000468 - 0.000000864 i` | `0.224175563 - 0.022017796 i` |

Thus the promising second-row value measures ordinary finite inverse
approximation at a nonzero zeta point. It is not evidence that the
defect becomes less than one at a zero. The probe also evaluates the
first smooth band and the Abel transform of the Buchstab leading model.
The leading model is inaccurate in some tested cases and is explicitly
**not an error bound**.

Twelve independent cases at `u=4,5,6` enumerate every physical endpoint
for every divisor, use direct prime factorizations and Möbius values,
and check the inverse defect, centered mean, and first smooth band.
They independently evaluate the model using its derivative density
instead of Abel boundary terms. All pass. Records are
`/tmp/eta-smooth-inverse.json` and
`/tmp/eta-smooth-inverse-direct-checks.json`.

The Lean diagnostic passes warning-as-error compilation and all 14
linters on 22 declarations plus 10 automatically generated ones. Its
seven terminal audits use only the three permitted standard axioms;
the log is `/tmp/eta-smooth-inverse-audit.log`. It does not change the
root theorem inventory or the displayed frontier.

The next independent estimate must keep the interference between the
first smooth band, later smooth bands, and the rough model. Separate
smooth-band decay, a fixed-order logarithmic allowance, and the finite
inverse-defect identity have not supplied a fixed source gap. The full
signed arithmetic upper bound, the original weighted goal, and RH
remain open. No new zero bound follows from this audit.

## Complete cutoff mixtures with their coefficient costs retained

The next coefficient test combines entire rough/smooth carriers. It does
not estimate rough factors or smooth bands separately. At `A=u^4`,
`D=u^3`, it uses seven prime thresholds between `2*u` and `2*u^2`,
deduplicated at small scales. For the corresponding smooth low-divisor
selections `S_i`, each physical column is

\[
 J_i(M)=S_\rho-\sum_{d\in S_i}T_\rho(M,d).
\]

The [probe](../scripts/probe_eta_cutoff_mixture.py) checks, with integer
coefficients at every product through `2*A`, that each column is exactly
its full rough model plus its complementary original product group.
This finite numerical audit includes the unit coefficient, prime powers,
and every physical prefix. The general rough-product identity retains
the formalization status stated above; the local Lean theorems below
apply directly to the actual selected-divisor expression displayed here.

### An admissible coefficient family

Let `sum_i w_i=1`, and let `J_w` be the complex first mean of
`sum_i w_i J_i(M)`. The root-importing diagnostic
`/tmp/EtaCutoffMixtureAudit.lean` proves exactly

\[
 J_w-S_\rho=-\sum_i w_i\operatorname{mean}
                    \sum_{d\in S_i}T_\rho(M,d).
\]

The first allowance follows from the compiled selected-family estimate:

\[
 \|J_w-S_\rho\|
 \le C_\rho u^{2-4\sigma}\sum_i|w_i|.
\]

However, using that triangle bound too early loses cancellation between
overlapping selections. Define the combined divisor coefficients and
their size-weighted mass by

\[
 g_w(d)=\sum_{i:d\in S_i}w_i,\qquad
 B_D(w)=\sum_{1\le d\le D}d\,|g_w(d)|.
\]

`cutoffMixture_sub_source_eq_weighted` retains this exact combined
coefficient vector. The terminal bound
`norm_cutoffMixture_sub_source_le_overlap` then proves

\[
 \boxed{\ \|J_w-S_\rho\|
       \le C_\rho A^{-\sigma-1}B_D(w)\ },\qquad
 B_D(w)\le D^2\sum_i|w_i|.
\]

The comparison is checked by `divisorMass_effective_le`. It does not
require nested selections; all their intersections are combined before
norms are taken. It uses the existing per-divisor first-mean theorem,
with the original Möbius term and completion factor retained.

An exact clipping rule makes this a usable mathematical constraint on
fitted coefficients. Start from an affine base vector `w0` with
`B_D(w0)<=R`, and put

\[
 \theta=\begin{cases}
  1,&B_D(w)\le R,\\[2pt]
  \dfrac{R-B_D(w_0)}{B_D(w)-B_D(w_0)},&B_D(w)>R.
 \end{cases}
 \qquad w_{\rm clip}=(1-\theta)w_0+\theta w.
\]

Lean proves `0<=theta<=1`, preserves the full complex affine
normalization, and proves `B_D(w_clip)<=R` in
`divisorMass_effective_clipped_le`. The denominator in the second case
is proved nonzero; no division at an exceptional case is hidden. This
rule uses the actual base mass instead of replacing it by one.

On the quartic schedule, choose `R=u^(5+2*sigma)`. Then
`norm_cutoffMixture_quartic_sub_source_le_overlap_budget` gives

\[
 \|J_{w_{\rm clip}}-S_\rho\|\le C_\rho u^{1-2\sigma}.
\]

`cutoffMixture_overlap_budget_tendsto_source` proves convergence to
`S_rho` when `sigma>1/2`, even when the selections, their number, and
the coefficients vary with `u`. Its budget is required only for
`u>=1`. This is a coefficient admissibility theorem. It supplies no
independent upper bound for the whole mixed carrier.

### Full physical optimization and checks

The numerical Gram matrix is

\[
 H_{ij}=\frac1A\sum_{M=A}^{2A-1}
          \overline{J_i(M)/S_\rho}\,J_j(M)/S_\rho.
\]

Every entry is retained, and the directly evaluated mixed energy is
checked against `w* H w`. Five choices are tested: unconstrained affine
least squares, regularized affine least squares, equal weights, clipping
by the coarse coefficient norm, and clipping by the combined divisor
mass. The regularized numerical solve uses
`(H+lambda*I)^(-1) 1`, normalized to have coefficient sum one, with
`lambda=u^(2-4*sigma)`. Its objective is checked against a feasible equal
mixture. No Lean optimality or rounding certificate is asserted.

At the first critical-line zero, all quantities below are numerical and
the RMS is normalized by the source norm:

| `u` | Unconstrained RMS | Coefficient mass | Combined mass `B_D/D^2` | RMS after combined-cost clipping |
| ---: | ---: | ---: | ---: | ---: |
| 4 | `0.860302` | `72.341092` | `1.878212` | `0.907002` |
| 8 | `0.991510` | `38.556049` | `1.031175` | `0.991523` |
| 16 | `0.998518` | `29.425124` | `0.750367` | `0.998518` |
| 32 | `0.999941` | `6.771525` | `0.323136` | `0.999941` |

Thus the coarse coefficient budget would discard useful overlap
cancellation. The sharper rule keeps the full unconstrained fit at the
last two scales, but those finite critical-line gaps still shrink.
Critical-line samples neither prove nor refute a bound restricted to
right-half zeros. The very small fitted values at `3/4+it` remain
samples at **nonzero** zeta points and retain the inverse-defect issue
identified in the preceding audit.

Every record also includes the measured signed correction to the
original carrier, its termwise triangle cost, and the full measured
source error. The inequality
`RMS + norm(measured mean - source) >= norm(source)` is a general
triangle/Jensen consistency check. It is not a new obstruction theorem
and does not rule out proving a stronger independent estimate under the
actual zero hypothesis. The recorded theoretical budget shapes omit
`C_rho/norm(S_rho)` and are explicitly not certified bounds.

The main run has 16 cases and 80 mixtures, recorded in
`/tmp/eta-cutoff-mixture.json`. Three independent integer-window checks
and six complete mean/Gram/optimization cases at `u=2,3,4` pass. The
checker uses direct factorizations and Möbius values, enumerates every
physical prefix with 40-digit powers, recomputes all Gram entries and
combined divisor masses, checks the affine normal equations, and solves
the regularized system independently. Its records are in
`/tmp/eta-cutoff-mixture-direct-checks.json`.

The local Lean diagnostic passes warning-as-error compilation and all
14 linters on 29 declarations plus 19 automatically generated ones.
Its eight terminal axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`; the log is `/tmp/eta-cutoff-mixture-audit.log`.

The next candidate should be assessed using the combined divisor cost
and the exact centered eta representation from the preceding audit.
An independent signed upper bound below the source remains necessary.
Neither the new coefficient rule nor the numerical fits prove arithmetic
decay, a new zero bound, or RH. The root theorem inventory and public
frontier are unchanged.

## Centering the cutoff scan removes its inverse-defect signal

The next [probe](../scripts/probe_eta_centered_cutoffs.py) retains the
same complete physical columns and divisor budget, but also tests the
exact centered eta representation. Put `a(s)=1-2*2^(-s)` and
`B_i(s)=sum_(d in S_i) mu(d)*d^(-s)`. Before completion, the centered
column is

\[
 \widehat J_i(M)=a(s)-\sum_{d\in S_i}\mu(d)d^{-s}
       \bigl[F_s(\lfloor M/d\rfloor)-a(s)\zeta(s)\bigr]
       =J_i(M)+a(s)\zeta(s)B_i(s).
\]

The local diagnostic `/tmp/EtaCenteredCutoffAudit.lean` proves this
pointwise in `centeredCarrier_eq_raw_add`. Its theorem
`completed_centeredCarrier_at_zero` identifies the completed centered
column with the original source minus the literal selected low family
at every actual zero. Centering at a nonzero point produces a different
carrier; it does not produce a new zero or impose a zero equation.

That distinction also affects the **total** Möbius convolution. Lean
proves `total_centered_eq_inverse_defect`:

\[
 \sum_{d\le M}\mu(d)d^{-s}
       [F_s(\lfloor M/d\rfloor)-a(s)\zeta(s)]
       =a(s)[1-\zeta(s)B_{[1,M]}(s)],\qquad M\ge2.
\]

Consequently the actual high centered divisor sum is
`centeredCarrier(s,[1,D],M)-a(s)*zeta(s)*B_[1,M](s)`, when `D<=M`.
This is checked by `high_centered_eq_carrier_sub_inverse`. The extra
term vanishes under the actual zero hypothesis; it cannot be dropped
at the off-critical nonzero samples. The centered experiment therefore
tests the local tail mechanism without pretending to satisfy the
complete zero-dependent arithmetic constraint.

### Every covariance cross term survives

For normalized column means `m_i` and shifts `c_i=zeta(s)*B_i(s)`,
the full Gram update is

\[
 \widehat H_{ij}=H_{ij}+\overline{m_i}c_j+
                   \overline{c_i}m_j+\overline{c_i}c_j.
\]

All centered covariance entries are unchanged. The diagnostic proves
the pointwise product expansion in `gramProduct_add_const` and the
whole-window covariance identity in `covarianceEntry_add_const`.
The numerical code checks the Gram update and independently recomputes
every covariance entry from its physical column. The largest observed
entry change is below `3.3e-19`.

Each sample fits the raw and centered matrices independently, using
unconstrained affine least squares, equal weights, and the combined
divisor-cost clipping rule. It also transfers each fitted coefficient
vector between both carriers without refitting. At
`s=3/4+14.134725…i`, which is **not a zero**, the results are:

| `u` | Raw fitted RMS | Same coefficients, centered RMS | Centered refit after divisor-budget clipping |
| ---: | ---: | ---: | ---: |
| 4 | `0.031118` | `0.990411` | `0.936122` |
| 8 | `0.003808` | `0.999670` | `0.994711` |
| 16 | `0.001295` | `1.000016` | `0.999070` |
| 32 | `0.000235` | `1.0000003` | `0.999947` |

The large apparent improvement in the raw fit uses the finite inverse
shift. Refitting the centered carrier keeps a small finite RMS gap, but
that tested gap shrinks. At critical-line zeros the raw and centered
tests agree, as their exact identity requires. None of these observations
proves or refutes an estimate restricted to right-half zeros.

The main run records 16 cases, 96 fitted mixtures, and all 96 coefficient
transfers in `/tmp/eta-centered-cutoffs.json`. Twelve independent cases
at `u=2,3,4` use literal divisor selections, 40-digit complex powers,
every physical prefix, and both full Gram/covariance matrices. They
check the inverse polynomials, affine normal equations, combined divisor
masses, clipping budgets, and transferred fits. All pass; records are
in `/tmp/eta-centered-cutoffs-direct-checks.json`.

The local Lean audit passes warning-as-error compilation and all 14
linters on 14 declarations plus 14 automatically generated ones. Its
six terminal axiom checks use only the three permitted standard axioms;
the log is `/tmp/eta-centered-cutoffs-audit.log`. No root theorem,
dashboard milestone, or zero bound is added.

The inverse-defect signal is therefore not a reason to enlarge this
same numerical scan. A future signed bound must use additional
arithmetic information from the actual zero constraint. The full
arithmetic decay theorem and RH remain open.

### Checked positive gamma physical averaging

The numerical lead following [DLMF 25.12.11](https://dlmf.nist.gov/25.12.E11)
now has a Lean proof for the actual eta series and the original completed
Möbius carrier. The proof does not assume a polylogarithm identity: it
identifies the Mellin integral from the convergent paired eta prefixes
using dominated convergence. The four root modules are
[`EtaGammaKernel`](../RiemannGaussian/EtaGammaKernel.lean),
[`EtaGammaMellin`](../RiemannGaussian/EtaGammaMellin.lean),
[`EtaGammaDampedMoebius`](../RiemannGaussian/EtaGammaDampedMoebius.lean), and
[`EtaGammaPhysicalAverage`](../RiemannGaussian/EtaGammaPhysicalAverage.lean).
The declarations share namespace `RiemannGaussian.EtaGammaSmoothing`.

Put `f(t)=1/(1+exp(t))`. The theorem `abs_fermiThree_le` proves the
sharper derivative envelope `abs(f'''(t)) <= exp(-t)` on the entire real
line. For the exact transform

\[
 H(t,x)=f(t+x)-xf'(t+x)+\frac{x^2}{2}f''(t+x),
\]

`hasDerivAt_gammaTransform` gives
`dH/dx = x^2*f'''(t+x)/2`. The full signed difference is its derivative
integral. Consequently `abs_gammaTransform_sub_le` proves

\[
 |H(t,x)-f(t)|\le\frac{x^3}{6}e^{-t},\qquad x\ge0.
\]

The complex Mellin integral is absolutely integrable for every
`Re(s)>0`. Its phase is retained before the derivative envelope is
integrated. The theorem `integral_mellinFermi_eq_gamma_eta` identifies
it with `Gamma(s)*pairedEtaCore(s)`. The transformed integral is exactly
that actual eta value plus a remainder bounded by
`Gamma(Re(s))*x^3/(6*norm(Gamma(s)))`.

Define `Q(x)=exp(-x)*(1+x+x^2/2)`. The literal absolutely convergent
series

\[
 G_s(x)=\sum_{q\ge1}(-1)^{q+1}q^{-s}Q(qx),\qquad x>0,
\]

is the same Mellin transform by `hasSum_gammaDampedEta`. At an actual
nontrivial zero, `norm_gammaDampedEta_at_zero_le` proves

\[
 \|G_\rho(x)\|\le
 \frac{\Gamma(\sigma)}{6\|\Gamma(\rho)\|}x^3,
 \qquad \sigma=\Re\rho.
\]

#### Connection to the original physical carrier

The discrete physical weights are

\[
 \omega_A(M)=Q(M/A)-Q((M+1)/A),\qquad M\ge0.
\]

Lean proves they are nonnegative, summable, and have total mass one.
`gammaPhysicalWeight_eq_integral` identifies each weight with the
integral of `t^2*exp(-t)/2` over its scaled physical interval. Thus the
whole continuous physical half-line is represented, including the
interval below the first integer. That interval has an empty eta prefix.

Discrete Abel summation identifies the eta series with the weighted
literal unpaired prefixes. The infinite boundary is discharged using
the checked uniform prefix bound and exponential survival summability.
Every complete quotient fibre is then summed exactly. The theorem
`hasSum_gammaPhysicalWeight_moebiusTerm` gives

\[
 \sum_{M\ge0}\omega_A(M)T_\rho(M,d)
  =\mu(d)d^{-\rho}\chi(\rho)G_\rho(d/A),\qquad d\ge1.
\]

No interchange is justified by an unproved cancellation assumption:
the relevant complex sequences are absolutely summable. The theorem
`hasSum_gammaPhysicalWeight_moebiusSelected` sums this identity over
any finite positive divisor selection.

#### A stronger proved low-family allowance

Let

\[
 C_\rho=\|\chi(\rho)\|
       \frac{\Gamma(\sigma)}{6\|\Gamma(\rho)\|}>0.
\]

For every `S` contained in the positive integers through `D`, the theorem
`norm_tsum_gammaPhysicalWeight_moebiusSelected_le` proves

\[
 \left\|\sum_{M\ge0}\omega_A(M)
             \sum_{d\in S}T_\rho(M,d)\right\|
 \le C_\rho A^{-3}D^{4-\sigma},\qquad A>0.
\]

The full complex selected carrier is retained before applying a norm.
The sixth/fifth-power schedule `A=u^6`, `D=u^5` has allowance
`C_rho*u^(2-5*sigma)`. The terminal theorem
`tsum_gammaPhysicalWeight_moebiusSelected_sixth_tendsto_zero`
proves the **original selected low average** tends to zero for
`sigma>2/5`, with arbitrary scale-dependent selections.

This includes critical-line zeros. It improves the controlled divisor
range for this new kernel, but cannot itself rule out a zero anywhere.
It is not a stronger estimate for the old finite-window sampler, a
mean-square theorem, or a uniform estimate in zero height.

#### Exact source endpoints and the remaining high carrier

The theorem `hasSum_gammaPhysicalWeight_moebiusSource` proves that the
complete original Möbius average has source

\[
 S_{\rho,A}=\chi(\rho)
        \bigl[Q(1/A)-2\,2^{-\rho}Q(2/A)\bigr].
\]

The `M=1` prefix is handled explicitly. It is incorrect to replace this
source by `S_rho` at a finite scale. The theorem
`norm_gammaMoebiusSource_sub_le` proves

\[
 \|S_{\rho,A}-S_\rho\|
 \le \frac{\|\chi(\rho)\|(1+16\,2^{-\sigma})}{6A^3}.
\]

Finally, `hasSum_gammaPhysicalWeight_moebiusLarge` retains the actual
whole high-divisor carrier:

\[
 \sum_{M\ge0}\omega_A(M)\operatorname{High}_\rho(M,D)
 =S_{\rho,A}-\sum_{M\ge0}\omega_A(M)
                \operatorname{Low}_\rho(M,D).
\]

This identity also handles physical cutoffs below `D`: out-of-range
divisor terms have empty prefixes and are zero. No clipped endpoint is
silently omitted.

The remaining obligation is an **independent upper bound for this full
signed high average below the nonzero source at a hypothetical
right-half zero**. The new low decay and source correction do not
supply that upper bound. The goal of full arithmetic decay and RH
remains open, and this slice establishes no new zeta zero bound.

The earlier numerical seed compared polylogarithms, the damped series,
and physical prefixes in 12 cases at `x=1/4,1/8,1/16`, with 45-digit
arithmetic and agreement within `1e-37`; its record is
`/tmp/eta-gamma-seed.json`. The mathematics above is checked in Lean
independently of that numerical evidence.

The slice passes direct warning-as-error checks for all four modules,
the focused build (4,387 jobs), and the full build (9,715 jobs). The
whole-project audit reports zero findings across 12,356 declarations
plus 5,980 automatically generated declarations, using all 14 linters.
All 21 terminal axiom checks use only `propext`, `Classical.choice`,
and `Quot.sound`. The generated inventory contains 868 modules,
18,357 compiled declarations and 15,773 theorems, with zero project
axioms, placeholder-dependent declarations, or nonstandard theorem
axioms; `rhImplied` remains false. Regeneration is byte-identical.
These are local verification results; remote verification is recorded by
the GitHub Actions run for the exact committed SHA. Logs are `/tmp/eta-gamma-focused-build.log`,
`/tmp/eta-gamma-full-build.log`, `/tmp/eta-gamma-root-audit.log`,
`/tmp/eta-gamma-project-lint.log`, and `/tmp/eta-gamma-status.log`.


### The logarithmic mode survives gamma smoothing

The local audit `/tmp/EtaGammaLogModeAudit.lean` now checks the complete
logarithmic moment of the cubic gamma kernel. This tests whether the
stronger low-family cancellation also provides a way to shrink the
kernel norm independently of the actual Möbius signs.

For every positive integer `q`, define

\[
 L_q(x)=\frac{Q(qx)-Q((q+1)x)}{x}.
\]

The theorem `integrableOn_logarithmicCell` proves absolute integrability
on the entire positive axis. Near zero the cubic survival correction
removes the apparent singularity; at infinity the actual survival
function is an integrable dominator. Applying Mathlib's Frullani integral,
`integral_logarithmicCell` proves

\[
 \int_0^\infty L_q(x)\,dx=\log\frac{q+1}{q}.
\]

The actual eta prefix decay gives an absolutely summable integral budget
`sum_q log((q+1)/q)*norm(F_rho(q))`. The theorem
`summable_integral_norm_gammaLogTerm` discharges this condition before
any quotient sum and logarithmic integral are interchanged. The finite
Abel identity and the already checked eta derivative series then give

\[
 \boxed{\displaystyle
 \int_0^\infty G_\rho(x)\,\frac{dx}{x}=\eta'(\rho).}
\]

This is `integral_gammaDampedEta_div_eq_deriv`. It is an identity for the
whole literal damped eta series, with no assertion about a Möbius prefix
asymptotic. At a simple actual zero, `eta'(rho)=a(rho)*zeta'(rho)`, and
`normalized_gammaLogMoment_eq_source` gives

\[
 \frac{\chi(\rho)}{\zeta'(\rho)}
       \int_0^\infty G_\rho(x)\,\frac{dx}{x}=S_\rho\ne0.
\]

The nonzero zeta derivative is an explicit hypothesis of this comparison
statement. No simplicity assumption is added to the original Möbius
source identity or to the root gamma low-family bound.

#### Normalized scale mixtures retain the same moment

The theorem `integral_gammaDampedEta_dilation_div` proves invariance under
every positive scale `c`. For any finite complex weights with
`sum_i w_i=1` and positive scales `c_i`, the theorem
`integral_gammaDilation_mixture` gives

\[
 \int_0^\infty\sum_i w_iG_\rho(c_i x)\,\frac{dx}{x}=\eta'(\rho)
\]

when the eta derivative is nonzero. Integrability of every dilated kernel
and every finite mixture is discharged in the proof. The terminal theorem
`norm_source_le_normalized_gammaDilation_mixture` consequently proves

\[
 \|S_\rho\|\le
 \int_0^\infty\left|
   \frac{\chi(\rho)}{\zeta'(\rho)}
       \sum_i w_iG_\rho(c_i x)\right|\frac{dx}{x}
\]

at a simple actual zero. The weights can be complex and can cancel;
normalization still preserves the moment. Thus fitting these scales
cannot drive this logarithmic comparison norm to zero or below the
source norm. This does **not** prohibit an estimate using additional
arithmetic properties of the actual Möbius coefficients.

#### Numerical check across smoothing orders

The [probe](../scripts/probe_eta_gamma_log_mode.py) checks gamma orders
`1,2,3,4,6` at the first three numerical critical-line zeros and at
`3/4+it` with the same ordinates. Away from zeros it explicitly uses
`G_s,k(x)-eta(s)*Q_k(x)`; this centering is not treated as a zero equation.
The logarithmic integral is computed by an integrated Taylor expansion
on `(0,1)` and an independent incomplete-gamma series on `(1,infinity)`.
Each is also checked with 30 fewer terms. All 30 full moments agree with
the independently evaluated eta derivative: the largest observed error
is below `2.8e-77`, and the largest truncation-comparison difference is
below `6.8e-69`, using 80-digit arithmetic. These are numerical checks,
not certified remainder bounds. The Lean theorem above concerns the
cubic gamma kernel and its positive dilations; it does not assert the
whole arbitrary-order generalization.

At the first numerical zero, the complex contributions divided by the
eta derivative illustrate where the comparison mode goes:

| Gamma order | Integral on `(0,1)` | Integral on `(1,infinity)` |
| ---: | ---: | ---: |
| 1 | `0.871170 - 0.001290i` | `0.128830 + 0.001290i` |
| 3 | `0.425492 + 0.010553i` | `0.574508 - 0.010553i` |
| 6 | `0.069735 + 0.020198i` | `0.930265 - 0.020198i` |

Their sum remains one. Increasing the smoothing order shifts this
comparison contribution into larger `x`, rather than supplying a smaller
whole moment. These entries do not estimate the actual Möbius carrier.
Full records are in `/tmp/eta-gamma-log-mode-repo.json`.

#### Scope of the external cancellation estimate reviewed

[Maier–Rassias, Theorem 2.1](https://arxiv.org/pdf/1806.05070) bounds a
Möbius sum against a periodic Estermann/continued-fraction function
`g(n/k)` over `k^D <= n < 2*k^D`, with `D>=2`, saving a fixed power of
`k`. Its weight, frequency scale, and summation range differ from the
present smooth kernel `G_rho(d/A)`. Transferring that result would require
a new identity and estimates that retain the remaining terms; no such
transfer has been proved. The paper's auxiliary saving is therefore not
used as an upper bound for this carrier. This is a scope audit, not an
impossibility claim about all uses of its methods.

The local diagnostic passes warnings as errors, all 14 declaration
linters on 39 declarations plus 31 automatically generated declarations,
and 11 terminal axiom checks using only the three permitted standard
axioms. Its log is `/tmp/eta-gamma-log-mode-audit.log`. The root theorem
inventory and its generated artifacts are unchanged by this diagnostic.
The next arithmetic estimate must retain the actual signed high Möbius
family; the kernel norm alone does not remove its comparison source
mode. Full arithmetic decay, a new zero bound, and RH remain unproved.

### Finite localization with a paid infinite arithmetic tail

The next two root modules are
[`EtaGammaDivisorTail`](../RiemannGaussian/EtaGammaDivisorTail.lean) and
[`EtaGammaFiniteBand`](../RiemannGaussian/EtaGammaFiniteBand.lean).
The original divisor series, rather than a comparison sequence, now has
an absolutely convergent sum and a quantitative finite localization.

The bounds `gammaSurvival_le_exp_half` and
`norm_gammaDampedEta_le_exp_half` prove
`Q(x)<=4*exp(-x/2)` for `x>=0` and `norm(G_s(x))<=8*exp(-x/2)` for
`x>=2`, `Re(s)>0`. The actual geometric majorant gives
`summable_norm_gammaMoebiusTerm` and

\[
 \left\|\sum_{d>R}\mu(d)d^{-\rho}\chi(\rho)G_\rho(d/A)\right\|
 \le 16\|\chi(\rho)\| A R^{-\sigma}e^{-R/(2A)},\qquad R\ge2A.
\]

The terminal theorem for this estimate is
`norm_tsum_gammaMoebiusTerm_tail_le`. The theorem
`hasSum_gammaMoebiusTerm` identifies the entire sum with `S_(rho,A)`.
Its proof first takes the increasing finite divisor selection through
the original physical average, using a summable bound proportional to
`M*exp(-M/(2*A))` independent of that selection. Thus neither the sum
identity nor the interchange assumes the missing arithmetic estimate.

Let `R(A)=ceil(2*A*(1+2*log A))`. For `A>=1`, the compiled terminal
theorem `norm_gammaPhysicalHigh_sub_logBand_le` proves

\[
 \left\|\sum_{M\ge0}\omega_A(M)\operatorname{High}_\rho(M,D)
   -\sum_{D<d\le R(A)}\mu(d)d^{-\rho}\chi(\rho)G_\rho(d/A)\right\|
 \le\frac{16\|\chi(\rho)\|}{A},\qquad D\le R(A).
\]

The exact difference is retained by
`gammaPhysicalHigh_sub_band_eq_tail`. The sharper logarithmic-cutoff
tail theorem also retains the factor `R(A)^(-sigma)`.

For the full finite band `B_rho(u)` on `A=u^6`, `D=u^5`, the theorem
`norm_gammaMoebiusSixthBand_sub_source_le` pays all three costs:

\[
 \|B_\rho(u)-S_\rho\|\le E_\rho(u)
 := C_\rho u^{2-5\sigma}
   +\frac{16\|\chi(\rho)\|}{u^6}
   +\frac{\|\chi(\rho)\|(1+16\,2^{-\sigma})}{6(u^6)^3}.
\]

The source limit `gammaMoebiusSixthBand_tendsto_source` holds for
`sigma>2/5`. It includes actual critical-line zeros and establishes no
independent upper bound below the source at a right-half zero.

#### Acceptance condition for the direct finite-band attack

Retain the real projection `P_rho(u)=Re(conj(S_rho)*B_rho(u))` rather
than requiring a bound on every component of the band. The proved norm
comparison implies

\[
 P_\rho(u)\ge\|S_\rho\|^2-\|S_\rho\|E_\rho(u).
\]

An independent upper estimate `P_rho(u)<=U_rho(u)` closes the reductio
if `U_rho(u)+norm(S_rho)*E_rho(u)<norm(S_rho)^2` at one admissible
scale for the hypothetical zero. A fixed strict saving along an
unbounded admissible sequence is sufficient as well. These are acceptance
conditions derived from the checked comparison, not new assumptions
discharged by the current proof chain. A full decay rate is unnecessary.
The estimate must distinguish `sigma>1/2` from the critical line.

The minimal finite test can also use a shrinking saving. With
`q_rho(u)=Re(B_rho(u)/S_rho)` and `e_rho(u)=E_rho(u)/norm(S_rho)`,
it is enough to prove independently `q_rho(u)<=1-delta_rho(u)` and
`delta_rho(u)>e_rho(u)` at the same admissible scale. For an asymptotic
attack without an explicit cutoff, a sufficient target is some
`delta_rho>0` and arbitrarily large scales with
`q_rho(u)<=1-delta_rho`. The existing vanishing allowance then supplies
the final contradiction. No statement that this independent target is
proved or known to be easier to establish than RH is intended.

#### Numerical checks of the entire arithmetic band

The [probe](../scripts/probe_eta_gamma_high.py) checks `u=2,3,4,6` at
the first two numerical critical-line zeros and at `3/4+it` with the
same ordinates. It keeps every Möbius sign, all factor-count channels,
and the divisor tail. Independent integer product coefficients reproduce
the complete high average. The largest source-split discrepancy among
the 16 cases is below `3e-14`; the largest product-reconstruction
discrepancy is below `1.8e-14`. These are floating-point comparisons.

At the first numerical zero, the source-normalized complex finite band is:

| `u` | Full finite band divided by source | Sum of norms of all factor-count channels |
| ---: | ---: | ---: |
| 2 | `0.868447 + 0.056539i` | `0.907821` |
| 3 | `0.927537 - 0.024214i` | `0.950256` |
| 4 | `0.971735 - 0.003547i` | `0.976484` |
| 6 | `0.990940 - 0.004169i` | `0.995171` |

The factor-count channels cover one, two, three, and at least four
distinct prime factors. The small difference between the final channel
norm sum and the full norm says nothing about cancellation inside a
channel. The approach to one is consistent with the proved source limit
on the critical line. The off-critical samples are nonzeros, so their
small raw values do not establish the required estimate under a zero
hypothesis. These are complex first means, not physical mean squares.

Four independent 40-digit checks at `u=2` construct every finite physical
prefix using SymPy divisors and Möbius values, and evaluate every band
kernel by the direct polylogarithm formula. They retain the last finite
Abel boundary. The largest band discrepancy is below `3e-15`, the
source discrepancy below `8.2e-35`, and the finite physical Abel
discrepancy below `6.9e-40`. These checks do not certify interval bounds.
Records are `/tmp/eta-gamma-high.json` and
`/tmp/eta-gamma-high-direct-checks.json`; the independent checker is
`/tmp/check_eta_gamma_high.py`.

Both new root modules pass direct warnings-as-errors elaboration. The
focused and full builds pass, the latter with 9,717 jobs. The root audit
checks 12,385 declarations plus 6,000 automatically generated declarations
with all 14 linters finding no errors; all 17 terminal axiom checks use
only the three permitted standard axioms. The whole-project declaration
linter also passes. This is local verification. The latest remotely
verified commit remains `d0d07f3200fedc964fdfb56d564bce0918c3e69e`, CI
34200679878. The user has put further commits on hold pending concrete
progress on the independent upper-bound goal.

#### Direct attack through the complete prime-error/cofactor pairing

The local Lean audit `/tmp/EtaGammaPrimeErrorAudit.lean` proves the
exact identity

\[
 \mu(n)\log n
   =-\sum_{qm=n}\bigl(\Lambda(q)-1\bigr)\mu(m),\qquad n>1.
\]

The constant-density part cancels because the full Möbius divisor sum
is zero at every nonunit product. All prime powers in `Lambda`, every
composite contribution from `-1`, and the `q=1` cofactor are retained.
This is classical Möbius inversion used as an exact transport, not a
claim of new cancellation or novel number theory.

`gammaMoebiusSelected_eq_prime_error` applies it to the actual completed
gamma band. `weighted_moebius_eq_cofactor_prime_error` transposes all
product fibres into complete quotient intervals. With

\[
 K_{\rho,A}(n)=
 \frac{n^{-\rho}\chi(\rho)G_\rho(n/A)}{\log n},
\]

the resulting band is exactly

\[
 B_\rho(A,D)=
 -\sum_{1\le m\le R(A)}\mu(m)
    \sum_{D/m<q\le R(A)/m}
       (\Lambda(q)-1)K_{\rho,A}(qm),
\]

where the two divided endpoints are integer floors. The logarithm is
never divided by zero: every retained product exceeds `D>=1`.

This suggests applying finite Abel summation to each complete `q`
interval using the signed prefix `psi(q)-q`, then retaining the sum over
`m` and every boundary before projecting along the source. The new task
is an estimate for that **whole signed pairing**. The Gaussian prime
Abel and weighted Chebyshev modules provide possible test-kernel tools,
but their existing estimates concern their stated kernels. Transport to
this cofactor-dependent kernel, including the full coefficient cost,
would need proof. A generic norm estimate or prime-density substitution
does not supply a strict source gap.

The local numerical probe `/tmp/probe_eta_gamma_prime_error.py` checks
six complete bands (`u=2,3,4`, first two numerical zeros), including every
cofactor Abel row, its two endpoints, and every finite difference. The
constant-density sum vanishes to floating-point precision, and the
largest whole reconstruction discrepancy is below `5.7e-15`. The
literal termwise absolute Abel budgets at `u=3,4` are:

| `u` | First-zero budget divided by source norm | Second-zero budget divided by source norm |
| ---: | ---: | ---: |
| 3 | `14.579862` | `22.199771` |
| 4 | `28.084685` | `43.256882` |

These are computed absolute majorants, not interval certificates. They
show why this tested termwise comparison cannot close the source gap.
The signed sum still approaches the source, consistently with the
critical-line theorem. No independent right-half estimate is inferred
from these samples. All records, including dyadic cofactor and prime-index
shells, are in `/tmp/eta-gamma-prime-error.json`.

The exact-identity audit passes warnings as errors, all 14 linters on
8 declarations plus 10 automatically generated declarations, and three
terminal axiom checks containing only the permitted standard axioms.
Its log is `/tmp/eta-gamma-prime-error-audit.log`. It remains a local
route diagnostic and adds no dashboard milestone. The independent
finite-band upper bound remains unproved.

#### Auditing the Gaussian/Suzuki transfer and the full quadratic alternative

The Suzuki envelope is not an unweighted square-root estimate for
`psi(x)-x`. In
[`RiemannXiSuzukiPointwiseChebyshevCumulativeEnvelope`](../RiemannGaussian/RiemannXiSuzukiPointwiseChebyshevCumulativeEnvelope.lean),
the input `abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le`
is the linear bound `abs(psi(x)-x)<=5*x`. The later square-root envelopes
include inverse powers of the endpoint in their kernels. Those powers
must be paid for when transporting an estimate to the prime-error pairing
above. No direct square-root cancellation theorem is obtained by that
substitution.

The next numerical test uses the full quadratic identity already audited
in `/tmp/EtaQuadraticMobiusAudit.lean`, now on the actual gamma band.
For `U=ceil(sqrt(R))<=D`, define the source-normalized weight
`F(n)=n^(-rho)*chi(rho)*G_rho(n/A)/S_rho` and the symmetric complex matrix

\[
 K_{a,b}=-\sum_{D<kab\le R}F(kab),\qquad 1\le a,b\le U.
\]

The classical finite coefficient identity gives
`B_rho/S_rho=mu^T K mu`, with every entry retained. Its continuous
comparison has rank one:

\[
 K^{\mathrm{cont}}_{a,b}=-\frac{I}{ab},\qquad
 I=\int_D^R F(x)\,dx,
 \qquad
 \mu^T K^{\mathrm{cont}}\mu
   =-I\left(\sum_{a\le U}\frac{\mu(a)}a\right)^2.
\]

The squared harmonic sum is nonnegative, so a favorable phase of `I`
can make this main term's real projection nonpositive. This does not
control the remainder. The local probe
`/tmp/probe_eta_gamma_quadratic.py` checks all finite integer
coefficients before evaluating the complete complex matrix. In the 12
cases (`u=3,4,6`, first two ordinates, `sigma=1/2,3/4`), the continuous
main term's norm is below `7.4e-6` after source normalization. Most of the
critical-line source is already in the arithmetic remainder. The general
matrix estimate is too large even when the main term has the favorable
sign.

Let `H=Re(K-K_cont)` and let `H_+` denote its positive spectral part.
The real projection has the finite upper comparison

\[
 \Re(B_\rho/S_\rho)
 \le \Re(-I H_\mu(U)^2)+\mu^T H_+\mu.
\]

This retains the actual Möbius vector in every spectral coordinate. It
is more selective than `lambda_max(H)*norm(mu)^2`, but its arithmetic
size still needs proof. The gamma-matrix comparison is a local analytic
and numerical candidate; no new root upper-bound theorem is claimed.

At `u=6`, the full numerical results are:

| Sample | General matrix upper comparison | Upper comparison using the actual positive spectral energy |
| --- | ---: | ---: |
| First critical-line zero | `127.519035` | `1.164513` |
| `3/4` at the first ordinate | `10.358730` | `0.123428` |
| Second critical-line zero | `219.420559` | `1.346888` |
| `3/4` at the second ordinate | `18.404076` | `0.154798` |

The figures are rounded source-normalized upper comparisons; all
unrounded data are retained.
The off-critical points are nonzeros. Furthermore, evaluating the
**proved** zero-specific error formula at these parameters gives about
`3.73e6` at the first off-critical sample and `1.96e11` at the second.
Thus none of these small raw spectral values passes the complete source
gap test. The cubic Mellin constant's dependence on the ordinate is
included, not discarded.

The positive spectral trace is much smaller than the general matrix
budget in these samples. A bound for `mu^T H_+ mu` by a scale-independent
multiple of that trace, together with a decaying trace estimate, remains
an optional diagnostic route. **Neither estimate has been proved, and
neither is required by the finite-band acceptance condition.** A trace
estimate alone would not bound the actual vector's energy. Further work
must retain the negative spectral contribution whenever it helps the
signed source projection. Growth in an auxiliary comparison constant
is acceptable if the complete resulting bound still passes that test.

The largest whole matrix reconstruction discrepancy in the 12 cases is
below `2.5e-12`. Four independent 40-digit checks at `u=3` verify 16
selected complete matrix entries using polylogarithms and all four
continuous main terms using incomplete gamma integrals. Their largest
entry discrepancy is below `2.7e-17` and their largest continuous-main
discrepancy below `1.1e-19`. These are numerical consistency checks, not
interval certificates or arithmetic bounds. Records are
`/tmp/eta-gamma-quadratic.json` and
`/tmp/eta-gamma-quadratic-direct-checks.json`; the independent checker is
`/tmp/check_eta_gamma_quadratic.py`.

The regenerated root inventory contains 870 modules, 18,406 compiled
declarations, and 15,820 project theorems. It reports zero project axioms,
zero placeholder-dependent declarations, no nonstandard theorem axioms,
and `rhImplied=false`. Regeneration is byte-identical on repetition.
No commit or push has been made. The independent finite-band upper
bound and RH remain open.

#### Audit of the family and the strength of its proposed estimates

The user's question about choosing an unnecessarily hard family changes
the priority of the auxiliary estimates. There are two separate issues:
a prescribed coefficient law can demand additional mathematics, and a
bound used to analyze it can discard cancellation needed for the original
goal. Neither issue is resolved by making the finite computation larger.

There is an established warning for the earlier logarithmic choice.
[Wei and Wu, Proposition 1.9](https://bimsa.net/doc/publication/1424.pdf)
prove that the standard critical-line Nyman–Beurling mean-square error
for `V_N(s)=sum_(n<=N) mu(n)*(1-log(n)/log(N))*n^(-s)` tending to zero
implies both RH and simplicity of the zeros. Their Theorem 1.10 gives
an RH equivalence for convergence on every fixed line strictly to the
right of `1/2`. The distinction concerns the actual norm and domain,
not just the appearance of Möbius coefficients. The repo's balanced eta
correction and the present gamma band have not been identified with that
critical-line norm. No simplicity obstruction for either actual carrier
is established by citing this result.

For the current gamma route, keep the precise quantifiers: for each
hypothetical actual zero with `sigma>1/2`, find one admissible scale and
an independent upper bound satisfying
`U_rho(u)+norm(S_rho)*E_rho(u)<norm(S_rho)^2`. Constants and the scale
may depend on that zero. Its multiplicity is unrestricted. An estimate
on all complex parameters, all coefficient vectors, or every scale is
an additional proposal. No uniformity as `sigma` approaches `1/2`,
prescribed power rate, or bound on the positive spectral part alone is
required. Under RH there are no zeros in this quantified domain, so
the zero-conditional acceptance statement itself cannot demand a
separate simplicity assertion. This logical audit is not a new Lean
theorem or a proof of the independent arithmetic estimate.

For example, the symmetric matrix `diag(L,-L)` and vector `(1,-1)`
have signed quadratic value zero and positive spectral energy `L`
for every `L>=0`. This elementary comparison only illustrates the
information lost by deleting negative spectral contributions; it does
not assert that the actual gamma matrix has this form. Failure of a
positive-energy or constant-trace target is therefore not, by itself,
a rejection of the signed route.

The next estimates should address the complete signed projection and
be judged with all three proved allowances included. Keep full decay,
uniform trace comparison, and power savings optional. If a fixed kernel
or taper introduces an extra obstruction, vary it and re-establish its
source normalization and complete comparison costs. The original
[`EtaMoebiusTrialCoefficients.lean`](../RiemannGaussian/EtaMoebiusTrialCoefficients.lean)
already preserves arbitrary real arithmetic weights and proves complete
coefficient bounds when their absolute values are at most one; those
interfaces do not force the logarithmic law. They also do not establish
decay for an alternative family. The remaining independent inequality
still has RH-level consequences, and no argument here makes it known
to be tractable with the present arithmetic input.

#### Full smooth quadratic: exact remainder and cutoff audit

The root-imported
[EtaGammaSmoothQuadratic](../RiemannGaussian/EtaGammaSmoothQuadratic.lean)
removes the sharp divisor-band endpoints from the quadratic kernel.
Write `m_U=mu_(<=U)`, `l_U=mu_(>U)`, and let `*` denote Dirichlet
convolution. The coefficient identity is the classical formula

```
mu = 2*m_U - (1*m_U*m_U) + (1*l_U*l_U).
```

Here `1` denotes the arithmetic function that equals one at every
positive integer. Define the entire smooth quadratic and its omitted
contribution by

```
Q(rho,A,U) = -sum_(n>=1) (1*m_U*m_U)(n) n^(-rho) chi(rho) G_rho(n/A),
J(rho,A,U) =  sum_(n>=1) (1*l_U*l_U)(n) n^(-rho) chi(rho) G_rho(n/A).
```

The theorem `summable_norm_cofactor_gamma` proves absolute convergence
before using any source identity. The coefficient bound is at most
`n^2`, independent of `U`; the exponential envelope absorbs that entire
factor. The theorem `source_eq_short_add_quadratic_add_error` proves

```
S_(rho,A) = 2*Low(rho,A,U) + Q(rho,A,U) + J(rho,A,U).
```

Every coefficient of the omitted square through `U^2` vanishes.
The theorem `norm_smoothError_le` consequently bounds its entire
remaining series by

```
norm(J(rho,A,U)) <= 1024*norm(chi(rho))*A^3*exp(-U^2/(4*A)),
```

provided `A>0` and `2*A<=U^2`. This estimate assumes no Möbius
cancellation. It controls the additional cofactor tail, which was not
covered merely by the original single-divisor tail estimate.

On the explicit schedule `A=u^6`, `U=u^4`,
`norm_short_sixth_fourth_le` bounds each short copy by
`C_rho*u^(-2-4*sigma)`. The omitted-square allowance is
`1024*norm(chi(rho))*u^18*exp(-u^2/4)` and tends to zero by
`smoothError_sixth_tendsto_zero`. The source endpoints retain their
existing cubic allowance. Thus `smoothQuadratic_sixth_tendsto_source`
proves `Q(rho,u^6,u^4)->S_rho` at every actual nontrivial zero.
This does not establish a strict signed saving. It justifies using a
full smooth quadratic as an alternative carrier for the same
contradiction, without a discontinuous product-band kernel or an
uncontrolled infinite cofactor tail.

The local audit passes warnings-as-errors elaboration, all 14 linters
on 29 declarations plus 14 generated declarations, and four terminal
axiom checks using only `propext`, `Classical.choice`, and `Quot.sound`.
Its initial log is `/tmp/eta-gamma-smooth-quadratic-audit.log`. The proof
is now in the root-imported
[EtaGammaSmoothQuadratic](../RiemannGaussian/EtaGammaSmoothQuadratic.lean),
under namespace `RiemannGaussian.EtaGammaQuadratic`. The independent
signed arithmetic estimate remains unproved.

The numerical audit `/tmp/probe_eta_gamma_smooth_quadratic.py` retains
all integer cofactor coefficients, both short linear contributions,
the omitted square, and every signed spectral contribution. It checks
24 cases: `u=3,4,6`, the first two ordinates, real parts `1/2,3/4`,
and both the original kernel and `G_s(x)-eta(s)*Q_survival(x)`.
For these numerical tests `U=floor(sqrt(R(A)))+1`, rather than the
fourth-power schedule used in the limit theorem. The exact identity
and tail bound apply to both choices.

The centered kernel agrees with the original only at an actual eta
zero. At a nonzero its full source includes the additional term
`-eta(s)*sum_(n>=1) mu(n)*n^(-s)*Q_survival(n/A)` (before completion).
This term is retained in every reconstruction; the small values of
the centered off-critical samples are not zero exclusions.

At `u=6`, the original smooth quadratic divided by `S_rho` has real
part `0.999785` at the first numerical critical-line zero and `0.999661`
at the second. The respective positive spectral contributions are
`1.159355` and `1.297832`, while the negative contributions are
`-0.159571` and `-0.298171`; the continuous main is also retained.
The source persists when the sharp lower cutoff is removed. Therefore
cutoff removal alone supplies no evidence of a strict saving, and the
negative contributions remain necessary data for further estimates.

The maximum complete reconstruction discrepancy is below `2e-13`.
An independent 40-digit check evaluates 16 complete matrix entries in
both kernel variants using the divisor coefficient
`tau(j)-2*1_(2|j)*tau(j/2)`, rather than the nested eta series. The
largest entry discrepancy is below `1.7e-15`. These are numerical
consistency checks, with finite exponential shadows, not interval
certificates or bounds for hypothetical off-critical zeros. Records
are `/tmp/eta-gamma-smooth-quadratic.json` and
`/tmp/eta-gamma-smooth-quadratic-direct-checks.json`; the independent
checker is `/tmp/check_eta_gamma_smooth_quadratic.py`.

[Huxley and Watt](https://arxiv.org/pdf/1807.05890), Section 1, give
classical truncated Möbius identities with independently chosen factor
cutoffs, including their quadratic matrix form. Their subsequent
spectral estimates concern their real unweighted matrix and do not
provide an estimate for this complex gamma kernel or its actual Möbius
projection. The classical identity is useful here as exact bookkeeping;
its signed arithmetic estimate is still an additional obligation.

#### Unequal factor cutoffs and the retained outer signed sum

The subsequent local probe `/tmp/probe_eta_gamma_rectangular.py`
tests the classical mixed version
`mu=m_L+m_V-(1*m_L*m_V)+(1*l_L*l_V)` with the same full smooth,
zero-centered kernel. Its 36 cases use `u=3,4,6`, both ordinates and
real parts above, and the three factor ranges `(u^2,u^5)`, `(u^3,u^5)`,
and `(u^4,u^4)`. Every integer coefficient of the omitted convolution
through `L*V` is checked to be zero, and both short sums and the complete
finite shadow of the omitted convolution are retained. Their maximum
source/product reconstruction discrepancy is below `2e-13`.

Let `K` be the source-normalized real matrix and retain the actual
right Möbius vector first: `c_a=sum_b K_(a,b)*mu(b)`. The remaining
signed quantity is `sum_a mu(a)*c_a`. The probe compares it with
the sum of `abs(c_a)` over the actual nonzero Möbius coordinates,
and also with both Cauchy comparisons obtained by folding either
actual vector first. These comparisons are optional diagnostics;
the full outer signed sum is still available and remains the target.

For `u=6`, `L=216`, `V=7776`, the results are:

| Sample | Actual real bilinear projection | Best tested outer comparison |
| --- | ---: | ---: |
| First critical-line zero | `0.990939` | `1.046121` |
| `3/4` at the first ordinate | `0.048694` | `0.050679` |
| Second critical-line zero | `1.007405` | `1.254928` |
| `3/4` at the second ordinate | `0.047603` | `0.055487` |

This geometry reduces the tested comparison relative to the balanced
cutoffs; it is evidence to retain the completed inner Möbius sum before
estimating the outer expression. It is not an independent bound. The
off-critical samples are nonzeros, their centered source correction is
retained, and none supplies a full acceptance certificate. The more
extreme `(u^2,u^5)` choice has a substantially larger omitted cofactor
cost in these samples, so its smaller outer comparison cannot be judged
in isolation. The mixed-cutoff transport is now proved in
[EtaGammaRectangular](../RiemannGaussian/EtaGammaRectangular.lean),
as detailed below. Records are `/tmp/eta-gamma-rectangular.json`.

#### Complete inner cancellation and the surviving short rectangle

The root-imported `EtaGammaRectangular` works with actual short Möbius
factors `m_L,m_V`, their complements `l_L,l_V`, and the literal outer
interval `f_(W,L)(a)=mu(a)*1_(W<a<=L)`. The theorem
`mixedCofactor_short_eq_sub_long` proves the exact identity

```
1*f*m_V = f - 1*f*l_V.
```

Here `*` is Dirichlet convolution and `1` is the arithmetic function
equal to one on positive integers. This uses the classical inverse
identity `1*mu=delta`, with no cancellation estimate assumed. After
gamma evaluation, `foldedOuterBand_eq_low_add_error` gives

```
B_(W,L,V) = -Low_((W,L]) + Eval(1*f_(W,L)*l_V).
```

The complementary cofactor vanishes through `W*V`. The proved absolute
convergence and `norm_evaluate_mixed_le` consequently control its whole
remaining series. The theorem `norm_foldedOuterBand_le` establishes

```
norm(B_(W,L,V)) <= C_rho*A^(-3)*L^(4-sigma)
                  +1024*norm(chi(rho))*A^3*exp(-W*V/(4*A)),
```

for `A>0` and `2*A<=W*V`. On `A=u^6`, `W=u^2`, `L=u^3`, `V=u^5`,
`norm_foldedOuterBand_sixth_le` reduces this allowance to

```
C_rho*u^(-6-3*sigma)+1024*norm(chi(rho))*u^18*exp(-u/4).
```

The terminal `foldedOuterBand_sixth_tendsto_zero` proves that the entire
outer strip vanishes at every actual nontrivial zero. This bound keeps
the completed inner Möbius sum before taking the norm. It does not use
the earlier Fourier sampler outside its range.

For the full rectangle `Q_(L,V)=-Eval(1*m_L*m_V)`, the theorem
`source_eq_shorts_add_rectangle_add_error` retains the exact source law

```
S_(rho,A)=Low_L+Low_V+Q_(L,V)+Eval(1*l_L*l_V).
```

All four series converge before they are combined. The theorem
`smoothRectangle_sub_eq_foldedOuterBand` also proves
`Q_(L,V)-Q_(W,V)=B_(W,L,V)` for `W<=L`, so the removed strip is exactly
the difference of the original signed rectangles. No matrix entries or
cross terms have been dropped.

For the surviving `Q_(u^2,u^5)`,
`norm_smoothRectangle_sixth_sub_source_le` proves source error at most

```
2*C_rho*u^(2-5*sigma)+1024*norm(chi(rho))*u^18*exp(-u/4)
```

relative to `S_(rho,u^6)`. The original cubic endpoint correction is
retained when passing to `S_rho`. Thus
`smoothRectangle_sixth_tendsto_source` proves convergence to the
original nonzero source for `sigma>2/5`, including the critical line.
The independent upper bound for the surviving short outer sum remains
unproved. This localization gives no new zero exclusion.

The initial local audit has 28 declarations plus 27 generated declarations,
passes all 14 linters, and has nine terminal axiom checks using only
`propext`, `Classical.choice`, and `Quot.sound`. Its log is
`/tmp/eta-gamma-rectangular-audit.log`. The root module uses namespace
`RiemannGaussian.EtaGammaRectangular`.

Both root modules pass direct warnings-as-errors elaboration, the focused
build (4391 jobs), and the full build (9719 jobs). The root audit passes
all 14 linters on 12442 declarations plus 6041 generated declarations;
all 13 terminal axiom checks use only the standard three axioms. The
project lint and source scans pass. The regenerated inventory records
872 modules, 18504 declarations, 15907 theorems, no project axioms,
no placeholder dependencies, and `rhImplied=false`; repeating generation
produces byte-identical JSON and SVG. The root audit log is
`/tmp/eta-gamma-rectangular-root-audit.log`. This slice remains local and
uncommitted under the user's hold; no new remote CI result is claimed.

#### Testing the remaining outer Abel estimate

The subsequent diagnostic `/tmp/probe_eta_gamma_outer_abel.py` computes
the completed inner coefficients independently as
`c_V(n)=sum_(b|n,b<=V) mu(b)`. It checks their exact vanishing on
`2<=n<=V`, and `c_V(n)=-mu(n)` on `V<n<=2*V`. It reconstructs each
outer row from these coefficients, independently of the earlier matrix
grouping. For `L=u^2`, the ordinary Abel transform retains the terminal
term `M(L)*Re(w_L)` and all terms `M(a)*(Re(w_a)-Re(w_(a+1)))`.
The complex-weighted version retains the actual prefix
`sum_(n<=a)mu(n)*n^(-s)` and the corresponding complex weight differences.

Both reconstructions and the complete dyadic outer-shell sum agree with
the prior full rectangle to within `2.1e-13` in 12 numerical cases:
`u=3,4,6`, the first two ordinates, and real parts `1/2,3/4`.
Every source correction and complementary cofactor from the earlier
probe remains recorded; off-critical points are nonzeros.

Taking absolute values after either Abel transform gives a larger upper
comparison than the completed-row absolute comparison in all 12 cases.
At `u=6`, the two critical-line samples give:

| Sample | Actual real projection | Completed-row comparison | Ordinary Abel comparison | Complex-weighted Abel comparison |
| --- | ---: | ---: | ---: | ---: |
| First zero | `0.990076` | `1.042974` | `2.814930` | `2.171799` |
| Second zero | `1.008330` | `1.250050` | `4.454489` | `2.774512` |

For example, the first ordinary Abel sum contains positive contribution
`1.902503` and negative contribution `-0.912427`; taking their absolute
values discards material cancellation. These observations do not rule
out an argument retaining those signs. They do not support replacing
the surviving signed target by either tested absolute Abel envelope.
The complete records are `/tmp/eta-gamma-outer-abel.json`; none is a
certified upper bound for a hypothetical off-critical zero.


#### Exact harmonic balancing of the surviving outer factor

The module [EtaGammaBalancedOuter](../RiemannGaussian/EtaGammaBalancedOuter.lean)
provides a mathematically specified coefficient choice on every positive
integer cutoff. Define

```
H_L = sum_(n<=L) mu(n)/n,
K_L = sum_(L<n<=2L) 1/n,
c_L = -H_L/K_L,
f_L(n) = mu(n)                 for 1<=n<=L,
         c_L                  for L<n<=2L,
         0                    otherwise.
```

Theorems `half_le_harmonicBlock` and `abs_balancingConstant_le_four`
prove `K_L>=1/2` and `|c_L|<=4`. The original prefix is unchanged,
including its zero Möbius coefficients. The added interval uses the
literal constant above, including at integers where Möbius is zero;
it is a different arithmetic factor, whose full correction is retained.
No sign-change conjecture or quantitative harmonic decay is needed.

The theorem `harmonic_balancedOuter_eq_zero` proves
`sum_(n<=2L) f_L(n)/n=0`. Consequently,
`reciprocalProduct_balancedOuter_eq_zero` kills the whole matrix term
`C/(a*b)` for every complex constant `C` and every other factor.
This is the reciprocal-product component isolated in the earlier
continuous-main calculation. The proof uses finite arithmetic and
does not assume a Voronoi expansion or a bound for its remainder.

Let `Q_bal=-Eval(1*f_L*m_V)`, where `Eval` is the original completed
gamma evaluation. The theorem `balancedRectangle_eq_original_sub`
retains its exact difference from the original rectangle. Completing
the inner sum in the added interval gives a finite low term and the
whole complementary cofactor above `L*V`; both are bounded before
passing to a limit. On `A=u^6`, `L=u^2`, `V=u^5`,
`norm_balancedRectangle_sixth_sub_original_le` proves

```
norm(Q_bal-Q_original) <= 32*C_rho/u^10
                        +4096*norm(chi(rho))*u^18*exp(-u/4).
```

The terminal `norm_balancedRectangle_sixth_sub_source_le` includes all
costs against the original source:

```
E_bal(rho,u) = 2*C_rho*u^(2-5*sigma) + 32*C_rho/u^10
              +5120*norm(chi(rho))*u^18*exp(-u/4)
              +norm(chi(rho))*(1+16*2^(-sigma))/(6*u^18).
```

The theorem `balancedRectangle_sixth_tendsto_source` proves the unchanged
source limit for `sigma>2/5`. No simplicity assumption is used. At a
hypothetical right-half zero, the acceptance condition remains an
independent bound on `Re(Q_bal/S_rho)` strictly below
`1-E_bal(rho,u)/norm(S_rho)` at an admissible scale. Neither the exact
zero harmonic moment nor the limit theorem supplies that bound.

The standalone [probe](../scripts/probe_eta_gamma_balanced_outer.py)
checks the harmonic moment using exact rational arithmetic. It also
checks the original integer cofactor support, reconstructs the complete
inner rows independently, and retains the added low term, complementary
cofactor, full source, and off-zero centering correction. Its 12 cases
use `u=3,4,6`, the first two ordinates, and real parts `1/2,3/4`.
The maximum reconstruction discrepancy is below `2.5e-14`.

At `u=6`, the first critical-line sample has balanced real projection
`0.99015949` and absolute-row comparison `1.04315787`; the second has
`1.00845022` and `1.25033372`. Each absolute-row comparison increases
slightly relative to the unchanged rectangle, as it includes the
additional interval. The centered off-critical samples are nonzeros.
Thus the coefficient rule removes one matrix component exactly, but
the tested absolute estimates do not close the signed arithmetic gap.
Records are `/tmp/eta-gamma-balanced-outer.json`. These diagnostics are
not interval certificates or new zero exclusions.

The root module passes direct warnings-as-errors elaboration, the focused
build (4428 jobs), and the full build (9720 jobs). All 14 root declaration
linters pass on 12468 declarations plus 6069 generated declarations;
the seven terminal axiom checks use only `propext`, `Classical.choice`,
and `Quot.sound`. Project lint, source scans, the standalone probe CLI,
and whitespace checks pass. The inventory contains 873 modules, 18558
declarations, and 15955 theorems, with no project axioms, placeholder
dependencies, or nonstandard theorem axioms; `rhImplied` remains false.
Repeated inventory generation is byte-identical. Logs are
`/tmp/eta-gamma-balanced-outer-root-audit.log` and the corresponding
`direct`, `focused`, `full`, and `status` logs. These gates passed while
commits were held; the user subsequently authorized the combined gamma
checkpoint for further research review.

#### Divisor-transform audit for the remaining signed part

The complete cofactor kernel has divisor coefficients
`tau(n)-2*1_(2|n)*tau(n/2)`. A transform must keep its full remainder and
handle the origin of the test function `y^(-s)*Q(x*y)`, which is singular
there. The infinite divisor-transform formulation reviewed in
[Banerjee, Dixit and Gupta](https://arxiv.org/pdf/2304.05923), Section 1,
uses Schwartz test functions. It cannot be substituted for this singular
test function without additional justification.

A pointwise square-root divisor-error bound by itself would still lose
too much when summed over both arithmetic factors. Even if it supplies
a kernel remainder of size `C_s*x^(sigma-1/2)`, termwise summation
would give a budget proportional to

```
A^(1/2-sigma) * (sum_(a<=2L) |f_L(a)|/sqrt(a))
             * (sum_(b<=V) |mu(b)|/sqrt(b)).
```

Using only the proved coefficient bounds makes this of order
`A^(1/2-sigma)*sqrt(L*V)`, or `u^(13/2-6*sigma)` on the current schedule.
That exponent is positive throughout the right half of the critical
strip. This is an audit of a proposed bound's loss, not a Lean theorem
asserting that a divisor transform has been completed. A useful version
must estimate the joint signed arithmetic expression before taking
absolute values.

Direct Möbius transformation also has additional obligations:
[Chorge and Dixit](https://arxiv.org/pdf/2410.04506), Theorem 2.9,
assumes simple nontrivial zeros and retains an explicit sum over those
zeros with reciprocal zeta derivatives. It provides no independent
upper estimate for that zero sum. No theorem from either paper has
been imported as a premise of the balanced-coefficient proof.

#### Small-prime folding of the balanced rectangle: numerical route audit

The next [probe](../scripts/probe_eta_gamma_prime_orbits.py) tests the
arithmetic signs before applying an upper comparison. It folds the actual
balanced outer coefficients into the entire inner weight `r_b`, and checks
the result independently by completing the inner Möbius convolution first.
Both calculations retain every product through the common exponential
cutoff `P=80*A`. The added balancing interval, both short sums, the complete
cofactor correction, and the off-zero centering correction remain present.
This is an exploratory calculation; no new Lean theorem or zero exclusion
is claimed in this subsection.

For a selected prime cutoff `y`, each squarefree inner index is partitioned
as `b=d*k`, where every prime factor of `d` is at most `y`, and every prime
factor of `k` exceeds `y`. The probe checks coprimality and
`mu(b)=mu(d)*mu(k)` using integer arithmetic, then forms

```
W_y(k) = sum_(d*k<=V, d squarefree and y-smooth) mu(d)*r_(d*k).
Q_bal  = sum_k mu(k)*W_y(k).
```

The full complex sum is kept. Grouping the real terms by these prime orbits
reduces their absolute envelope in every tested case, as expected from
finite grouping. A second comparison keeps the known signs for `k=1` and
prime `k` and bounds only the remaining composite cores by absolute values.
Thus it measures what the prime recurrences contribute, rather than deleting
prime-divisible indices. Once `y>sqrt(V)`, there are no remaining squarefree
composite cores: the result consists of the smooth part and a signed sum over
primes. This removes the unknown core signs but does not bound the weighted
prime sum independently.

At `u=6`, with `L=36`, `V=7776`, the critical-line controls give:

| Sample | Original inner coordinate envelope | Prime-sign comparison, `y=29` | Full signed rectangle |
| --- | ---: | ---: | ---: |
| First ordinate | `9.578654` | `1.171802` | `0.990159` |
| Second ordinate | `12.725496` | `1.211142` | `1.008450` |

At `y=89`, the prime-sign comparison equals the full rectangle. Adding the
measured absolute source corrections gives `1.001323` and `1.034631`,
respectively. Keeping those corrections signed reproduces the normalized
source, up to its finite smoothing correction. These measured costs are
not substitutes for the proved `E_bal` allowance. Merely exhausting the
composite cores therefore gives no strict saving.

The probe also tests a direct connection to the existing prime-counting
machinery. In the prime-only case it extends `W_y(n)` to all positive
integers, puts `w_n=W_y(n)/log(n)` for `n>y`, and keeps every proper prime
power. The finite calculation has the form

```
B = W_y(1) - sum_(y<n<=V) w_n
    + sum_(y<p^j<=V, j>=2) W_y(p^j)/j,
Q_bal = B - sum_(y<n<=V) (Lambda(n)-1)*w_n.
```

Writing `E(n)=psi(n)-n`, its complete signed error is

```
-E(V)*w_V + E(y)*w_(y+1)
- sum_(y<n<V) E(n)*(w_n-w_(n+1)).
```

Neither endpoint nor the proper prime powers are dropped. The available
root theorem
`abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le` in
[`RiemannXiSuzukiPointwiseChebyshevCumulativeEnvelope`](../RiemannGaussian/RiemannXiSuzukiPointwiseChebyshevCumulativeEnvelope.lean)
supplies `abs(E(n)) <= 5*n`. Inserting it into this particular absolute
Abel comparison gives numerical upper costs `415.273` and `581.594` at
the two critical-line controls at `u=6`, before source corrections. Even
replacing `5*n` by the actual finite numerical `abs(E(n))` leaves costs
`1.331367` and `1.598365`. The signed prime-discrepancy contributions are
about `0.512143` and `0.535095`, respectively; this channel cannot be
treated as a small error in these controls.

The 12 cases use `u=3,4,6`, the first two ordinates, and real parts
`1/2,3/4`. Complete source and convolution reconstruction discrepancies
are below `2.5e-14`; the prime-orbit and Abel reconstructions are below
`2.5e-15`. Selected orbits are additionally checked by independent smooth
divisor enumeration. Records are `/tmp/eta-gamma-prime-orbits.json`.
Off-critical samples are nonzeros, so their smaller centered values give
no evidence of an exclusion for a hypothetical zero. These are finite
floating-point shadows, not interval certificates.

This test does not rule out a signed prime-error approach. It does show
that the tested small-prime grouping and the existing `5*n` envelope do
not supply the missing estimate. Further work on this branch must control
the full signed correlation of `E(n)` with the changes in `w_n`, together
with `B` and all source corrections. Replacing this correlation by another
pointwise absolute envelope is not supported by the tests. No root theorem
or dashboard milestone was added for this numerical audit; its reproducible
probe accompanies the gamma theorem checkpoint.

#### Cumulative prime audit and existing library connections

The [second Abel probe](../scripts/probe_eta_gamma_cumulative_prime.py)
extends the preceding audit without changing its balanced coefficients,
prime-power corrections, source terms, or finite exponential cutoff. Put
`D(n)=sum_(j<=n) E(j)` and `delta w_n=w_n-w_(n+1)`. The complete signed
prime-discrepancy term becomes

```
-E(V)*w_V + E(y)*w_(y+1)
-D(V-1)*delta w_(V-1) + D(y)*delta w_(y+1)
-sum_(y<n<V-1) D(n)*(delta w_n-delta w_(n+1)).
```

The continuous primitive in
[`RiemannXiSuzukiPointwiseChebyshevCumulative`](../RiemannGaussian/RiemannXiSuzukiPointwiseChebyshevCumulative.lean)
does not equal `D(n)`. The exact lattice correction is
`D(n)=integral_1^(n+1) (psi(t)-t) dt+n/2`, checked independently against
the triangular von Mangoldt sum. The existing continuous envelope therefore
gives `abs(D(n)) <= (5/2)*((n+1)^2-1)+n/2`. Summing the available
pointwise estimate instead gives `(5/2)*n*(n+1)`.

At `u=6`, the critical-line controls give the following numerical upper
comparisons. They include the signed baseline `B`, keep the original
`E` endpoints signed for the second transform, and precede all source
corrections. Even this favorable treatment does not make them sufficient.

| Control | First Abel, measured `abs(E)` | Second Abel, measured `abs(D)` | Second Abel, summed `5*n` envelope |
| --- | ---: | ---: | ---: |
| First ordinate | `1.331367` | `6.638897` | `6704.057302` |
| Second ordinate | `1.598365` | `15.852540` | `20952.819798` |

The probe separately retains the first difference caused by smooth divisors
leaving at the cutoff `d*n=V`, and the part from divisors present in both
adjacent weights. In the first Abel comparison using `5*n`, the jump costs
are `3.260034` and `12.448303`; the common-divisor costs are `406.507273`
and `563.336913`. Thus clipping jumps are not the dominant loss in these
tests. Smoothing just those jumps has no demonstrated route to a useful
bound. All 12 second-transform absolute comparisons worsen; this does
not rule out an estimate that retains the signed correlation.

The full records are `/tmp/eta-gamma-cumulative-prime.json`; the portable
script reproduces them with its default arguments. Its standalone CLI was
also checked on both real parts at `u=3`, first ordinate, with exact JSON
value agreement against the original run. The largest second Abel
reconstruction discrepancy is below `2e-15`. As above, off-critical samples
are nonzeros and floating-point identities are diagnostics, not proofs.

A fetched branch review on 2026-09-08 found only `main`, `origin/main`, and
`origin/copilot/analyse-mathematical-claims`. The latter points to
`35b8c8fd50c88e5897a82c0cdb0c93538526ffb0` and is an ancestor of the
checkpoint's parent `d0d07f3200fedc964fdfb56d564bce0918c3e69e`.
There are 310 commits unique to that parent and zero unique to the other
branch. No missing branch implementation was found. Relevant machinery
already imported into the root library includes:

| Existing module | Information retained | What an arithmetic application still needs |
| --- | --- | --- |
| [EtaPhaseProjectionMargin](../RiemannGaussian/EtaPhaseProjectionMargin.lean) | Actual eta-support phase projection and the proved zero-dependent edge margin | A bound for the surviving gamma rectangle; the existing strip margin does not imply it |
| [EtaEnergyFiniteWindowReflectionCorrelation](../RiemannGaussian/EtaEnergyFiniteWindowReflectionCorrelation.lean) | Original and reflected complex correlations, self terms, and multiplicities | A useful estimate on the full correlated expression |
| [EtaEnergyFiniteWindowHeatMatrix](../RiemannGaussian/EtaEnergyFiniteWindowHeatMatrix.lean) | The complete finite Gaussian matrix, including off-line real and imaginary terms | An independent arithmetic inequality; Gaussian positive semidefiniteness alone is insufficient |
| [ProjectionHeatLeakage](../RiemannGaussian/Hybrid/ProjectionHeatLeakage.lean) | Exact `P H_u P H_v P = P H_(u+v) P - P H_u (1-P) H_v P` and the cross-time transition Gram | An embedding of the actual arithmetic direction with controlled leakage; cross-time sign is not automatic |
| [EtaSupportGapHeatCommutator](../RiemannGaussian/Hybrid/EtaSupportGapHeatCommutator.lean) | Actual support/gap kernels and mixed phase inner products | A joint estimate using their phases; the individual norm forgets them |
| [EtaCurrentFullHeatComparison](../RiemannGaussian/EtaCurrentFullHeatComparison.lean) | Full current equals support, gap, and nonpositive contributions, with integrability | An inequality for all signed companion terms together |
| [EtaSignedHeatCertificate](../RiemannGaussian/Hybrid/EtaSignedHeatCertificate.lean) | Spectral signed heat of the actual finite zero matrix and its inertia | A new upper estimate; its existing count consequence does not improve the certificate |
| [RiemannXiSuzukiGramSchur](../RiemannGaussian/RiemannXiSuzukiGramSchur.lean) | A precise implication from an absolute Gram-row premise to a Bessel bound | The Gram-row premise, which is an explicit unproved condition |

The next research target remains the full arithmetic direction, with phases,
cross terms, and all source corrections available. An independently proved
signed upper bound below the source by more than the allowance at one
admissible scale per hypothetical right-half zero would suffice. The branch
review and these finite diagnostics add no Lean theorem or zero bound.

#### Product shells, their heat complements, and a sharper factor tail

The [product-shell probe](../scripts/probe_eta_gamma_product_shells.py)
retains the complete balanced convolution, its complex phases, every
two-dimensional dyadic block, and the original short, cofactor, and
centering corrections. Its independent checks include 92 exact rational
product coefficients and 60 complete kernel evaluations using
`tau(n)-2*1_(2|n)*tau(n/2)`. The coefficient checks agree exactly; the
largest kernel discrepancy is below `2.8e-15`. All 12 original records
are reproduced exactly before adding these checks, and the complete
source reconstruction discrepancies remain below `2.4e-14`.

After removing the reciprocal-product component, grouping by product
shells or by pairs of factor shells gives weaker absolute comparisons
than completing the entire inner Möbius factor first, in all 12 cases.
At `u=6`, the critical-line controls give:

| Control | Full inner factor, then row envelope | Product-shell envelope | Two-dimensional shell envelope |
| --- | ---: | ---: | ---: |
| First ordinate | `1.043158` | `2.022516` | `2.165036` |
| Second ordinate | `1.250334` | `1.993680` | `2.687796` |

The multiplier `exp(-h*log(ab/A)^2)` is tested with its entire signed
complement retained. At `h=2`, the retained real parts are `-0.142803`
and `-0.200741`, but the removed parts are `1.132962` and `1.209192`.
Their sums recover the original rectangles. Thus the negative localized
value cannot bound the original signed sum. The main positive product
shells in these controls lie between about `A/16` and `A/2`; the
negative blocks at larger products remain important.

The eta factor vanishes at the zeta pole, cancelling the potential double
pole of `zeta(z)^2`. The cofactor kernel consequently has the single
reciprocal-product component already used in the balancing audit. A
formal Mellin expansion of the centered kernel predicts a leading cubic
remainder `-(eta(s-3)-eta(s))*zeta(s-3)*x^3/6`. Forty additional finite
evaluations at `x=2^-k`, `k=3,...,12`, approach that coefficient; these
records are `/tmp/eta-gamma-product-cubic.json`. This is an analytic lead,
not a compiled asymptotic or a proved cubic bound for the cofactor kernel.
Even a low-product bound would leave the measured positive region above.

There is also a general exponent check on a pointwise divisor-error
approach. If its proposed remainder is `O(x^(sigma-theta))` with
`0<=theta<1`, taking absolute values of both coefficient vectors gives
an upper budget proportional to
`A^(theta-sigma)*(L*V)^(1-theta)`. For power schedules
`L*V=A^q`, `q>=1`, its exponent is
`1-sigma+(1-theta)*(q-1)`, which is positive in the critical strip.
This does not bound the actual sum from below or exclude a special finite
scale. It shows that sharpening the pointwise exponent alone does not
make this absolute comparison an asymptotic sub-source bound.

The new compiled estimate is instead a sharper bound for the full omitted
cofactor in [EtaGammaFactorTail](../RiemannGaussian/EtaGammaFactorTail.lean).
It avoids the earlier loss from replacing both factor cutoffs by the
single coefficient envelope `n^2`. For actual factors `f,g` bounded by
one and vanishing through `L,V`, respectively,
`norm_evaluate_mixed_factor_le` proves

```
norm(Eval_gamma(zeta * f * g)) <= B(rho,A,L,V),
B = 64*norm(chi(rho))*A^2*(L*V)^(-1-sigma)*exp(-L*V/(2*A)),
```

provided `A>0` and `L*V>=2*A`. To see where the saving comes from,
keep the actual triple `a*b*k`, with `a>L`, `b>V`, `k>=1`. Then

```
a*b*k >= a*V + b*L + k*L*V - 2*L*V.
```

The original exponential carrier bound retains `(a*b*k)^(-sigma)`.
Three separately summable exponential arithmetic functions then majorize
the full convolution. Their masses are bounded by
`exp(-L*V/(2*A))*2*A/V`, `exp(-L*V/(2*A))*2*A/L`, and
`2*exp(-L*V/(2*A))`. The proof uses the exact multiplication theorem
for convergent arithmetic-function sums; no product fibre or infinite
cofactor is dropped.

The theorem `norm_smoothError_sixth_factor_le` specializes this to

```
norm(J(rho,u^6,u^4)) <= 64*norm(chi(rho))*exp(-u^2/2)
```

for `u>=2`, `sigma>=1/2`. At `u=6`, this is approximately
`9.75e-7*norm(chi)`, replacing approximately `1.28e13*norm(chi)`.
These numbers compare only the omitted-cofactor allowance. Both short
sums and the physical endpoint correction still have to be paid.
The compiled `norm_smoothQuadratic_sixth_sub_source_factor_le` gives
their complete sum:

```
norm(Q(rho,u^6,u^4)-S_rho)
  <= 2*C_rho*u^(-2-4*sigma) + 64*norm(chi(rho))*exp(-u^2/2)
     + norm(chi(rho))*(1+16*2^(-sigma))/(6*u^18).
```

The original rectangle also inherits the new bound. For the balanced
rectangle, `norm_balancedRectangle_sub_source_factor_le` includes both
short allowances, `32*C_rho*L^4/A^3`, five copies of `B`, and the
physical endpoint allowance. The factor five pays one original omitted
cofactor and the added interval's factor of at most four.

This is an independently proved improvement to the full source error
budget. It does not establish a sub-source bound for the surviving signed
sum, a new zero exclusion, or RH. The ongoing target is unchanged.

Verification: warnings-as-errors direct elaboration, the focused build
(`4429` jobs), and the full root build (`9721` jobs) passed. All 14 verbose
root declaration-lint checks passed, as did the project lint. The six
public terminal theorems in `EtaGammaFactorTail` depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The compiled inventory
contains 874 project modules, 18617 declarations, and 16009 theorems,
with zero project axioms, zero placeholder-dependent declarations, and
no nonstandard theorem axioms. The product-shell probe passed all 12
cases and its independent coefficient and kernel checks; the two-record
CLI subset also reproduces the full run exactly. These numerical checks
remain exploration rather than theorem evidence.


## Exact gcd blocks and reflected diagonal control

The subsequent [gamma gcd and reflection ledger](eta-gamma-gcd-reflection.md)
records the response to the user's new steering memo. The original smooth
quadratic now has an absolutely convergent complete-row expansion and an
exact finite gcd partition, including both divided cutoffs, all three
coprimality conditions, and the full complex common-factor power.

`EtaGammaGcd.norm_largeGcd_le` bounds the complete large-gcd contribution
by `64*norm(chi)*G^(1-2*sigma)/(2*sigma-1)` for `sigma>1/2`, `G>=1`,
`G^2>=2A`. On the concrete `A=u^8`, `U=u^5`, `G=2u^4` schedule it
vanishes, while `EtaGammaQuadratic.smallGcd_eighth_fifth_tendsto_source`
proves that the remaining core retains the original source.

`EtaGammaReflection.smoothQuadratic_partner_mul_conj` keeps the entire
reflected product. Its actual common-gcd diagonal coefficient is
`mu(g)^2/g^2`; its complete reduced core remains complex. The terminal
`norm_gcdCrossDiagonalTail_le` bounds that diagonal above `G` by
`4096*norm(chi(rho#))*norm(chi(rho))/G`, with both physical thresholds
paid. This holds throughout the strip and yields `O(u^-4)` on the same
schedule. It does not bound the unequal-gcd interactions.

The source normalization now connects exactly to the existing Laplace
reflection rigidity theorem, but equality of the normalized source
energies is still unproved. The single-index reflected Moebius diagonal
has `mu(d)^2/d`, not a signed `mu(d)/d`; harmonic Moebius cancellation
cannot be substituted for that coefficient. The remaining test is a
signed estimate on the retained small-gcd and off-diagonal objects,
including every source allowance. No new zero exclusion is claimed.
