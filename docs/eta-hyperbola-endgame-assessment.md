# Exact hyperbola split and the remaining quotient estimate

The completed current reconstruction and the original uniform weighted
arithmetic bound remain the active objective. The bound, full logarithmic
arithmetic decay, and RH are still open. The new research direction tests
the zero-dependent source reductio suggested in
`/home/dbsanfte/riemann/RiemannGaussian_hyperbola_reductio_steer-1.md`.
The memo is a research proposal, not an input to Lean's proof kernel.

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

The prior logarithmic Möbius family remains available as a separate
arithmetic program. Its complete growing head and quadratic tail decay,
and `p_M log M→1`; the band `floor(log M)<L≤M²` is still uncontrolled.
See the [arithmetic residual assessment](eta-parity-endgame-assessment.md).
Neither that gap nor the original weighted-current objective is closed
by this hyperbola package. No sharper numerical zero strip or novelty
claim about an RH-level theorem is made.
