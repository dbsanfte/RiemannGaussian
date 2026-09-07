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
Abel summation now also identifies every capped shell with an alternating
Möbius bilinear sum and both boundary terms. The high aggregate uses one
fixed product coefficient sequence across its physical window, and its
entire energy has an explicit overlap matrix. The original hyperbolic
collision bound applies to the alternating coefficients, but does not
bound their full signed quadratic form.
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
complement. The constant depends on `p`, and the present theorem treats
one fixed odd prime at a time; simultaneous exclusion of a growing prime
set, its overlaps, and its accumulated error have not been bounded.
The oddness condition is essential to this identity. None of these
statements proves the original uniform weighted bound or a new zero strip.

As a diagnostic only, floating-point samples at the first two
critical-line zeros gave normalized prime-product energies for `p=3`,
`v` replaced here by the original `u`, of about `0.00197` and `0.00822`
at `u=16`, and `0.0000719` and `0.0000976` at `u=128`. The numerical
test used the actual coefficient arrays and checked the prime coefficient
recurrence exactly as integer arrays. The Lean identities and bounds
above do not depend on those samples; no off-critical zero was sampled.
