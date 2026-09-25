# Joint shifted configurations and cancellation across a share boundary

The subsequent [literal joint prime transfer](zeta-riesz-joint-prime-transfer.md)
pays the exterior factorial tails and canonical-owner removal arithmetically.
The remaining masked signed sum is still open.

This local continuation leaves the RH, zero-free-region and certificate
frontiers unchanged. There is no independent signed floor for the final
carrier. It proves one literal arithmetic error bound and a quantitative
joint modal cancellation theorem, with their remaining bridge explicit.

## 1. Cancel the shifted configurations before estimating modes

[`ZetaRieszJointShift.lean`](../RiemannGaussian/ZetaRieszJointShift.lean)
proves the nonempty-subset expansion and its exact signed ledger for
arbitrary finite masks and weights. At count-transform level,

\[
\frac{1-P/H}{z^2}+\frac{P}{H}\frac{1-H}{z^2}
=\frac{1-P}{z^2}.
\]

Thus jointly adding the complete shifted correction cancels the shifted
channels. It returns the original response, **including its original pole**;
this algebra is not itself a saving. `original_pole_split` retains that
pole coupled to the entire negative-mode product Q:

\[
\frac{1-\frac{w+z-b}{w-b}Q}{z^2}
=\frac{1-Q}{z^2}-\frac{Q}{z(w-b)}.
\]

The same module sums factorial allocations before estimating them. For
normalized shares x and a selected subset B, the exact full multinomial
tilt is `(1+(C-1)*sum_B x)^M`. It includes every order, including zero
and one. `kernel_multiplier_all_orders` states the shift identity for
the factorial kernel itself, without multiplying an order-zero kernel
by zero.

There is a necessary correction to interpreting the old modal probes.
The Riesz difference at a prime uses `1-exp(-z*log(p))` at both centers.
The factorial scale C does **not** rescale this cutoff. After aligning
the logarithmic poles, the exact two-variable positive-pole factor is

\[
\frac{(a+z)/a}{(Ca+z)/(Ca)}=\frac{C(a+z)}{Ca+z},
\qquad
\frac{1-C(a+z)/(Ca+z)}{z^2}=\frac{1-C}{z(Ca+z)}.
\]

`pole_count_ne_one` proves this is nontrivial for the actual shifted-center
ratio and nonzero regular cutoff. The one-variable pole cancellation
remains exactly true. Earlier common-clock finite-mode counterexamples
remain counterexamples to their stated model inferences; they were not
literal two-variable prime-packet transfers. Do not use either interpretation
to erase the other's hypotheses.

## 2. A literal finite correction now has a source-scale bound

[`ZetaRieszJointShiftError.lean`](../RiemannGaussian/ZetaRieszJointShiftError.lean)
keeps the existing `fullParityBand` and original rectangle allocations.
For every selected prime and allocation,

\[
\log p\ge\frac{117}{5000}N,\qquad k_p\le N+2,
\qquad \left|C^{k_p}/p\right|\le e^{-N/50}\quad(N\ge1).
\]

The count ceiling 39 therefore bounds the complete product error by
`2^39*exp(-N/50)`. Summing the original nonnegative factorial weights
preserves this estimate. No low-order allocation is discarded.

`correctionPacket` is the literal finite signed sum of this correction
against the original residual coefficient and complex kernel. The exact
`shiftedPacket_ledger` is

\[
\mathrm{shiftedPacket}=\mathrm{fullParityPacket}
+\mathrm{correctionPacket}.
\]

For `0<=u<=10001/20000`, `|y|>54`, and N>=1,

\[
\left\|u^{N+1}\mathrm{correctionPacket}\right\|
\le 2^{39}U\,r^N\,mathrm{MajorantMass}(1+1/262144),
\quad
r=U\frac{262144}{131071}e^{-1/50}<1.
\]

Numerically this rate is approximately `0.98030417`; the strict inequality
is proved in Lean, not inferred from that decimal.

`tendsto_shiftedPacket_sub_original` proves decay along every cofinal
order schedule, with arbitrary moving finite count cutoffs. This is an
independent arithmetic comparison on the **fixed** lower-share box.
It does not extend to a shrinking share threshold. It does not identify
the shifted packet with a completed mode product or prove that either
packet tends to zero. In particular it does not rescue the old fixed-cutoff
packet by pole cancellation alone.

## 3. The growing internal edge cancels in a joint share integral

The optional probe
[`probe_riesz_joint_share.py`](../scripts/probe_riesz_joint_share.py)
uses a finite synthetic divisor with eight zeros, respecting conjugation
and `beta -> 1-beta`. These are **not asserted zeta zeros**. Its cofactor
count product includes the original positive pole, all negative modes and
the empty-cutoff residue. The marked-largest density also includes the
positive pole and all negative modes. It integrates the share before
integrating the radial variable.

The model retains the finite radial window, factorial kernel and moving
Riesz length. Its share measure is **dp**. It does not include the literal
prime measure, positive least-share cutoff, factorial rectangle, original
allocation or discrete masks; those transfers are not claimed.

Set the selected height to 55 and introduce the synthetic height ratio
`-37/43`. The phase is resonant exactly at the old lower share edge
`43/80`, because

\[
-\gamma+\frac{43}{80}
\left(\gamma+\frac{37}{43}\gamma\right)=0.
\]

The separate endpoint has source exponent
`log(2U)+log(U)/10000`, approximately `0.00003069028`.
`model_seam_exponent_pos` proves it exceeds `3/100000`.

The signed numerical responses, at source scale, are:

| N | log10 norm on [43/80,9/16] | log10 norm on [21/40,43/80] | log10 norm of their signed sum |
|---:|---:|---:|---:|
| 65,536 | -3.91667 | -3.91526 | -6.30595 |
| 262,144 | -1.83104 | -1.83104 | -7.87270 |
| 1,048,576 | 7.88458 | 7.88458 | -12.06475 |

The two growing terms cancel at their common boundary. Neither a fixed-share
estimate nor a sum of the two norms sees this cancellation. The probe checks
130- versus 190-digit arithmetic, the partial fractions, the joint count
identity and the signed interval identity. Exact floor lengths are used
through N=8192; subsequent length approximations carry an explicit error
bound propagated to the response. Every numerically omitted term has an
absolute envelope in the report. See
[`riesz-joint-share-probe.json`](riesz-joint-share-probe.json).

## 4. The cancellation and a geometric bound are now Lean theorems

[`ZetaRieszJointShare.lean`](../RiemannGaussian/ZetaRieszJointShare.lean)
proves the exact antiderivative

\[
\int_a^b e^{(c+qB)T}\,dq
=\frac{e^{(c+bB)T}-e^{(c+aB)T}}{BT}.
\]

`jointModal_seam` cancels the shared endpoint **before** taking a norm.
`radialPrimitive_bound` controls the finite radial antiderivative by three
times its endpoint amplitude. This avoids an uncontrolled growing-order
integration-by-parts constant.

For the two exterior denominators `a_q=1/2-c-qB`, assuming
`Re(a_q)>=1/2` and `norm(a_q)>=1`, the proved bound is

\[
|\mathrm{jointModal}_N|
\le\frac{6U}{|B|}\left(r_-^N+r_+^N\right),
\quad
r_\pm=U t_\pm e^{1-t_\pm/2}<1,
\quad (t_-,t_+)=(1.95,2.03).
\]

The additional moving-cutoff factor `exp(z*L_N)` is retained under
`Re(z)<=0`, `L_N>=0`. Both radial rates are rigorously below one; the
weaker rate is approximately `0.99998861`. The theorem places **no bound
on the shared internal denominator**. `model_joint_tendsto` instantiates
the resonant seam regression: its two outer frequency gaps are
`gamma/43` and `2*gamma/43`, while the interior denominator is exactly 1/2.
It proves decay of the jointly integrated dangerous modal term for every
`|gamma|>54`. The entire eight-zero numerical response is a broader
experiment, not the conclusion of that instantiated theorem.

The probe includes a necessary negative control. Retuning the synthetic
height ratio to `-19/21` moves the resonance to the new exterior edge
`21/40`. The enlarged interval then grows again: its log10 normalized
norm is about `8.36471` at N=1,048,576. `retuned_edge_resonance` proves
that a synthetic pair can resonate at any chosen nonzero share edge.
Thus enlarging this particular interval is not a uniform remedy. The
exterior frequency assumptions in `jointModal_bound` must be proved
for the actual combined response, or its remaining boundary terms must
cancel with further literal pieces. The result does not assert a gap
for arbitrary actual zeta-mode assignments.

## Remaining mathematical obligation

`finite_weighted_seam` retains arbitrary common arithmetic weights in
an exact finite partition. To use the modal saving on the actual carrier,
one must derive a **joint** expression for neighboring share regions with
their Riesz coefficients, finite factorial selections, least-prime and
physical masks intact. Estimates cannot separate the boundary terms first.
No completed-leg convergence through a mask has been invoked.

The neighboring slice lies in the explicit complementary carrier; it is
not discarded or treated as a free reserve. The exact amplitude and phase
at the common boundary must match in a valid discrete-to-modal argument.
The positive-cutoff identification and remaining signed rest bound are
still open. No broad packet, shrinking-cutoff comparison, independent
floor or new zero exclusion is proved by this slice.
