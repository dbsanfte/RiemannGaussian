# Complex null moments in the joined signed floor

The independent cofinal floor is **open**. This local pass strengthens the
actual whole-carrier signed inequality and proves exact cancellation of the
previously obstructive coherent early channel. It does not prove a numerical
native budget, a zero exclusion or RH.

## Exact cancellations, with both phases retained

For every squarefree label with at least three prime factors, the constant,
first-log and second-log Möbius divisor moments vanish. The checked
`nullProfile_pairing_zero` and `complex_null_zero` apply this to the original
label weights, including every count, allocation, phase and physical mask.

Let `f=correctedProfile X L 1 0`. Define the exact centered null profiles

\[
q_1(d)=\log d-\log X,\qquad
q_2(d)=\frac{(\log d)^2-(\log X)^2}{N+1},\qquad(d\le X),
\]

and zero beyond `X`. The implementation defines them by differences of the
already checked corrected profiles, so their pairing is exactly zero.
For the complete complex divisor prefix `Phi(k)`, choose one vector
`(v, Re A, Im A, Re B, Im B)` over **all** counts and cutoffs. Its increments are

\[
(\operatorname{Re}\Phi-v\operatorname{Im}\Phi)\Delta f
 +\operatorname{Re}(A\Phi)\Delta q_1
 +\operatorname{Re}(B\Phi)\Delta q_2.
\]

`sum_increment_eq` proves their total is exactly
`Re(carrier)-v*Im(carrier)`. Each complete cutoff period is summed before
charging its adverse net contribution. All early cutoffs, including the
empty-divisor/coherent channel, remain in this cost.

The compact minimum over the cube `[-4,4]^5` contains the previous bounded
global phase tilt. `bestCost_le_old` proves the new **actual signed cost**
never exceeds the former one. This is not an energy-only projection, a
sectorwise minimization or a claim that the gain is always strict.

## Kill the coherent early channel without a norm price

If the common moment is `M`, choose

\[
A=a\,\frac{i\overline M}{|M|},\qquad
B=b\,\frac{i\overline M}{|M|},
\]

with zero coefficients when `M=0`. The null increment becomes

\[
\frac{\operatorname{Im}M\operatorname{Re}\Phi
      -\operatorname{Re}M\operatorname{Im}\Phi}{|M|}
       (a\Delta q_1+b\Delta q_2).
\]

Consequently it vanishes whenever `Phi` is a real multiple of `M`.
`increment_coherent_zero` proves that every such flat cutoff is exactly zero.
`first_cutoff_zero` applies this to the literal cutoff-one common moment of
every population, regardless of its size. `orthogonal_floor` removes only
these proved zero increments from the **whole signed floor**; noncoherent
early cutoffs remain charged.

This addresses the common-moment obstruction in `ZetaRieszNullProfileAudit`
for these cross-phase corrections. That audit of the old real correction
remains valid and unchanged. There is no assumption that the full core is
rough, that a partial imaginary sum is zero, or that small primes are paid.

## Same original carrier, stronger exact cost ledger

Write `D_j` for the new native cost, `G_j` for old native cost minus `D_j`,
and `C_j` for the previously retained phase credit. Lean proves `G_j>=0`
and the unconditional finite floor

\[
\operatorname{Re}(u^{N_j+1}\operatorname{joinedPhysical}_j)
 \ge -D_j-\operatorname{nativeError}_j.
\]

`nativeError` is unchanged: `4*abs(Im P)+5*norm(Q-P)`, with `Q` the existing
count-cropped core and `P` the original whole carrier. Its vanishing under
the exposed source remains checked for every analytic multiplicity.

`bestCost_add_credits_le_original` proves the required COST comparison
before retaining both credits. `eventually_joined_floor_with_credits` gives

\[
\operatorname{Re}P_j\ge C_j+G_j
 -\sqrt{\max(E_j,0)\,129N_j/200}-e_j,
\]

with the same signed remaining energy `E_j` and the same already-paid error
`e_j` from `ZetaRieszJointCreditFloor`. Every geometric pair price is charged
once. Neither credit is assumed large; no signed-energy monotonicity is used.

The direct remaining independent target is cofinally

\[
D_j\le399/5000=0.0798.
\]

`false_of_cofinal_nativeCost` retains this **explicit open hypothesis**.
The cost is not proved to tend to zero: `negative_real_le_bestCost_of_im_zero`
shows that, when the whole imaginary part vanishes, it must still pay the
negative whole real contribution. The multiple-source ceiling remains open.

## Optional quantitative diagnostics

`scripts/probe_riesz_complex_null_profiles.py` enumerates all squarefree
subsets of the same two constructed twelve-prime universes, using the
original masks, allocation and phases. It includes all divisor cutoffs and
joins counts and complete periods before a single convex linear program.
It checks both exact null sums numerically and retains the actual imaginary
correction of the finite subset.

At `N=256,640`, two seeds and heights `54,65,100`, complex null corrections
improve 7 of 12 former bounded-tilt period costs by approximately
`3.75%..32.74%`; five give no gain. Restricting to coherent-channel-free
coefficients improves four of twelve by `5.02%..17.48%`. The imaginary null
corrections alone give no gain in these cases: the improvement is joint.

These are rescaled probable-prime finite universes, with floating logarithms
and interpolated huge cutoff-period edges. They are not the full core,
interval certificates, a source-budget comparison, a uniform saving or
cofinal evidence. The actual finite-subset imaginary correction can worsen
the cost. The probe is optional and is not in any build or CI workflow.

A further `N=1536`, one-seed check improves the old cost by about `12.42%`
at height `65`, and gives no gain at heights `54,100`. The coherent-channel-
free restriction gives no improvement in those three larger-order tests.
This does not support a uniform saving or a rate; do not treat the fixed
five-parameter search as an established route to the numerical budget.

The next arithmetic question is the size of the **joined cross-phase null
gain** on the full population, including noncoherent early and late cutoffs.
Do not replace that question by another profile-energy improvement or claim
that the exact null identities alone supply the independent floor.
