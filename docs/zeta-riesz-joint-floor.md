# The direct joint floor is sufficient

The latest [central source-scale comparison](zeta-riesz-central-reserve.md)
gives an explicit growing signed credit for a literal triple/four/five-prime
selection, in both lower and upper directions. Its opposing signed
complement remains; under a finite whole source it is unbounded in the
opposite direction. The earlier exponential-head payments and all exact
coefficient refinements remain available, without double spending their
supplies. The numerical whole-joint-sum floor and ceiling below remain open.

The [phase-density audit](zeta-riesz-phase-density-audit.md) now checks why
opposite-phase pairing cannot be justified by local count accuracy alone:
an exponentially small real density error can retain any fixed source
inside the same radial core. It does not model the literal prime sum or
pay another arithmetic component. Its phase-correlated error must be
controlled before applying such a comparison to either endgame bound.

The simple-zero endgame does not require separate decay of the retained
packet and its complement. It requires a lower bound for their signed sum
at arbitrarily late indices. Multiple zeros have the opposite source sign
and need a further argument; the checked two-sided criterion below uses an
upper bound for the same sum. `ZetaRieszJointFloor` states both obligations
for the existing literal expressions, without introducing a new carrier.

Use the original dyadic orders `N_j` and count thresholds `K_j`. For this
note only, abbreviate

\[
\begin{aligned}
J_j&=\mathrm{lowerThresholdPacket}(u,y,N_j,K_j)
       -\mathrm{shortOverflowPacket}(u,y,N_j,K_j),\\
C_j&=\mathrm{ZetaRieszLeastBoundary.rest}(u,y,N_j,K_j).
\end{aligned}
\]

Here `C_j` is the **signed complementary core response**. It is not the
old complete harmonic companion, and it is not an absolute allowance.
Every original arithmetic mask, phase, allocation and factorial weight
stays in the two existing expressions.

`tendsto_nondominant_sub_joint` proves independently of any zero hypothesis
that

\[
\mathrm{nondominantRemainder}_j-u^{N_j+1}(J_j+C_j)\longrightarrow0.
\]

It combines the two paid logarithmic-window errors, the exact
`coreResponse = fullPacket + rest` ledger, and the paid replacement of
`fullPacket` by the current lower-threshold/overflow expression. It never
takes separate norms of `J_j` and `C_j`.

There is a practical simplification here: in `fullPacket + rest`, the
rectangle selection and its complementary fraction add to one exactly.
Thus a direct core floor need not solve the artificial largest/least-share
or rectangle-projection problems introduced to isolate that packet. The
original core support, unassigned factor `1-boundedShare`, Riesz coefficient
and phase still remain. The packet's count ceiling 55 is not a count ceiling
for this whole sum; the complementary counts remain in `rest`.

Consequently, under the original simple exposed-zero hypotheses,

\[
u^{N_j+1}(J_j+C_j)\longrightarrow -1+c_{\rm ret}(u),\qquad
c_{\rm ret}(u)=\frac{\log(32/13)}{-2u\log u}-\log(19/13).
\]

Simplicity is a substantive restriction here. The actual theorem
`tendsto_joint_exact_source` retains arbitrary analytic multiplicity `m`
and gives the source `-m + m^2*c_ret(u)`. The exposed-zero selection theorem
isolates a zero location; it does not show `m=1`, even if that location is
the only zero in the exposed disk. No theorem currently supplies a simple
exposed counterexample whenever RH fails.

On `1/2 <= u <= 10001/20000`, the new rational estimate
`retainedCost_lt_restricted` proves `c_ret(u)<921/1000`. Thus the sufficient
arithmetic target is only

\[
\boxed{\quad
\operatorname{Re}\bigl(u^{N_j+1}(J_j+C_j)\bigr)
\ge-\frac{79}{1000}-\varepsilon_j
\quad\text{for arbitrarily large }j,\qquad \varepsilon_j\to0.
\quad}
\]

`false_of_joint_cofinal_floor` proves the contradiction **conditional on
this inequality and simplicity**. An eventual floor, positivity, decay to zero and bounds
on either component separately would all be stronger than necessary.
The allowance `79/1000` is also larger than the previous sufficient
`3/40`, reducing the required accuracy of a joint estimate. No assumption
that the error is nonnegative is needed.

For orientation, direct high-precision evaluation gives source values
approximately `-0.07992934` at `u=1/2` and `-0.07987180` at `u=0.50005`.
These endpoint diagnostics do not establish a uniform bound; the Lean
rational inequalities supply that bound over the entire interval.

### Multiplicity audit and an unchanged-carrier repair

`retainedCost_gt_nine_tenths` now proves the complementary uniform bound
`9/10 < c_ret(u)`. Together with the existing upper bound, Lean proves
that the source is below `-79/1000` for `m=1`, but above `3/2` for every
`m>=2` (`multiple_source_gt_three_halves`). In particular, the present
negative floor is compatible with every multiple-zero source. This is
an obstruction to that floor alone, not a contradiction or a failure of
the multiplicity-preserving source theorem.

The same literal joint sum can handle all multiplicities if it also has
an independent upper bound. `false_of_joint_cofinal_bounds` checks the
sufficient pair of arithmetic targets

\[
-\frac{79}{1000}-\varepsilon_j
\le \operatorname{Re}\bigl(u^{N_j+1}(J_j+C_j)\bigr),
\qquad
\operatorname{Re}\bigl(u^{N_j+1}(J_j+C_j)\bigr)
\le \frac32+\eta_j,
\qquad \varepsilon_j,\eta_j\to0.
\]

Each inequality need only hold cofinally; their subsequences may differ.
The floor excludes `m=1`, and the ceiling excludes `m>=2`. Neither
arithmetic bound has been established for the whole sum. This repairs the
scope of the *conditional endgame* without asserting its premises, defining
a new carrier, discarding a sign, or assuming global simplicity.

The [complete-period upper payment](zeta-riesz-capacity-phase-payment.md#upper-payment-over-a-complete-period)
is actual arithmetic progress toward the ceiling: selected five-prime
credit pays the entire eligible positive-coefficient four-prime population
over one complete period at every sufficiently large dyadic order. The
estimate retains the original signed complement and does not bound it.
Neither this payment nor the corresponding lower payment establishes
either whole-sum inequality above.
The subsequent [joint three/four/five payment](zeta-riesz-capacity-phase-payment.md#balanced-triples-paid-from-the-same-five-prime-credit)
uses the same five-prime credit to pay all selected four-prime terms and
every balanced triple with prime shares in `997/3000..1003/3000` throughout
a complete phase period. This is checked in both directions, with one
signed complement in each case; the remaining triple shapes and other
sectors are still open. It does not presume or prove simplicity.
The subsequent [central comparison](zeta-riesz-capacity-phase-payment.md#checked-central-payment-for-the-broader-triple-band)
enlarges the paid triple band to `31/100..7/20` and proves both complete-period
inequalities with common credit `1309/10000`, debit `1261/10000`, and margin
`g*V0*h/500`. Its five-prime cover and literal transfer are checked. The
same whole-sum floor and ceiling above remain open because the remaining
signed complement has not acquired either required bound.

The existing Gaussian theorem `simple_of_near_edge` supplies simplicity
only in its explicit height-dependent boundary layer, not throughout this
fixed candidate strip. The upstream `normalizedAdaptiveSmooth` carrier
also has a multiplicity-robust `-m` source and a sufficient floor above
`-1`; its independent floor is likewise open. Those are alternative
routes, not reasons to erase the current multiplicity obligation. Extending
any restricted exclusion to the full RH range remains a separate task.

The independent arithmetic floor remains open. The new theorem transfers
and sharpens its sufficient threshold; it does not control more of the
signed prime sum. In particular, numerical evidence for `J_j` alone is
insufficient unless its correlated `C_j` is retained in the same comparison.
Balanced triples in `C_j` are not paid by the divergent absolute
`restAllowance`. Work on separate component decay is optional and should
continue only when it directly helps this joint lower bound.

There is also a checked reason not to replace the fixed-family target by
a bound uniform over arbitrary complex bilinear coefficients.
[`ZetaMultiplicativePhase.uniform_re_floor_iff_norm_bound`](../RiemannGaussian/ZetaMultiplicativePhase.lean)
proves that such a uniform signed floor is equivalent to a norm bound:
a unit rotation of one freely chosen coefficient family rotates the
entire response to the negative real axis. The matrix can retain every
correlated cutoff, factorial weight and coprimality condition. Its entries
are not replaced by their absolute values.

The existing exact multiplicative-phase transport then makes this uniform
floor equivalent to a **zero-height norm bound**. The new
`cofinal_uniform_floor_iff_zero_height_bound` proves the equivalence also
when the uniform assertion is required only at arbitrarily late indices,
with arbitrary moving orders, masks, heights and error budgets. The
cofinal quantifier is outside the coefficient quantifiers on both sides.

This is an audit of a stronger proposed proof method, not an obstruction
to the desired floor. The actual arithmetic coefficients cannot be
rotated freely. Preserving those fixed signed correlations is precisely
what keeps the joint cofinal floor weaker than a norm estimate. This audit
does not bound an additional component of the arithmetic carrier.

An actual component bound is now available in
[`ZetaRieszCoreExtensions`](zeta-riesz-core-extensions.md): all squarefree
extensions of a balanced triple that remain in the core have vanishing
mass relative to that triple, uniformly over their phases and selections.
Composite extensions cancel exactly; Chebyshev's prime bound and the
original factorial curvature control the rest. This rules out extending
one fixed balanced triple as its sole compensation mechanism. It does not
give source-scale decay after summing over base triples, or control
cancellation with different large-prime configurations. The joint floor
above remains open.

The subsequent [four-prime compensation theorem](zeta-riesz-quadruple-compensation.md)
does prove an independent signed comparison between different actual
large-prime configurations: one fixed-width balanced triple box is paid
by at most `B/(N+1)` of a positive four-prime supply. The exact core ledger
keeps its unspent positive credit and the full signed complement. This
neither pays all balanced triples nor makes the amount spent a vanishing
source error. The remaining target is still the joint floor, including
that unused credit, rather than separate bounds for the resulting pieces.

[`ZetaRieszFourPrimeFloor`](zeta-riesz-four-prime-floor.md) now supplies a
signed bound for the whole four-prime class. With `T=log n`, its coefficient
has the weak sign of `g=log(largestPrime n)+T-2L` and lies between
`-(T/L)*max(0,-g)` and `(T/L)*max(0,g)`. The original core discharges the
length conditions eventually. Its real-atom comparison retains all
positive credit and charges only `weight*(T/L)*max(0,-g*cos(y*T))`.
The non-four-prime complement stays signed. This explicit debit is not
yet controlled at source scale; the joint floor remains open.

[`ZetaRieszFivePrimeFloor`](zeta-riesz-five-prime-floor.md) extends the
same comparison to all five-prime labels. A positive coefficient requires
both a large largest-prime share and a large separation from the second
prime. The upper allowance retains both gaps and is capped by three
least-prime logarithms. The joint four/five-prime lower comparison keeps
all actual positive credit, every other prime count, and the five-prime
positive-cosine terms signed. It introduces no new carrier or error term.
It confines an adverse sector but does not yet pay the aggregate debit
at source scale; the cofinal joint target above remains open.

[`ZetaRieszBandCompensation`](zeta-riesz-band-compensation.md) now pays all
balanced triples in `2N<=log n<=2N+1` whose prime logs lie within `η*N` of
`2N/3`, for some fixed `η>0`. A three-dimensional disjoint four-prime grid
provides enough actual positive mass to pay at most half its credit.
The region is eventually nonempty; its prime-log width grows with `N`.
The exact ledger retains every other signed term and at least half the
supply. This still covers only one total-log interval and a conservative
share width; it is not the whole cofinal floor or a vanishing source error.

The [radial compensation theorem](zeta-riesz-radial-compensation.md) now
extends this to a fixed positive balanced share band throughout the
original core. Disjoint supplies pay successive triple slabs; all balanced
labels missed at the radial edges have an independent geometric allowance.
The original moment order remains fixed while the slab centre varies.
The terminal floor keeps the complete signed complement, positive triple
credit and at least half the supply. It does not pay every triple share
configuration or the remaining prime counts. The full joint target above
remains open.

The [exact four-prime reserve](zeta-riesz-four-prime-reserve.md) replaces
the negative four-prime allowance by an exact clipped-log formula. Its
observed debit never exceeds the previous largest-prime bound.
`eventually_compensated_core_floor` combines the sharper four/five-prime
comparison on the untouched complement with the paid balanced triple band
and at least half its positive supply. The only error is the existing
radial-edge allowance. This keeps one joint signed target; its final
numerical lower bound is still open.

The [five-prime reserve slice](zeta-riesz-five-prime-reserve.md) makes the
five-prime negative-cosine debit exact too. It accounts for every cofactor
prime excess after deleting the largest prime and is pointwise no larger
than the previous clipped allowance. The compensated-core inequality keeps
the paid triple band, half the supply and all other signed sectors.
Coefficient slack is removed on this sector; its weighted population and
the whole joint numerical floor remain open.

The [positive-head payment](zeta-riesz-five-positive-head.md) now bounds
that coefficient by one marked-prime logarithm and proves its positive
part vanishes when two small cofactor logs fit below the deletion cutoff.
Actual counting pays the surviving positive five-prime head with a prime
at most `N^2` throughout the existing radial selection, alongside the
original narrow triple band and count-three/count-four heads. One eighth
of their single supply remains. The new `eventually_core_joint_floor`
keeps all favorable selected parts and the full signed complementary
carrier. It replaces the earlier spending ledger; neither the complete
rest's floor nor its multiple-zero ceiling has been proved.

`ZetaRieszFivePositiveHead.eventually_core_full_exponential_floor` now
extends that same payment to a fixed common exponential small-prime head
and pays the radial and dominant-prime omissions with the existing
vanishing allowance. Its exact rest has no surviving positive five-prime
label containing a prime below the common exponential threshold. This
still leaves other triple shapes, the unselected five-prime sign, higher
counts and all remaining signed terms; their combined one-sided numerical
bound has not been established.

The [upper head comparison](zeta-riesz-head-ceiling.md) now develops the
additional multiple-zero obligation arithmetically. It proves negative
four-prime supply at the original positive-cosine phase and pays the same
exponential head classes from above, including their boundary errors.
The resulting `eventually_core_full_exponential_ceiling` keeps one exact
signed rest and one eighth of the negative supply. It is not yet the
independent whole-sum numerical ceiling required by
`false_of_joint_cofinal_bounds`.

The [six-prime head payment](zeta-riesz-six-prime-head.md) extends both
comparisons to the entire six-prime population containing a prime at most
`N^2`. Both coefficient signs are paid, including radial boundary labels.
The terminal `eventually_core_full_floor` and `...full_ceiling` retain one
sixteenth of their respective original supply, all favorable selected
observations and one exact signed rest. They replace the previous spending
ledger; they do not add a second supply or prove either whole-sum target.
Every prime in the remaining six-prime population exceeds `N^2`.

The same [six-prime payment](zeta-riesz-six-prime-head.md#keep-the-minimum-logarithm-before-summing)
now reaches a fixed exponential head. The minimum logarithm is retained
across all five cofactor factors before using literal fractional prime
mass bounds. `ZetaRieszSixPrimeExponentialHead.eventually_core_full_floor`
and its ceiling counterpart pay every label with a prime
`p<=floor(exp(epsilon*N))`, including boundaries. Previous head widths
are retained; the same supply still leaves one sixteenth. Every prime
of an unpaid six-prime label has `log p>epsilon*N`. Neither independent
whole-sum endgame bound follows from this component payment.

The [negative five-prime head payment](zeta-riesz-five-negative-head.md)
now adds the previously unpaid coefficient sign. A minimum-prime fractional
bound pays its fixed exponential head from another one thirty-second of
the SAME supply, retaining all old payments and one thirty-second unused.
`ZetaRieszFiveNegativeHead.eventually_core_full_floor` and its ceiling
counterpart include all original boundary failures and one exact signed
rest. Both five-prime signs now have only exponentially large factors in
the unpaid nonzero population. These results have no zero or simplicity
assumption. The remaining signed populations must still satisfy the two
independent whole-sum bounds; the multiplicity issue is not erased.

The [complementary-divisor refinement](zeta-riesz-complement-window.md)
now sharpens the higher even-count costs on every subset of this original
signed rest. At the reflected one-third cutoff, a middle-rank subset and
its complement cannot both survive. The resulting general LYM bound gives
literal coefficient intervals `[-15,13]` at eight primes, `[-49,56]` at
ten and `[-210,186]` at twelve, in least-prime units. Both original cosine
orientations, all favorable observations and all other counts remain.
No new supply is spent and neither cofinal numerical endgame bound follows.
