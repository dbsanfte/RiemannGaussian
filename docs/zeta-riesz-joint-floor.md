# The direct joint floor is sufficient

The latest component estimate is
[`ZetaRieszSmallPrimeCompensation.eventually_compensated_core_floor`](zeta-riesz-small-prime-compensation.md):
one actual positive four-prime supply pays both a fixed balanced triple
band and the entire three-prime head containing a prime at most `N^2`.
Both positive triple credits, one quarter of that supply and the signed
complement remain, with only a geometric radial-edge error. The complement
also has the exact four- and five-prime debit refinements. The numerical
joint floor stated below remains open.

The endgame does not require separate decay of the retained packet and its
complement. It requires a lower bound for their signed sum at arbitrarily
late indices. `ZetaRieszJointFloor` checks this for the existing literal
expressions, without introducing a new carrier.

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
this inequality**. An eventual floor, positivity, decay to zero and bounds
on either component separately would all be stronger than necessary.
The allowance `79/1000` is also larger than the previous sufficient
`3/40`, reducing the required accuracy of a joint estimate. No assumption
that the error is nonnegative is needed.

For orientation, direct high-precision evaluation gives source values
approximately `-0.07992934` at `u=1/2` and `-0.07987180` at `u=0.50005`.
These endpoint diagnostics do not establish a uniform bound; the Lean
rational inequalities supply that bound over the entire interval.

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
