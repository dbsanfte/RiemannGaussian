# Sharper simplicity payment of the unchanged ceiling

The full independent `42/25` ceiling on the original fixed candidate strip
remains **open**. This local slice proves a larger simplicity layer and
transfers it to the same `joinedPhysical` carrier under the original
exposed-source hypotheses. It changes no arithmetic carrier or mask.

Put `L = log(abs(Im rho) + 2)`. The checked result is

\[
1-\Re\rho\le
\min\!\left(\frac1{20000},\frac6{L+60000}\right)
\quad\Longrightarrow\quad m_\rho=1.
\]

This holds at every height with no exposure or simplicity assumption. It
excludes **multiple** zeros in the layer; it does not exclude simple zeros
or prove an all-zero-free region.

The entire candidate width is paid for multiplicity through **log-height
60000**, extending the preceding 50000 plateau. Above 60000 the width is
at least `10/9` times the preceding all-height simplicity width. The theorem
`old_width_le` preserves the preceding payment at every ordinate.

The source of the improvement is a signed moment calculation, not a new
prime-cancellation hypothesis. At `x = 2701/2000`, write

\[
M_n(x)=\int_0^\infty t^n e^{-t^2-xt}\,dt.
\]

The existing exact identities

\[
2M_1+xM_0=1,\qquad
2M_{n+2}+xM_{n+1}=(n+1)M_n
\]

and `M_16 >= 0` imply `M_0 >= 59/125`. The recurrence coefficients are
kept together; no absolute values are taken. Exact homogeneity gives

\[
G_4(2701/1000)\ge\frac{59}{250}.
\]

No quadrature is used in that Lean proof. The optional scalar probe checks
the signed rational recurrence independently against the closed Gaussian
formula and direct moment quadrature.

For `L >= 50000`, set `q = (L+60000)/1000000`. The depth `6/(L+60000)`
has normalized damping `27/10`; the existing positive shift adds `1/1000`.
The selected multiplicity-two source, including its cotangent correction
and nonnegative Poisson reserve, is at least `67000*q - 4`. The complete
existing arithmetic budget is at most

\[
36922q+\frac L{35}+57\log L+840.
\]

The global tangent `log L <= L/200000 + 12` proves the uniform surplus

\[
36922q+\frac L{35}+57\log L+840+\frac{236431}{700}
\le 67000q-4.
\]

That margin is in Gaussian detector units. It is not a Riesz cancellation
credit, a proof percentage or a native entry-order certificate.

`eventually_joinedPhysical_ceiling_in_boundary_layer` combines the
independent simplicity theorem with the already-proved exposed source
limit. It gives the same carrier's eventual real ceiling `< 42/25` in
the larger layer. All factorial orders, the phase, count, moving length,
allocation masks and the single prime-square diagonal are retained.

For any surviving multiple candidate in the original strip, the exact
unpaid location is now

\[
L>60000,\qquad
\frac6{L+60000}<1-\Re\rho\le\frac1{20000}.
\]

The prior all-family positive-budget no-go is unchanged. This improvement
does not make that method an all-height fixed-strip closure strategy. The
remaining ceiling requires actual signed arithmetic information beyond
the complete positive allowance. The independent simple-zero floor and
RH also remain open.

The leaf and its namespace/transitive-axiom check pass locally: 27 theorem
declarations use only standard Lean axioms, and all 14 namespace linters
pass. The optional probe replays 16 exact scalar height rows. It samples
no primes, actual zeros or carrier arrays. Prior proof/probe snapshots are
preserved. No root registration, wider checks, commit, push or public
README/explorer update is part of this slice.

Proof: [ZetaRieszCeilingSharpMultiplicity.lean](../RiemannGaussian/ZetaRieszCeilingSharpMultiplicity.lean).
Scoped check: [CheckRieszCeilingSharpMultiplicity.lean](../scripts/CheckRieszCeilingSharpMultiplicity.lean).
Optional scalar probe: [probe_riesz_ceiling_sharp_multiplicity.py](../scripts/probe_riesz_ceiling_sharp_multiplicity.py).
Audit: [riesz-ceiling-sharp-multiplicity-audit.json](riesz-ceiling-sharp-multiplicity-audit.json).
