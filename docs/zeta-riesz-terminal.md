# Riesz reduction: terminal checkpoint

The Riesz branch is frozen as a checked reduction. It does not prove RH.
The remaining all-height task requires new information about actual primes,
not another rearrangement of this carrier.

Set `s0=3/2+iy`, `rho=s0-u` and

\[
a_k(u,y)=\frac{u^{k+1}}{k!}\sum_p (\log p)^{k+1}p^{-s_0},\qquad
E_k(c)=\frac1{k!}\int_0^\infty
 (e^{-t}\psi(e^t)-1)t^ke^{-ct}\,dt.
\]

For every permitted fixed radius `1/2<u<=10001/20000`, every fixed height
and every positive integer multiplicity, the checked logical endpoint is

\[
\boxed{\begin{gathered}
\zeta(s)\ne0\quad\text{for every }\Re s\ge19999/20000\\
\Longleftrightarrow\quad
\text{no campaign prime-moment sequence converges to }-m\\
\Longleftrightarrow\quad
\text{no corresponding centered factorial transform of }\psi-x
\text{ converges to }-m.
\end{gathered}}
\]

The last statement uses, at `|y|>=54`, the exact sequence
`u^(k+2)*(s0*E_(k+1)(s0-1)-E_k(s0-1))`. Independent verified zero
completeness handles smaller heights. Main-density and proper-power terms
vanish independently in the transform comparison. All integrals remain
in their proved Euler domain; no literal prime series is asserted to
converge through that boundary.

[`campaign_nonvanishing_iff_noPersistentError`](../RiemannGaussian/ZetaPrimeMomentTerminal.lean)
composes exposed-zero selection, the forward source, the converse with
exact multiplicity and the actual Chebyshev-error identity. Exposure is
internal to selection, not an endpoint premise. A diagnostic
`-m*x^rho/rho` component produces exactly `-m`; no one-component
asymptotic for actual `psi` is assumed.

The audits close these **specific mechanisms**, not every possible theorem
in the named areas:

| Tested mechanism | Recorded obstruction |
| --- | --- |
| Cutoff and adjacent-order repartition | The multiplicity-square source returns in the transition or mask correction. |
| Saddle-matched two-center comparison | Comparison plus curvature retains the original coherent source. |
| Scalar multi-height/Stechkin comparison | Native quadratic coefficients have both signs; all-safe auxiliary shifts impose an unpaid exponential cost. |
| PNT/subexponential error envelopes | A positive continuous coherent model passes every sublinear logarithmic-loss envelope. |
| Generic Euler-product/divisor structure | Generalized prime systems can retain zero-driven components; this structure alone does not distinguish actual integer primes. |

Proofs, exact domains, numerical-control limitations and primary references
are in the [arithmetic-frontier audit](zeta-prime-moment-error-frontier.md)
and [publication audit](prime-moment-terminal-publication-audit.json).

[Finite-height radius coverage](../RiemannGaussian/ZetaPrimeMomentRegionCoverage.lean)
is a separate engineering track. Its checked logarithmic ceiling is 2000;
stronger published analytic proofs remain import tasks. The all-height
non-coherence premise remains open. Main research now returns to
[global Gaussian/Weil and Suzuki arithmetic](gaussian-suzuki-pivot.md).
