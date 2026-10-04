# Signed credits after joining the full prime-pair coefficient

The independent cofinal target is unchanged:

\[
\operatorname{Re}\mathrm{prefixPairDefect}_{N_j}
\le \frac{399}{5000}+o(1).
\]

[`ZetaRieszJoinedPairSignCover`](../RiemannGaussian/ZetaRieszJoinedPairSignCover.lean)
proves independent signed credits for two broad populations in this same
literal sum. It does **not** prove the target bound, quantify a cofinal
population credit, or exclude a zero.

## The coefficient tested

For distinct primes \(p<q\), put \(x=\log q\), \(z=\log p\),
\(T=x+z\), and \(L=\mathrm{length}(u,N)\). After both factorial prefixes
and the full Selberg subtraction are joined, the real coefficient is

\[
g_N(x,z)=\mathrm{prefixLogCoefficient}(N,L,x,z)
              +\frac{2xz}{T}.
\]

Writing \(F_N(a)\) for the exact binomial prefix with total order \(N+1\)
and integer cutoff \(\lfloor13N/32\rfloor\), its ratio is

\[
\frac{g_N(x,z)}{T}
=1-\frac{T}{L}
-\frac{(L-x)F_N(z/T)+(L-z)F_N(x/T)}{L}
+2\frac{xz}{T^2}.
\]

The Selberg term is part of the existing joined atom, not another free
credit. No count or factorial endpoint is removed before this sign test.

## Two uniform sign regions

For \(N\ge65536\), \(1/2\le u\le10001/20000\), and
\(39N/20\le T\le203N/100\), Lean proves:

| Geometry | Bound for the full coefficient | Favorable actual phase |
| --- | --- | --- |
| \(x/T,z/T\ge12/25\) | \(g_N\ge T/50\) | \(\cos(y\log n)\le0\) |
| \(5/8\le x/T\le11/16\) | \(g_N\le-T/200\) | \(\cos(y\log n)\ge0\) |

These are `balanced_coefficient_lower` and `owner_coefficient_upper`.
The proof uses the existing rational moving-length enclosure and exact
binomial-tail bounds. It needs no exposed-zero or prime-density hypothesis.

The finite set `favorableLabels` intersects these conditions with the
**original** nonprime complete-period support and actual semiprime labels.
Physical, radial-endpoint and period masks remain. For every retained
favorable label the full atom obeys

\[
\operatorname{Re}\bigl(g_N K_N(3/2+iy,n)\bigr)
\le-\frac{\log n}{200}\,
       \lVert K_N(3/2+iy,n)\rVert\cos^2(y\log n).
\]

The phase is literal, without phase freezing, completion, or a positive
`abs(cos)` allowance for the main sum.

## Preserve the exact credit in the floor

Let \(S\) denote the existing retained nonprime complete-period labels and
\(F\subseteq S\) the favorable labels. The rational benchmark is

\[
\mathrm{signCredit}_N
=\frac{u^{N+1}}{200}
 \sum_{n\in F}\log n\,\lVert K_N(3/2+iy,n)\rVert
                    \cos^2(y\log n)\ge0.
\]

The full credit retained by the ledger is instead

\[
\mathrm{exactSignCredit}_N
=-\operatorname{Re}\left[
u^{N+1}\sum_{n\in F}
(\mathrm{prefixCoefficient}_N(n)-\mathrm{selbergCoefficient}(n))
K_N(3/2+iy,n)\right].
\]

Lean proves `signCredit <= exactSignCredit` and the exact identity

\[
\operatorname{Re}\mathrm{prefixPairDefect}_N
=\operatorname{Re}\left[
u^{N+1}\sum_{n\in S\setminus F}
(\mathrm{prefixCoefficient}_N(n)-\mathrm{selbergCoefficient}(n))
K_N(3/2+iy,n)\right]-\mathrm{exactSignCredit}_N.
\]

`eventually_native_exact_credit_floor` inserts this identity into the
original whole-core floor with its existing Selberg and prefix budgets
spent once. It leaves the entire favorable mass available for joint
cancellation. Replacing it by the smaller benchmark can lose more than
the desired source-scale margin; the benchmark is not permission to discard
the excess or to call that family paid at source scale.

The next required estimate is a bound of `399/5000 + o(1)` on **the signed
rest minus the exact credit together**. Neither a density/lower bound for
that credit nor a numerical bound for this combined quantity has been
proved here. A finite favorable set can be empty. The previous continuous
positive-density countertest and all other no-go audits remain available.

## Optional exploration and focused checks

[`probe_riesz_joined_pair_profile.py`](../scripts/probe_riesz_joined_pair_profile.py)
evaluates 90 coefficient-grid cases at three large native orders, the two
radius endpoints, three total-log slopes and five owner shares. It uses the
certified moving-length **lower endpoint**, records the remaining enclosure
width, and evaluates the integer binomial prefix numerically. The sampled
balanced minimum is approximately `0.03430`; the sampled higher-owner
maximum is approximately `-0.009893`.

Those numbers are ratios of coefficients to total log. They are not actual
prime sums, phase/count densities, a cofinal certificate, or values in units
of the `0.0798` target. The Lean inequalities do not depend on the probe.

The strict local leaf build and
[`CheckRieszJoinedPairSignCover`](../scripts/CheckRieszJoinedPairSignCover.lean)
pass. The latter lints the namespace and audits all 37 theorem declarations,
including private/generated helpers, against only the standard Lean axioms.
All 211 preceding Riesz audit pins were checked before the guide update;
only guide/dependent-audit hashes are refreshed afterward. Proof and numerical
snapshots remain unchanged. The scoped audit is
[`riesz-joined-pair-sign-cover-audit.json`](riesz-joined-pair-sign-cover-audit.json).

This slice is local, with no root registration, wider gates, CI run, commit
or push. The global floor and higher-multiplicity ceiling remain open.
