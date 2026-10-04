# Signed Selberg endpoint audit on the unchanged balanced mask

The common-mask adjacent-order identity is preserved. Its three terms do
not, by themselves, give a uniform bounded signed contribution on that
mask. The new local Lean leaf proves growth for the **actual prime sum**
at the fixed test height (y=19\pi), including the actual factorial-prefix
correction. This is a no-go for an isolated, uniform all-height payment;
it is **not** a counterexample to the desired exposed-zero ceiling or to
a joint bound using the retained signed complement.

## Exact object and result

The existing mask is unchanged:

\[
\mathcal B_N=\{(p,q):p,q\text{ prime},\quad
N<\log p\le N+1<\log q\le N+2\}.
\]

The adjacent-order leaf already proves the requested identity on this one
common mask, with the exact moving (L_N), full complex phase and the
imbalance expanded into individual prime-order shifts. No native mask at
(N+1) is substituted. The two literal factorial prefixes retain their
exact (13N/32) endpoint and existing geometric payment.

For every (1/2<u\le10001/20000), the new theorem
`eventually_balanced_signed_growth` proves

\[
\operatorname{Re}\left[u^{N+1}\sum_{(p,q)\in\mathcal B_N}
\operatorname{selbergDefect}(u,N,pq)K_N(3/2+i19\pi,pq)\right]
\ge\frac{u}{120000}\frac{(2u)^N}{(N+1)^2}
\]

eventually. Its left side tends to (+\infty).
`balanced_literal_prefix_tendsto_atTop` proves the same divergence when
the defect is replaced by the actual
`prefixCoefficient u N (p*q) - selbergCoefficient (p*q)`.
`not_frequently_native_balanced_prefix_ceiling` excludes every constant
cofinal ceiling for this isolated literal contribution on the **original
dyadic schedule**.

These statements do not identify (19\pi) as a zero ordinate. They do not
bound the full `prefixPairDefect`, `joinedPhysical`, or its signed rest.
The original exposed-zero hypothesis may still supply information that
this uniform test does not use.

## Why neighboring orders do not finish the cancellation

At integer (N), the actual phase factors exactly as

\[
\cos(y\log(pq))=
\sin(y(\log p-N))\sin(y(\log q-N-1))
-\cos(y(\log p-N))\cos(y(\log q-N-1)).
\]

For (y=19\pi), the sine integral on each unit log window is (2/y)
and the cosine integral is zero. Qualitative PNT, used only at a fixed
relative accuracy, proves a positive phase contribution for the entire
literal box:

\[
N^2\sum_{\mathcal B_N}\frac{\cos(y\log(pq))}{pq}\ge\frac1{1000}.
\]

The exact common saddle weight is

\[
F_N(T)=e^{-(T-2N)/2}(T/(2N))^N,
\qquad B_N(L)=3N-4N^2/L.
\]

The joined three-order coefficient satisfies

\[
\left|\Delta_N(p,q)F_N(\log(pq))-B_N(L_N)\right|\le26,
\qquad B_N(L_N)\ge N/10.
\]

Thus the bounded error cannot cancel the positive endpoint phase. The
factorial kernel restores the superunit factor ((2u)^N). The proof
joins all three order terms before estimating this relative error; it
does not price them separately or norm-pay the selected source.

A fixed finite mesh is an exact partition used in the PNT proof and is
summed out. It introduces no new paid population, sampling hypothesis,
shrinking interval, or exponentially accurate prime-density assumption.
The PNT entry threshold is existential. The scalar thresholds in the
proof alone do not certify it numerically.

## Optional numerical regression and local validation

`scripts/probe_riesz_selberg_signed_boundary.py` records six scalar log
geometries and six ball controls at 360 bits. The separate 420-bit
consumer replays 30 ball comparisons, checking relative enclosure widths.
These rows contain no actual primes or zeros.

The producer separately records floating continuum quadrature at orders
256, 640, 1536, 4096, 8192 and 65536. It retains the **exact moving floor
and successor in (L_N)**. Raw magnitudes are stored logarithmically and
source-normalized values are also recorded. Every quadrature row is
explicitly uncertified. The limiting model shape is approximately

\[
(3+2/\log u)\,4/(19\pi)^2\simeq1.28202\times10^{-4}
\]

at (u=10001/20000). This diagnostic motivated the proof but provides no
native entry order, arithmetic carrier bound, or zero-exclusion result.

The local leaf/checker use warning-as-error, the 14 namespace linters and
a transitive axiom audit. Only `propext`, `Classical.choice` and `Quot.sound`
are permitted. The audit preserves all 360 earlier source/artifact pins.
No root import, public explorer metadata, broad gates, commits, pushes
or subagents are part of this slice.

## Remaining target

No new credit toward the fixed (42/25) ceiling or the independent simple
floor is claimed. The whole joined carrier remains open. Stop treating
adjacent-order algebra on the isolated balanced mask as a uniform payment.
The next valid estimate must retain the signed native mask complement or
use the exposed-zero hypothesis before imposing a boundedness conclusion.
