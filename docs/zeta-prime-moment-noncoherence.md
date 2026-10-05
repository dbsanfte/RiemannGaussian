# A structural non-coherence criterion for the campaign strip

The canonical endpoint is the weakest strip-wide arithmetic premise:

\[
\forall\;1/2<u\le10001/20000,\quad \forall y\in\mathbb R,\quad
\forall m\in\mathbb N_{>0},\qquad a_k(u,y)\not\longrightarrow-m.
\]

[`campaign_noncoherent_iff_nonvanishing`](../RiemannGaussian/ZetaPrimeMomentNoncoherenceStrip.lean)
proves this premise equivalent to nonvanishing on `Re(s)>=19999/20000`.
[`campaign_nonvanishing_of_noncoherent`](../RiemannGaussian/ZetaPrimeMomentNoncoherenceStrip.lean)
is the direct conditional endpoint. Exposure is selected internally in the
contradiction; neither exposure nor a Riesz floor is an input premise.
Block deviation is only a sufficient way of supplying non-coherence.
No independent all-height arithmetic premise has been proved.

The Riesz branch is preserved as a reduction. Further internal rearrangements
are paused unless they introduce new arithmetic information. The new
[Chebyshev-error investigation](zeta-prime-moment-error-frontier.md) studies
the literal prime moments directly and separates finite-height coverage
from the open all-height non-coherence theorem.

There is a necessary correction to the proposed pointwise implication.
The converse says

\[
a_k(u,y)\longrightarrow-m\quad\Longrightarrow\quad
\zeta(3/2-u+iy)=0,\qquad m\in\mathbb N_{>0}.
\]

Its contrapositive is **nonvanishing implies non-coherence**. It does not
prove that pointwise non-coherence implies nonvanishing. A zero need not
be exposed; closer competing singularities can obstruct convergence of
the moment sequence at that candidate's radius. The converse alone does
not rule out that possibility. The pointwise reverse endpoint therefore
retains a forward zero-to-coherence premise explicitly.

## Exact moving blocks

For the actual complete ordinary-prime sequence from
[`ZetaPrimeMomentCoherence`](../RiemannGaussian/ZetaPrimeMomentCoherence.lean),
define

\[
I_N=\left[\frac{13N}{32},\frac{19N}{32}\right]\cap\mathbb N
 =\left\{\left\lceil\frac{13N}{32}\right\rceil,
       \ldots,\left\lfloor\frac{19N}{32}\right\rfloor\right\},
\qquad
E_N(u,y,m)=\frac1{|I_N|}\sum_{k\in I_N}|a_k(u,y)+m|^2.
\]

The lower endpoint is rounded **up**, exactly as required by the literal
rational interval. Empty-block averages are zero; the blocks are proved
nonempty for `N>=32`. Every member of the moving block tends to infinity
uniformly over the block.

[`tendsto_blockDeviation_of_tendsto`](../RiemannGaussian/ZetaPrimeMomentNoncoherence.lean)
proves for any complex sequence, including these actual prime moments,

\[
a_k\longrightarrow-m\quad\Longrightarrow\quad E_N\longrightarrow0.
\]

Consequently either of the following rules out that particular limit:

- `0 < limsup E_N`;
- there is an `epsilon>0` such that `E_N>=epsilon` on cofinally many blocks.

The second formulation also detects unbounded deviation and avoids using
the default real limsup of an unbounded sequence. Its constant may depend
on `u`, `y` and `m`; no uniform height estimate is required. Neither a
finite numerical sample nor a bounded-order certificate supplies the
cofinal premise.

`noncoherent_of_nonvanishing` is the genuine contrapositive of
`exists_zero_multiplicity_of_tendsto`, for `0<u<1`.
`nonvanishing_of_noncoherent_of_forward` and the two block variants make
the missing pointwise forward hypothesis visible rather than assuming it.

## A valid zero-free bridge with no exposure premise

The repo already proves that any right-half zero leads to an exposed zero
**at least as far right**, without requiring a rightmost zero. This allows
a stronger arithmetic premise to give the requested zero-free conclusion.
For `U<1`, require

\[
\forall\ u\in(1/2,U],\ \forall y\in\mathbb R,\ \forall m\in\mathbb N_{>0},
\qquad a_k(u,y)\not\longrightarrow-m.
\]

[`nonvanishing_of_strip_noncoherent`](../RiemannGaussian/ZetaPrimeMomentNoncoherenceStrip.lean)
then gives

\[
\forall s\in\mathbb C,\qquad
\Re s\ge\frac32-U\quad\Longrightarrow\quad\zeta(s)\ne0.
\]

The proof selects an exposed zero only after assuming a zero for
contradiction. Its radius is still in `(1/2,U]`, so the strip-wide premise
applies. The existing forward theorem supplies convergence to minus its
positive analytic multiplicity, contradicting non-coherence. Exposure is
**not** a premise of the zero-free criterion. No Riesz floor appears in
any premise, and no new arithmetic cancellation hypothesis is treated as
proved. The converse gives the reverse global direction as well:
`strip_noncoherent_iff_nonvanishing`.

Both block-deviation formulations have direct strip endpoints. In
particular
[`campaign_nonvanishing_of_block_limsup`](../RiemannGaussian/ZetaPrimeMomentNoncoherenceStrip.lean)
proves the implication

\[
\left[
\forall\frac12<u\le\frac{10001}{20000},\ \forall y,\ \forall m>0,
\quad\limsup_{N\to\infty} E_N(u,y,m)>0
\right]
\quad\Longrightarrow\quad
\left[
\Re s\ge\frac{19999}{20000}\Rightarrow\zeta(s)\ne0
\right].
\]

The cofinal-positive-gap variant has the same conclusion. These are
sufficient corollaries of the canonical direct endpoint; a positive block
limsup is not required by that endpoint. A block gap at one candidate
height/radius alone does not exclude a zero there using the converse theorem.

## Local validation

The two new modules are checked with warnings as errors. The scoped
[`CheckPrimeMomentNoncoherence`](../scripts/CheckPrimeMomentNoncoherence.lean)
gate runs both namespace linters and checks transitive axioms for every
declaration, including private helpers. The
[local audit](prime-moment-noncoherence-audit.json) records the exact scope.

All earlier coherence proofs, positive results, no-go audits and semiprime
work are preserved. The [terminal checkpoint](zeta-riesz-terminal.md)
registers these modules in the ordinary root and public explorer; its
[publication audit](prime-moment-terminal-publication-audit.json) records
the wider gates separately from the original scoped validation. No
exhaustive numerical certificate verification is needed for these proofs.
