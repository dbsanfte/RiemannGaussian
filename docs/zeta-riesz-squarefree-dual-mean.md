# A linear squarefree mean at every cutoff

Lean now proves a uniform linear second-moment bound for the actual
squarefree Möbius cutoff response, then transfers it to both sides of a
literal signed prime-fibre sum. The counting budget covers every cutoff
and cofactor count. The correlated prime-weight energy and its combined
period cost remain open; neither whole endgame threshold is proved.

For the existing sharp response

\[
M_R(n)=\sum_{\substack{d\mid n\\1\le d\le R}}\mu(d),
\]

squarefree nonunit labels satisfy the exact reflection

\[
M_R(n)=-\mu(n)M_{\lfloor(n-1)/R\rfloor}(n),\qquad R>0.
\]

The `n-1` is essential: the complementary divisor inequality is strict.
This includes primes and retains boundary labels.

## One rounding error per divisor pair

Expanding the reflected square before estimating the integer counts
leaves, for each pair `d,e`, the single interval

\[
R\max(d,e)<n\le X,\qquad \operatorname{lcm}(d,e)\mid n.
\]

Its counting error relative to interval length divided by the least
common multiple is at most one. Thus the total finite error is
`floor(X/R)^2`. The main term retains the signed Möbius cross terms;
it is a sum of the existing uniformly bounded sharp lcm quadratics.

Consequently, for arbitrary squarefree `S` in `(1,X]`, Lean proves

\[
\sum_{n\in S}M_R(n)^2\le E X+\lfloor X/R\rfloor^2.
\]

Combining this with the existing direct bound `E' X+R^2` closes every
cutoff range. If `R^2<=X`, use the direct estimate; otherwise
`floor(X/R)^2<=X`. One proved, unevaluated constant `C>0` therefore gives

\[
\boxed{\displaystyle \sum_{n\in S}M_R(n)^2\le C X
\quad\text{for every }R>0.}
\]

The earlier cubic complementary bound remains available in
`ZetaRieszSquarefreeDualMean`; its intermediate-cutoff limitation has now
been removed by `ZetaRieszSquarefreeUniformMean`. No external sieve,
zero, simplicity, share, or fixed-count hypothesis enters this result.

## Both Riesz cutoffs remain together

For common endpoints `A<=B`, the existing positive mixture of sharp
prefixes gives

\[
\sum_{n\in S}(\mathcal R_B(n)-\mathcal R_A(n))^2
\le (B-A)^2 C X.
\]

Arbitrary real correlated weights then satisfy `-K<=J<=K`, where

\[
J=\sum_{n\in S}w_n(\mathcal R_B(n)-\mathcal R_A(n)),\qquad
K^2=\left(\sum_{n\in S}w_n^2\right)(B-A)^2 C X.
\]

There is no superlinear counting penalty. The displayed weight energy
still needs an estimate. General endpoints are fixed across labels;
the theorem does not cover arbitrary label-dependent endpoints.

The literal prime carrier has a useful exact application. For a squarefree
composite cofactor `a`,

\[
\operatorname{response}(L,\log p+\log a,a)
=-\mu(a)\bigl(\mathcal R_L(a)-\mathcal R_{L-\log p}(a)\bigr).
\]

For each fixed marked prime `p`, both reflected endpoints are common to
the cofactor population. `exists_literal_prime_fibre_bounds` therefore
bounds the real part of the sum of the **original** `residualCoefficient`
times `zetaPrimeLogKernel`, retaining phase, factorial and allocation
weights. The squared budget is

\[
\left(\sum_{a\in S}
 \left(\frac{\operatorname{signedPrimeWeight}(a,p)}a\right)^2\right)
(\log p)^2 C X.
\]

All eligible cofactor counts and arbitrary selected populations are
allowed, with `p` prime and coprime to every selected cofactor. This is an
independent literal inequality, without a raw-prime-bound premise. It is
not a source-small bound: the weight energy and total over marked primes
remain unpaid. Joint prime-period cancellation and its cutoff correction
still require control, preserving disjointness of previously paid sectors.
The whole `-79/1000` floor and `3/2` ceiling remain open.

## Finite diagnostic

The optional `scripts/probe_riesz_squarefree_dual.py` tests reflection
using exact integer Möbius prefixes. At `X=200000`, `R=10000`, the old
normalized counting error is `500`; the new reflected square error is
`0.002`. The actual squarefree second moment divided by `X` is `0.32244`;
the separate main-term constant is still present. The probe checks
several cutoffs, including both sides of the square-root transition.

These computations are diagnostic, not a prime-phase or zeta certificate.
They stay outside ordinary CI and are not used by the Lean proofs.

Sources:
[exact reflection and initial bounds](../RiemannGaussian/ZetaRieszSquarefreeDualMean.lean),
[uniform bound and literal application](../RiemannGaussian/ZetaRieszSquarefreeUniformMean.lean).
Audit: [riesz-squarefree-dual-mean-audit.json](riesz-squarefree-dual-mean-audit.json).
