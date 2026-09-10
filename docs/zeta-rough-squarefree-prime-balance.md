# What completing the rough squarefree divisor sum actually proves

The proposed divisor--cofactor completion has a precise limitation. Lean
proves that its **entire completed signed prefix decays at the source
scale**, but the completion restores ordinary primes. Those primes carry
the full hypothetical-zero source. This is an audit of that proposed
shortcut, not a new zero exclusion or a proof that every bilinear method
must fail.

All theorem names below are in
[ZetaRoughSquarefreePrimeBalance.lean](../RiemannGaussian/ZetaRoughSquarefreePrimeBalance.lean).
The preceding [rough squarefree source](zeta-rough-squarefree-signed-source.md)
and all its exact phase and reflection identities remain available.

## The completion changes the arithmetic support

Let `S` be a finite set of primes and `D >= 1`. Write

\[
b_D(n)=-\sum_{\substack{d\mid n\\1\le d\le D}}\mu(d)\log(n/d),
\qquad
B_{D,S}(n)=\mathbf1_{\mathrm{squarefree}(n)}
 \mathbf1_{\forall p\in S,\ p\nmid n}\,b_D(n).
\]

The original rough squarefree composite coefficient `a_{D,S}` satisfies
the exact identity

\[
a_{D,S}(n)=B_{D,S}(n)+
 \mathbf1_{\mathrm{prime}(n),\ n\notin S}\log n.
\]

This is `zetaRoughSquarefreeCoefficient_eq_prefix_add_prime`, with no
asymptotic premise. In particular, on each ordinary prime outside `S`,
`B_{D,S}(p)=-log(p)` for every positive divisor cutoff. Lean checks this
separately in `zetaRoughSquarefreePrefixCoefficient_prime`.

Thus summing over all squarefree coprime products would restore a real
prime contribution. It is not permissible to apply a bound for that
completed sum to the composite restriction without paying for those
primes.

## Independent control of the entire completed prefix

The complete prime-avoidance transform retains every signed intersection:

\[
B_{D,S}(n)=\sum_{W\subseteq S}(-1)^{|W|}
 \mathbf1_{\mathrm{squarefree}(n),\ \prod W\mid n}\,b_D(n).
\]

`hasSum_zetaRoughSquarefreePrefixFilter` transports this identity through
the full genuinely convergent series with the original complex polynomial
kernel. The divisor cutoff, ordinate, polynomial coefficients, and all
overlaps remain present.

For any fixed `|y|>1` and `0<r<1`, if every selected prime is at most `R`,
`exists_zetaRoughSquarefreePrefixFilter_bound` proves

\[
|B_{D,S,p,N}(3/2+iy)|
 \le C_{y,r}D e^{4\sqrt R}r^{-N}\sum_k|p_k|r^{-k}.
\]

The constant is independent of `D`, `N`, `R`, the selected prime family,
and the polynomial. This uses the previously proved uniform squarefree
intersection bound, including its shared-prime correction. No estimate
for the remaining ordinary-prime sum is assumed.

At every hypothetical right-half zero, set

\[
u=3/2-\Re\rho,\quad q=u^{-1/4},\quad
D_N=\lfloor q^N\rfloor,\quad
R_N=\lfloor N\log(q)/8\rfloor^2,
\quad S_N=\{p\le R_N:p\text{ prime}\},
\]

and use the actual pole-jet polynomial. With
`lambda=2*sqrt(u)/(1+sqrt(u))<1`, Lean proves

\[
|u^{N+1}B_N|\le C_\rho\lambda^N\longrightarrow0.
\]

The entry points are
`exists_zetaRightHalfRoughSquarefreePrefix_error_bound` and
`tendsto_zetaRightHalfRoughSquarefreePrefixFilter`.

## The ordinary-prime correction carries the source

Let `P_N` be the actual filtered sum of `log(p)` over ordinary primes
outside `S_N`, with the full original complex kernel. Genuine convergence
and the exact series identity give

\[
A_N=B_N+P_N.
\]

The earlier theorem gives `u^(N+1)*A_N -> -m_rho`. The independent prefix
bound therefore proves

\[
u^{N+1}P_N\longrightarrow -m_\rho.
\]

This is `tendsto_zetaRightHalfRoughPrimeFilter`. The completed prefix can
be small because its prime and composite pieces cancel each other.
Its smallness does not imply smallness of either piece.

The comparison also holds at finite moment order. If `F_N` is the actual
retained complex Fourier carrier and `E_N` is the already proved complete
physical/Fourier localization allowance, then

\[
|u^{N+1}(P_N-F_N)|\le C_\rho\lambda^N+E_N.
\]

Using the exact identity `Re(F_N)=-2W_N` gives

\[
\left|-\frac{u^{N+1}\Re P_N}{2}-u^{N+1}W_N\right|
\le\frac{C_\rho\lambda^N+E_N}{2}\longrightarrow0.
\]

Both comparisons are compiled as
`exists_zetaRightHalfRoughPrime_fourier_error_bound` and
`exists_zetaRightHalfRoughPrime_reflection_error_bound`.

## Decision and remaining obligation

Do not pursue a bound for the completed divisor sum as a stand-alone
contradiction mechanism: that bound is now proved, and it leaves an
ordinary-prime correction with the full source. An exact bilinear rewrite
could still be useful if it supplies a new signed estimate for the
composite restriction itself. No such estimate is established here.

The outstanding goal remains one independently proved strict bound
`u^(N+1)*W_N <= m_rho/2 - epsilon`, for some positive epsilon at arbitrarily
late orders, for every hypothetical right-half zero. This slice does not
improve that bound or exclude any additional zero. The all-height edge
margin remains `1/(10 log(|t|+2))`; RH is open.
