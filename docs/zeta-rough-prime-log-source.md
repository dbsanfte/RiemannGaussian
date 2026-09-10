# Small-prime logarithmic decay and the large-prime tail

The new independent estimate controls the squared Möbius mask's complete
small-prime logarithmic contribution. Its subtraction leaves a weight
supported on integers with a large prime and a large cofactor. Keeping
the exact source parameter also bounds its complete cubic head. The
remaining strict signed upper bound and RH are unproved.

Use the unchanged definitions

\[
u=3/2-\Re\rho\in(1/2,1),\qquad q=u^{-1/4},\qquad
D_N=\lfloor q^N\rfloor,
\]

and retain the original sieve \(S_N\), polynomial \(p_\rho\), complex
kernel \(K_N(n)\) and multiplicity \(m_\rho\). Write

\[
M_D(n)=\sum_{\substack{d\mid n\\1\le d\le D}}\mu(d),\qquad
\ell_D(n)=\sum_{\substack{a\mid n\\a\text{ prime},\ a\le D}}\log a,
\qquad
h_D(n)=\sum_{\substack{a\mid n\\a\text{ prime},\ D<a}}\log a.
\]

For squarefree \(n\), \(\ell_D(n)+h_D(n)=\log n\). All these
quantities remain real before multiplication by the complex kernel.
Let \(b_S(n)\) be \(\log n\) on rough squarefree composites and zero
elsewhere. The existing square coefficient is \(M_D(n)^2b_S(n)\).

The complete correction is

\[
E_{D,S}(n)=\mathbf1_{\{n\text{ squarefree and }S\text{-rough}\}}
M_D(n)^2\ell_D(n).
\]

Its ordinary-prime values vanish exactly: a prime at most \(D\) has a
zero mask, and a larger prime has no small-prime logarithm. The theorem
`smallCoefficient_eq_lcm_sum` retains every ordered divisor pair:

\[
E_{D,S}(n)=\sum_{\substack{a\le D\\a\text{ prime}}}
\sum_{d,e\le D}\mu(d)\mu(e)\log a\;
\mathbf1_{\{n\text{ squarefree and }S\text{-rough},\
\operatorname{lcm}(a,d,e)\mid n\}}.
\]

`hasSum_smallResponse` justifies the expansion as genuinely convergent
series for \(\Re s>1\), at every positive moment order. The independent
marked bare-series bound pays for all three finite indices. At order
\(N+1\) the cost is at most

\[
C(y,r)D^3\log D\,e^{4\sqrt R}r^{-N}
\sum_k |p_k|r^{-k},\qquad |y|>1,\quad 0<r<1.
\]

No source limit or prime-cancellation hypothesis enters this estimate.
`exists_actualSmall_bound` specializes it to

\[
\left|u^{N+1}\sum_n E_{D_N,S_N}(n)K_N(n)\right|
\le C_\rho(1+N)\eta_\rho^N,\qquad
\eta_\rho=\frac{2u^{1/8}}{1+u^{1/8}}<1.
\]

The exact remaining coefficient is

\[
H_{D,S}(n)=\mathbf1_{\{n\text{ rough squarefree composite}\}}
M_D(n)^2h_D(n).
\]

`coefficient_eq_square_sub_small` proves
\(H_{D,S}=M_D^2b_S-E_{D,S}\), including zero, the unit, ordinary
primes and all excluded indices. The bound concerns the complete
correction; no separate bound on an arbitrary restriction of it is
asserted. The new coefficient is zero whenever every prime factor of
\(n\) is at most \(D\).

Every nonzero coefficient has a factorization \(n=am\), where \(a\)
is prime and both \(a>D\) and \(m>D\). The exact identity
\(M_D(am)=M_D(m)\) holds when \(a>D\); if \(1<m\le D\), its
complete divisor sum is zero. `coefficient_eq_large_prime_fibres` keeps
all large-prime factors with their exact cofactor masks, counting each
once rather than choosing one distinguished factor. The coefficient is
nonnegative, but its product with \(K_N\) still has a nontrivial phase.

The head estimate also retains more scale information. The general
[`ZetaArithmeticQuadraticSmallProduct.lean`](../RiemannGaussian/ZetaArithmeticQuadraticSmallProduct.lean)
theorem applies to every complex coefficient family satisfying

\[
|a_N(n)|\le D_N^2\,\mathrm{Majorant}(n)
\]

and every finite selected subset \(T_N\subseteq\{n:n\le D_N^3\}\):

\[
\left|u^{N+1}\sum_{n\in T_N}a_N(n)K_{p,N}(n)\right|
\le C(p)\left(\frac1{2u}\right)^N.
\]

The rate calculation keeps \(u q^8/2=1/(2u)<1\). Replacing the
source-dependent rate prematurely by a constant would miss this
quadratic coefficient allowance. `norm_coefficient_le` proves eligibility
of the full large-prime coefficient, and `norm_actualHead_le` bounds its
literal head.

The remaining series is therefore

\[
T_N=u^{N+1}\sum_{n>D_N^3}H_{D_N,S_N}(n)K_N(n).
\]

`exists_actualTail_error_bound` bounds its complete difference from the
original square response by

\[
C_\rho(1+N)\eta_\rho^N+C(p_\rho)(2u)^{-N}.
\]

`tendsto_actualTail_sub_square` proves this error tends independently
to zero. `tendsto_actualTail` then retains \(T_N\to m_\rho\ge1\).
The conditional interface `false_of_cofinal_tail_bound` states precisely
what is still needed: for each hypothetical right-half zero, some
\(\varepsilon_\rho>0\) and arbitrarily large orders with
\(\Re T_N\le1-\varepsilon_\rho\). That upper bound has not been proved.

All source, convergence, support and error theorems above are in
[`ZetaRoughPrimeLogSource.lean`](../RiemannGaussian/ZetaRoughPrimeLogSource.lean).
The accompanying
[`ZetaRoughMoebiusPrimeRecurrence.lean`](../RiemannGaussian/ZetaRoughMoebiusPrimeRecurrence.lean)
keeps the general weighted prime-insertion identity and, for prime
\(a\nmid m\), \(m>0\), its two exact mask recurrences:

\[
M_D(am)=M_D(m)-M_{\lfloor D/a\rfloor}(m),
\]
\[
L_D(am)=L_D(m)-L_{\lfloor D/a\rfloor}(m)
-\log a\,M_{\lfloor D/a\rfloor}(m).
\]

Here \(L_D(n)=\sum_{d\mid n,d\le D}\mu(d)\log d\). At the reflected
cutoff \(\lfloor am/(D+1)\rfloor\), the lower endpoint is exactly
\(\lfloor m/(D+1)\rfloor\). These identities preserve the moving
cutoff and both signed companions for further estimates. They do not
provide the missing global bound. No additional zero exclusion or
mathematical-priority claim is made.
