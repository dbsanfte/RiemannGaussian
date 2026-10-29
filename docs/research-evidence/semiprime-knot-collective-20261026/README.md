# Collective conic exchanges and cyclic quantum-torus tests

26 October 2026. This continuation tested collective row cancellation,
finite cyclic quantum-torus norms, and conic torsion presentations. The
strongest result is a **whole-family obstruction for literal integer-window
merging**: after exact-label deduplication it saves at most a factor two,
and the current complete catalogue retains interval mass
\(\Omega(km)\). The tested quantum-torus construction also does not
supply a faster complete query. The guaranteed sixth-exponent goal remains
active and unproved.

All claims are paper calculations with independent reviews. There is no
numerical coverage campaign or new factoring implementation.

## Contract

The actual labels are
\[
 E=a+bN+\lambda,\qquad \lambda^2\equiv4abN\pmod H,
 \qquad H=k^2,\quad 0\leq\lambda<H.
\]
The complete bounded catalogue has \(|a|,|b|\leq k\), with nonaxis
\(0<|ab|<k\), together with its specified axes. On the prepared branch,
\(k>16\), \(N>256H^2\), and the odd coprime local clock orders exceed
\(16H\). Public zero rows and the previously paid special rows are
handled as before. Let M be the original signed deletion horizon, with 2M+1<16H.
A physical interval has \(m<16H\), with the full
horizon \(m=\Theta(k^{3/2})\).

For \(J=\widetilde O(k)\) acquired rows, the complete query still costs
\(\widetilde O(J+\sqrt{Jm})\). The desired bound is
\(\widetilde O(J+\sqrt m)\), hence \(\widetilde O(k)\) at
\(k\asymp N^{1/6}\). A smaller representation by itself does not meet
this cost or complete the bit-complexity proof.

## Exact exchanges, and a bound on their interval compression

There is an actual conic reflection, before canonical reduction:
\[
 (a,bN,\lambda)\longmapsto
 (a+2\lambda+4bN,\ bN,\ -\lambda-4bN).
\]
It preserves both the discriminant and E. Reducing its coordinates modulo
H gives a partial involution on the retained catalogue, with a unique
admissible small lift when one exists. Its integer labels satisfy
\(E'=E+H\delta\), with \(\delta\in\{-1,0,1\}\).

For \(m\geq1\), put
\(A_m(E)=\prod_{i=1}^m(\beta^E-q^{-i})\). Then
\[
 (\beta^E-q^{-1})A_m(E+H)
 =q^m(\beta^E-q^{-(m+1)})A_m(E).
\]
This cleared identity is valid at collisions. Without dividing by its
possibly vanishing factors, the pair has exactly the local zero predicate
of one length-m+1 interval. Every endpoint retains an original row and
index for recovery. The empty prefix is handled separately.

The second reflection changes b and generates a finite graph on the
retained rows. Every edge preserves E modulo H. The proposed global
cancellation therefore groups integer labels by that residue and merges
the corresponding shifted integer intervals. Here is its complete bound:

1. If \(b'\ne b\), then
   \[
   |E'-E|\geq N-2k-(H-1).
   \]
   Whenever the difference is a multiple of H, its integer clock shift
   exceeds \(16H>m\). The two intervals are disjoint.
2. For fixed b, all labels lie in an interval of span less than \(2H\).
   Thus each residue modulo H has at most two distinct integer labels.
3. Consequently the merged interval mass is at least
   \(J_{\rm distinct}m/2\).
4. Already the retained positive b=1 subfamily has
   \(J_{\rm distinct}=\Omega(k)\). Choose \(1<a<k\) with
   \(aN\equiv1\pmod3\); each has four phase lifts. A fixed E gives,
   with \(\lambda=2\mu\) and \(S=H/4\),
   \[
   (\mu+N)^2\equiv NE\pmod S.
   \]
   Its allowed \(\mu\)-interval has span less than k/2. Square-root
   cosets modulo \(S=3^{2e}\) have spacing at least k/2 and number at
   most two, so each E has at most two descriptions. The chosen rows
   avoid both diagonals, and their labels and swap partners exceed HM,
   preserving them under public zero deletion.

This proves \(\Omega(km)\) mass for the **current complete family and
literal integer-orbit constructor**. In the existing block-and-evaluate
implementation, this merging cannot change the power scale. It is not a
lower bound for all arithmetic algorithms, for recognition of unknown
modular orbit aliases, or for a newly proved smaller coverage family.
See [exchanges, carries, and proof](conic-exchange.md) and
[independent review](exchange-review.md).

## The cyclic quantum-torus norm is cheap, but samples another orbit

Let \(\ell=k/2\), and adjoin an honest auxiliary primitive
\(\ell\)-th root \(\zeta\). With acquired base-ring central inputs,
let U have diagonal \(a\zeta^r\) and V be a cyclic shift with wrap c.
The exact identity is
\[
 \det(G(U)-V)=\prod_{r=0}^{\ell-1}G(a\zeta^r)-c.
\]
For the acquired split native polynomial
\(F(X)=\prod_j(X-v_j)\), its unshifted norm is
\[
 \det F(U)=(-1)^{\ell J}\prod_j(v_j^\ell-a^\ell).
\]
This scalar really is acquired in \(\widetilde O(J)\), without expanding
an extension-valued matrix. The extra subtraction by c is an additive
change and does not inherit the original collision decoder.

After the existing short-label order screen on \(q^\ell\), either we
have a factor or the physical clock points have unit-separated
\(\ell\)-th powers. One auxiliary orbit then contains at most one
physical clock point per hidden prime. Directly covering the clock by
such cyclic blocks therefore requires at least m blocks; one central
character does not compress it.

Using the actual arithmetic q instead gives the explicit wrap defect
\[
 DC-qCD=c(1-q^r)e_0e_{r-1}^{\mathsf T}.
\]
Its coefficient is a unit. Closing the cyclic-dilogarithm recurrence now
requires the real block normalizer \((xq;q)_r\). Across all rows and
blocks its initialized readout costs
\(\widetilde O(r+Jm/r+J)\), returning the old bound when optimized.
The normalizer contains the desired collision zeros and cannot be dropped
as a unit. See [calculation](quantum-torus.md) and
[review](quantum-torus-review.md).

## Torsion and conic parametrization retain their arithmetic boundary

The binary quadratic form
\(\begin{psmallmatrix}a&\lambda/2\\\lambda/2&bN\end{psmallmatrix}\)
is singular modulo the auxiliary S, but has determinant
\(-\lambda^2/4\), a unit, modulo N on nonaxis rows. Exponent reduction
modulo N is not reduction modulo the unknown group orders.

A valid exponential presentation instead has determinant
\[
 \det\begin{pmatrix}
 \beta^{a-Hi}&\beta^{-\lambda/2}\\
 \beta^{-\lambda/2}&\beta^{bN}
 \end{pmatrix}
 =\beta^{-\lambda}(\beta^{E-Hi}-1).
\]
The eliminated bottom pivot is a unit; the remaining Schur factor may
vanish at a collision. Identifying row vertices does not preserve that
product automatically. The exact rank-one parametrization modulo S
retains row-dependent integer carries. The complete character selector
requires \(\Theta(k^2)\) modes; it is not a product contraction on the
sparse native mask. See [torsion and character tests](torsion-conic.md)
and [review](torsion-conic-review.md).

## Literature and scope

[Kashaev's cyclic 6j construction](https://arxiv.org/pdf/hep-th/9411147)
and [Ishibashi's cyclic quantum Teichmüller theory](https://arxiv.org/abs/2501.02316)
provide the finite cyclic setting. The latter has a
[16 October 2026 phase correction](https://arxiv.org/abs/2610.23572)
requiring additional lifting data for strict pentagon identities. Valid
root-of-unity phase factors are units; correcting them does not acquire
the native block normalizer. The source-specific hypotheses and the
Cimasoni splice/Seifert normalizations are recorded in
[sources.json](sources.json).

The next useful step must change the actual scalar contraction or prove
coverage for a smaller family. Closing the current literal exchange graph
as interval unions cannot supply the target rate. The finite identities
remain available for a different collective construction, with their
boundary factors retained.

The archive preserves all 801 prior protected files, both old journal/agent
prefixes, and 22 concurrent engineering files. No numerical campaign,
executable research implementation, Lean module, public asset, commit, or
push is included. See [validation](review.json) and [manifest](manifest.json).
