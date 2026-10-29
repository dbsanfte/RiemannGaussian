# Direct tests of the acquired knot/Bethe core

26 October 2026. Three bounded attempts tested whether the preceding
[small-core construction](../semiprime-knot-joint-20261026/README.md)
actually makes the guaranteed collision query cheaper. Each was reviewed
independently. **None improves the whole-query bound.** This packet records
the exact failed mechanisms so they are not repeatedly offered as solutions.
It supplies neither a new backend requirement nor a completed sixth-exponent
algorithm.

The unchanged task is to detect and localize a nonunit in
\(\prod_{i=1}^{m}F(z_i)\), with acquired monic degree
\(J=\widetilde O(k)\), \(m=O(k^{3/2})\), \(k\asymp N^{1/6}\),
and \(z_i=\eta q^i\). The existing complete cost is
\(\widetilde O(J+\sqrt{Jm})\); the required cost is
\(\widetilde O(J+\sqrt m)\). Both local q-orders exceed \(16k^2\).
The original signed labels, coverage theorem, and recovery algorithm are
retained. Short prefixes proportional to J already fit the target.

## 1. The coefficient test converts exactly back to F

The preceding packet acquires the degree-at-most-J polynomial T in

\[
 S(\epsilon)=C(\epsilon)T(\epsilon)
 =\sum_{r=0}^{m}w_rF(z_1q^r)\epsilon^r,
 \qquad C(\epsilon)=(c\epsilon;q)_M,
\]

where \(M=m-J\), \(c=q^{J+1-2m}\), and all \(w_r\) are units.
A physical collision is therefore a **coefficient zero** in the long
product \(CT\), rather than automatically a shared root of C and T.

For \(T=\sum_{\ell=0}^{J}t_\ell\epsilon^\ell\), define

\[
 D_J(X)=\prod_{h=1}^{J}(X-q^{M+h}),\quad
 K_J=\prod_{h=1}^{J}(1-q^{M+h}),
\]

\[
 H_T(X)=\sum_{\ell=0}^{J}
 t_\ell(-1)^\ell c^{-\ell}q^{\ell(\ell+1)/2}
 (X;q^{-1})_\ell\prod_{h=\ell+1}^{J}(X-q^{M+h}).
\]

The exact finite-ring identities are

\[
 [\epsilon^r](CT)=C_r\frac{H_T(q^r)}{D_J(q^r)}
 \quad(0\leq r\leq M),\qquad
 \boxed{H_T(X)=K_JF(z_1X)}.
\]

All displayed bulk denominators and \(K_J\) are certified clock units.
The second identity follows from the first and the q-binomial ratios on
J+1 unit-separated bulk nodes. It applies to the actual native polynomial,
without treating its coefficients as independent. For \(m\leq2J\) the
old evaluator already costs \(\widetilde O(J)\).

Thus even the fully executed coefficient-functional conversion produces
exactly the original geometric-grid problem. The last J-1 requested
positions are cheaply evaluated, but the bulk still has \(\Theta(m)\)
positions. The extra position r=m is not part of the physical prefix.
See [derivation](core-query.md) and [review](core-review.md).

The same report checks the moment-rank proposal on actual native input.
The full moment sequence has one distinct clock node for each nonzero
\(F(z_i)\), so its rank is at least \(m+1-J>J+1\) when \(m>2J\).
A collision does not collapse it to a J-state recurrence. Individual small
Hankel minors can still cancel in finite characteristic; their saturated
zeros have no automatic original-leaf interpretation. The large Hankel
determinant, after subtracting the extra endpoint, has exactly the desired
predicate, but its long readout remains unpaid.

## 2. Scaling cannot shorten the actual negative witness

For an actual nonaxis witness with \(I\leq-1\) and \(0<\lambda<H\),
where \(H=k^2\), admissible positive integer scaling gives

\[
 I_d=dI-\lfloor d\lambda/H\rfloor\leq I.
\]

Opposing the row, scaling it, and opposing back instead gives

\[
 I'_d=1+dI-\lceil d\lambda/H\rceil\leq I.
\]

Neither operation shortens that negative index. This is a uniform theorem
for the actual operation and witness domain, not a finite-example finding
or a claim about every possible alternative conic vector. Dividing common
content remains the already credited operation.

The smaller-order result from the previous packet would make a short
partial-order incidence useful. For a candidate order prime \(\ell\),
a stationary center incidence requires an actual lattice point satisfying

\[
 aP-bQ\equiv0\pmod k,\qquad
 aP+bQ\in\bigcup_{t\in\mathbb Z}(H\ell t-H,H\ell t].
\]

The existing Gauss coverage theorem supplies the lattice condition and a
long index bound; it does not select these additional windows. The label
aggregate and first-drop localization would also need to be acquired.
See [native proof](native-cover.md) and [review](native-cover-review.md).

## 3. A recent fast-factorial method needs a different shift algebra

[Yann Tal's September 2026 paper](https://eccc.weizmann.ac.il/report/2026/211/)
was checked as a possible acquisition tool. Its divisor-dependent
algorithms use a supplied prime and appropriate arithmetic data. Its
separate uniform deterministic refinement gives a logarithmic gain for
factorials modulo a known prime or its square.

The mechanism tested here is its compact shifted-prefix state modulo
\(p^2\):

\[
 \prod_{j=1}^{h}(j+pZ)=A_h+pZB_h\pmod{p^2}.
\]

Terms of degree two and above vanish because the shift contains p. For
our multiplicative clock the corresponding exact expansion is

\[
 F(t(1+Z))=\sum_{r=0}^{J}t^rF^{[r]}(t)Z^r,
 \qquad Z=q-1.
\]

Here \(q-1\) is a **unit**, and the high-degree tail does not vanish.
It may cancel the truncated part at an actual collision. An auxiliary
nilpotent jet cannot be evaluated at that unit by an algebra homomorphism.
The legal even/odd product split retains both phases and gives the existing
\(JB+m/B\) block cost. See [source and adaptation](fast-query.md) and
[independent source review](fast-query-review.md).

## Consequence for the next effort

The coefficient conversion, short-rank-collapse criterion, and scaling
operation do not supply the requested speedup. The report also refutes
the universal algebraic inference from a clock root to a shared root of
C and T; it does not supply an attained native-catalogue counterexample
to a separate conic-specific gcd theorem. Such a theorem remains unproved.
The tested nilpotent-prefix algorithm lacks a valid native specialization.
None of these findings is a general impossibility result for knot methods
or for an arithmetic algorithm using the core.

The next substantive advance must use additional collective conic
arithmetic to acquire the original long zero predicate, or prove and
acquire a smaller guaranteed cover. Further basis conversion by itself
would repeat the first identity above. No new prep theorem, auxiliary
successful gcd, or numerical family is counted as attaining that advance.

The [source ledger](sources.json), [validation record](review.json), and
[manifest](manifest.json) retain the reviewed evidence. All 791 prior
protected files, both old journal/agent prefixes, and 22 concurrent
engineering files are preserved. No numerical campaign, executable
research implementation, Lean change, public asset, commit, or push is
included. The full sixth-exponent goal remains active and unproved.
