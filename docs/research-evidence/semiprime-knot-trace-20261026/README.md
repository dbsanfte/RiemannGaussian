# Stationary colours, Farey traces, and an acquired coverage family

26 October 2026. The constructive result of this pass is an exact linear
phase for each public stationary colour, together with a deterministic
algorithm that acquires a coverage-preserving family in
\(\widetilde O(k)\) bits. This is a uniform paper argument for the prepared
semiprime branch, not a finite coverage experiment. **The complete long
collision query is still not faster.** Its bound remains
\(\widetilde O(J+\sqrt{Jm})\), with \(J=\widetilde O(k)\),
\(m=O(k^{3/2})\), and \(k\asymp N^{1/6}\). The full deterministic
sixth-exponent factoring goal remains active and unproved.

The old catalogue already had softly linear acquisition. The contribution
here is a more structured choice of roots and rows, suitable for testing
collective colour recurrences. Neither its acquisition bound nor its
coverage theorem pays for the long query or finishes the overall bit-cost
proof. Prior virtual Gauss coverage and the pair-first/Dickson decoder
retain their existing credit.

## The arithmetic colour makes the conic phase linear

Use the existing prepared contract: \(N=PQ\), \(k=2\cdot3^e>16\),
\(H=k^2\), \(N\leq k^6\), and the guarded clock \(q=\beta^H\)
whose local orders exceed \(16H\). For each unit j modulo k define
\[
 \Lambda_j=\{(a,b):aj^2\equiv bN\pmod k\},\qquad
 \lambda_j(a,b)\equiv-aj-bNj^{-1}\pmod H,
 \quad 0\leq\lambda_j<H.
\]
The inverse is computed modulo the public H. On this index-k lattice,
the phase is independent of the chosen lift of j from k to H, and
\[
 \lambda_j^2\equiv4abN\pmod H.
\]
For the true colour \(j\equiv P\pmod k\), it is exactly
\(-aP-bQ\pmod H\), so the stationary index
\(I=(aP+bQ+\lambda_j)/H\) is an integer.

For same-colour vectors v,w, canonical reduction gives the acquired carry
\[
 \lambda_j(v+w)=\lambda_j(v)+\lambda_j(w)-Hh,
 \quad h\in\{0,1\},\qquad E_{v+w}=E_v+E_w-Hh.
\]
Unwrapping that carry produces an actual two-generator multiplicative
character. Its trace satisfies a second-order line recurrence, and the
canonical pair traces satisfy an exact determinant-weighted product-to-sum
identity. All colours and all admitted coloured incidences can be acquired
in \(\widetilde O(k)\), without a k-by-k table. Swapping exchanges
colours by \(j\mapsto Nj^{-1}\pmod k\); it need not stay in the same
colour. See [construction and incidence algorithm](trace-recurrence.md)
and [independent review](trace-recurrence-review.md).

## A public, selected-root family with a complete coverage proof

For each public colour and each dyadic factor-size guess \(p_0\), perform
exact two-dimensional Gauss reduction of \(\Lambda_j\) in the norm
\[
 \|(a,b)\|_0^2=(ap_0)^2+(bN/p_0)^2.
\]
The weighted covolume is kN. A shortest vector satisfies
\[
 \|(a,b)\|_0^2\leq\frac{2}{\sqrt3}kN,
 \qquad |ab|\leq\frac{k}{\sqrt3}<k.
\]
Thus it is an admitted native row, including the specified primitive axis
cases. For the true colour and a guess within a factor two of P,
\[
 |aP+bQ|\leq\frac{4}{3^{1/4}}\sqrt{kN}<4\sqrt{kN}.
\]
The existing safe signed horizon, using an integer ceiling for
\(\sqrt{kN}\), therefore contains its collision. Acquiring the vector,
its single selected phase, its opposite, and both swap partners costs
polylogarithmic work per colour/scale. There are O(k) colours and
O(log N) scales.

The true pair survives public zero-row deletion: deletion would give a
short nonzero clock period, then force the impossible integer relation
\(a=bQ\) or \(b=aP\). Opposites retain the exact \(I\mapsto1-I\)
or \(I\mapsto-I\) source map for the negative-only query; centre and
special-row cases use the inherited factor-or-unit processing. Nonzero-phase
axes are retained. These checks are part of the construction, not assumed
consequences of a lattice representation. See [coverage and branch test](farey-query.md)
and [independent derivation](farey-query-review.md).

This is an alternative family at the same exponent scale. It does not
prove a polynomially smaller number of colours or a shorter guaranteed
window.

## What the knot identities compute, and what is still missing

With the acquired unwrapped character \(X_v\), put \(B_v(Z)=Z-X_v\).
The same-colour addition law gives
\[
 B_{v+w}(ZW)=W B_v(Z)+X_v B_w(W).
\]
This propagates two common-prime collisions at coupled indices forward.
It does not decide whether either child subtree contains a collision, and
the child index interval is a sum of the parent intervals with its carry.
Consequently it is not yet an algorithm for selecting a useful colour.

Ordinary determinant-one Farey neighbours do not preserve the canonical
conic phase by a literal integer clock shift: additive phase closure would
require \(H/4\mid\det(v,w)^2\). The index-k colour lattice repairs this
precise defect. Hidden-order modular aliases are not ruled out by the
literal statement.

Two further calculations delimit specific proposed contractions:

* At a fixed acquired centre (a+b,lambda), the native catalogue contains
  only one unordered swap pair. Expanding the entire family in a formal
  common Chebyshev trace instead has degree \(\Omega(k^2)\), already
  on actual retained primitive rows. These facts concern those expansion
  strategies, not all implicit algorithms.
* A common mixed orientation gives a cheaply acquired rank-two polynomial
  \(h_0(Y)+h_1(Y)D\), with \(D^2-tD+1=0\). Closing all swap pairs
  takes the norm \(h_0^2+t h_0h_1+h_1^2\) and removes the orientation
  coordinate. The tested nonabelian Fricke relation supplies another
  symmetric quadratic, but no acquired equation selecting the mixed CRT
  branch. See [mixed-trace calculation](mixed-trace.md) and
  [review](mixed-trace-review.md).

The next substantive target is an exact scalar predicate for a group of
these colours that preserves an original collision witness, with all
initialization and query costs charged. A jointly contracted norm would
also suffice. Running the known long query separately for each colour
does not meet the target.

## Literature checked

[Frohman–Gelca](https://arxiv.org/abs/math/9806107) supplies the torus
skein product-to-sum identity. [Chesebro](https://arxiv.org/abs/1902.01968)
and [Elzenaar–Martin–Schillewaert](https://ems.press/content/serial-article-files/52234)
provide Farey character recurrences and initialized fan transfer. Their
specified-node recurrences motivate the construction; the native colour
and coverage arguments above are derived here, not asserted by those papers.

The equal-parameter constant in the latter paper must be read from
Theorem 4.4: it is \(2(\alpha+\alpha^{-1})^2\), or
\(8\cos^2\theta\) when \(\alpha=e^{i\theta}\). Constant 8 applies
to the parabolic specialization. The broader wording in Corollary 4.5
does not agree with that substitution.

[Goldman's trace-coordinate treatment](https://arxiv.org/abs/0901.1404)
and the Burde–de Rham theorem recalled by
[Bénard](https://arxiv.org/abs/1612.06237) clarify the relative-coordinate
and representation-existence issues. They do not supply a modular mixed
eigenline algorithm. Wang–Wong's fast one-hole-torus multiplication was
rechecked and is already covered in the earlier literature packet; its
skein-valued boundary discrepancy supplies no new native scalar here.
Source locations and prior-input hashes are in [sources.json](sources.json).

All results are paper calculations with independent reviews. No numerical
coverage campaign, factoring implementation, Lean change, public asset,
commit, or push is included. All 811 prior protected files, both existing
journal/agent prefixes, and 22 concurrent engineering files are preserved;
see [validation](review.json) and [manifest](manifest.json).
