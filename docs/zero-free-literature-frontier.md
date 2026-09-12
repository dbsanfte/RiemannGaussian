# Zero-free literature frontier and exact Lean comparison

Source audit: **12 September 2026**. This table separates a published or
reported zero-free statement from the repository's independently proved
comparison of its width function. External analytic proofs and numerical
RH verifications are **not assumptions or imported certificates** in the
Gaussian theorem chain.

## The exact comparison interval

Put (H=|t|), (L=\log H), and (u=1/450000). Define (L_*) as the unique
solution on (L\ge250000) of

```math
\boxed{\frac{981}{50}L_*=450000\log L_*},
\qquad
\boxed{L_{\max}=\log\!\left(e^{320000}-2\right)}.
```

[ZetaGaussianBandFrontier](../RiemannGaussian/ZetaGaussianBandFrontier.lean)
proves existence, uniqueness and the rational enclosures

```math
288000<L_*<289000,\qquad 310000<L_{\max}<320000.
```

The crossover is approximately (288346.768139), for orientation only;
the definition and every comparison use the exact equation. The upper
endpoint is **not** (320000): the original band bounds (\log(H+2)),
and Lean proves (e^{L_{\max}}+2=e^{320000}).

For the headline envelope

```math
W(L)=\max\left\{
\frac{1}{4.8594L},\quad
\frac{\log L}{19.62L},\quad
\frac{1}{51.34L^{2/3}(\log L)^{1/3}}
\right\},
```

Lean proves, for **every** (L\ge250000),

```math
\begin{aligned}
\log(e^L+2)\le320000\ \text{and}\ W(L)\le u
&\iff L\in[L_*,L_{\max}],\\
\log(e^L+2)\le320000\ \text{and}\ W(L)<u
&\iff L\in(L_*,L_{\max}].
\end{aligned}
```

Thus this is the full crossover-to-ceiling interval for these functions,
not a sampled subinterval. At (L_*) the Littlewood width equals (u);
the classical and VK widths are already strictly smaller. The same module's
`nonvanishing_and_comparison` combines the strict comparison with actual
zeta nonvanishing at either sign of height and on the closed right edge.
The zero-free region itself is unchanged by this comparison extension.

## Source statements and their applicable heights

In the table, a width (w) describes the right region

```math
\sigma>1-w\quad\text{(open edge)},\qquad
\sigma\ge1-w\quad\text{(closed edge)}.
```

Decimals in Lean expressions are exact rationals. **Compared** means the
displayed width is proved smaller than (u) throughout ((L_*,L_{\max}]).
It does not assert an external proof has been formalized. A source marked
**reported** has not had its full proof independently inspected here.

| Source and statement | Width or conclusion | Height domain | Edge / audit status | Lean comparison |
| --- | --- | --- | --- | --- |
| [Platt–Trudgian, Theorem 1 (2021)](https://arxiv.org/pdf/2004.09765v1) | All nontrivial zeros have real part one half | (0<H\le3\cdot10^{12}) | Rigorous external interval computation; PDF inspected | Outside the comparison interval; verification not imported |
| [Mossinghoff–Trudgian–Yang, Theorem 1.3 (2024)](https://doi.org/10.1007/s40993-023-00498-y) | (1/(5.558691L)) | (H\ge2) | Closed; journal statement inspected | Compared by `classicalWidth_lt` |
| [Bellotti–Trudgian–Yang, Theorem 1 (2026 v1)](https://arxiv.org/pdf/2603.21490v1) | (1/(4.896L)) | (t\ge3), reflected to negative heights | Open in theorem statement; preprint PDF inspected | Compared by `classicalWidth_lt` |
| [Yang, Corollary 1.2 (2024)](https://arxiv.org/pdf/2301.03165v2) | (\log L/(21.233L)) | (H\ge3) | Open; PDF inspected | Compared by `littlewoodWidth_lt` |
| [Bellotti, Theorem 1.2 (2023 v1)](https://arxiv.org/html/2306.10680v1) | (1/(54.004L^{2/3}(\log L)^{1/3})) | (H\ge3) | Closed; version explicitly pinned | Compared by `vkWidth_lt` |
| [Bellotti's published refinement, reported in BTY (2026), equation (4)](https://arxiv.org/html/2603.21490v1#S1.E4) | Same VK shape, denominator (53.989) | (t\ge3), reflected | Open as reported; journal full text not retrieved | Compared by `vkWidth_lt` |
| [Yang thesis (2025)](https://doi.org/10.26190/unsworks/31825), [as reported in BTY (2026), introduction](https://arxiv.org/html/2603.21490v1#S1) | (\log L/(19.62L)); VK denominator (51.34) | (t\ge3), as reported | Reported replacements in the open-edge formulas; thesis PDF retrieval failed | Compared; equality for Littlewood at (L_*) |
| [Mossinghoff–Trudgian–Yang, Theorem 1.4](https://doi.org/10.1007/s40993-023-00498-y) | (I(L)), defined below | (H\ge e^{1000}) | Open; full secondary correction retained | Compared by `intermediateWidth_lt` |
| [Ford, as stated in MTY (2024), equation (1.8)](https://doi.org/10.1007/s40993-023-00498-y) | (F_3(L)), defined below | (t\ge1.88\cdot10^{14}), reflected | Closed in inspected statement | Compared by `fordWidth_lt` |
| [Sharper Ford expression, Yang (2024), equation (1.4)](https://arxiv.org/pdf/2301.03165v2) | (F_{0.618}(L)) | (H\ge3) | Open in inspected statement | Compared uniformly in the leading constant |
| [MTY, Theorem 1.2](https://doi.org/10.1007/s40993-023-00498-y) | VK denominator (48.1588) | Sufficiently large (H); threshold unevaluated | Closed; **eventual**, not automatically available on this finite band | Function compared by `eventual_vkWidth_lt` |
| [Bellotti, Theorem 1.3 (2023 v1)](https://arxiv.org/html/2306.10680v1) | VK denominator (48.0718) | Sufficiently large (H); threshold unevaluated | Closed; **eventual** | Function compared by `eventual_vkWidth_lt` |

The supplementary formulas are retained exactly in
[ZetaGaussianLiteratureComparison](../RiemannGaussian/ZetaGaussianLiteratureComparison.lean):

```math
\begin{aligned}
h(L)&=\frac{27}{164}L+7.096,&
I(L)&=\frac{0.05035}{h(L)}-\frac{0.0349}{h(L)^2},\\
J_c(L)&=\frac L6+\log L+\log c,&
F_c(L)&=\frac{0.04962-0.0196/(J_c(L)+1.15)}
{J_c(L)+0.685+0.155\log L}.
\end{aligned}
```

These are the functions in the cited MTY and Yang statements. The Lean
theorem for (F_c) covers **every** (c\ge1/2); neither the leading
constant nor the secondary terms are silently replaced in its definition.
The intermediate and Ford comparisons hold already for (L\ge250000).
The VK comparison with denominator at least (48) holds from (L_*)
onward. Its use for an eventual source is solely a function comparison.

## Coverage and unresolved source checks

| Additional lead | What was checked | What can be claimed |
| --- | --- | --- |
| [BTY (2026 v1), named Theorem 2](https://arxiv.org/pdf/2603.21490v1) | Denominator (4.8594), stated for (t\ge3), open edge. The surrounding text conditions the result on Lemma 2; the concluding proof explicitly finishes Lemma 1. | Proof status unresolved in this version. The stronger width is nevertheless included in the Lean envelope. |
| [Independent July 2026 denominator claim](https://kenan.works/posts/the-480-boundary-layer/) | The author's indexed post reports (4.7975) for (t\ge2). Full source retrieval failed; boundary and certificate not independently checked. | Not certified here. Its classical width is covered by the stronger generic Lean comparison for every denominator at least two. |
| [Yang's complete thesis](https://doi.org/10.26190/unsworks/31825) | Official repository metadata retrieved. Both the direct PDF endpoint and download route returned HTTP 500. | The two reported constants are compared. Full parameter-dependent conclusions and any stronger consequences remain unaudited. |

The BTY abstract and theorem statement also differ on whether the edge is
closed; the table uses the theorem's open edge. Bellotti's arXiv v1 and the
later reported journal constant are kept separate, rather than assigning a
later constant to an earlier version.

**Supported claim:** the repository proves actual zero exclusion and strict
pointwise improvement over every explicitly displayed comparison function
in this table throughout the exact interval. The comparisons cover the
newer classical lead as well. **This is not yet an exhaustive world-record
or historical-novelty determination.** An unevaluated threshold cannot be
assumed below the ceiling, and headline constants do not exhaust every
possible optimization of a source's underlying methods.

The repository's own eventual component combines with its explicit band
by maximum wherever both height conditions hold; see
[the proved union](../RiemannGaussian/ZetaGaussianBandComparison.lean).
The external regions above are not silently added to that Lean union.
The independent ordinary-prime tail bound and RH remain open.

## Verification and maintenance

The crossover proofs use continuity, strict monotonicity and exact rational
inequalities. The numerical approximation is absent from their hypotheses.
All new declarations are imported by the root library and participate in
the strict build, declaration lint and transitive axiom audit.
[Generated proof status](proof-status.json) records the terminal theorem
names and [the explorer audit](theorem-explorer/audit.json) records the
exported chain. Source changes require regenerating those artifacts.

When updating this table, record the exact source version, theorem or
equation number, original height condition, edge convention and whether a
threshold is evaluated. A smaller denominator is not by itself an all-height
improvement, and a comparison theorem is not a formalization of the external
analytic argument.
