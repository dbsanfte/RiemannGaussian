# Zero-free region comparison graph

[![Benchmark regions and our independently proved Gaussian region](comparison.svg)](comparison.svg)

The coral boundary is our **independently proved region**, valid at every
height, including its closed right edge and excluding the pole `s=1`.
The picture starts at `|t|=3`, where all selected benchmarks apply.
The left panel plots its
width against logarithmic height; larger width excludes more of the strip.
The right panel magnifies the actual real coordinate near `σ = 1`, with
each region shaded toward that edge. The other edge follows by reflection;
both signs of the imaginary coordinate are covered.

The region combines the Gaussian proofs with the older signed-pole/reserve
proof from this repository's own analytic machinery. Throughout the grey Lean-checked interval, its width is
strictly greater than the maximum of all the plotted benchmark widths, so it
excludes additional area beyond their combined coverage.

The overview intentionally includes heights where external results are
stronger. Neither panel is an exhaustive world-record comparison. The
unresolved interior continues to the left of the magnified view; the
critical line is far outside that view.

## What the colours and styles mean

| Colour | Family | Inspected source (solid) | Additional comparison (dashed) |
| --- | --- | --- | --- |
| Coral | Complete explicit region | [Current Lean strip theorem](../../RiemannGaussian/ZetaUnifiedZeroFree.lean) | None |
| Blue | Classical | [BTY (2026 v1), Theorem 1: 4.896](https://arxiv.org/html/2603.21490v1#S1) | The same version's 4.8594 candidate has an unresolved supporting proof; its width is compared without adopting it as proved |
| Purple | Littlewood | [Yang (2024), Corollary 1.2: 21.233](https://arxiv.org/pdf/2301.03165v2) | 19.62 from Yang's thesis, [reported in BTY](https://arxiv.org/html/2603.21490v1#S1); full thesis not inspected |
| Green | Vinogradov–Korobov | [Bellotti (2023 v1), Theorem 1.2: 54.004](https://arxiv.org/html/2306.10680v1) | 51.34 from Yang's thesis, [reported in BTY](https://arxiv.org/html/2603.21490v1#S1); full thesis not inspected |

The three benchmark shapes are `1/(C L)`, `log(L)/(C L)`, and
`1/(C L^(2/3) log(L)^(1/3))`, where **`L = log|t|`**. The Gaussian
formula instead uses **`log(|t|+2) = log(exp(L)+2)`**. The exporter proves
the formula identities, and the plotting interpreter preserves that
distinction using a numerically stable evaluation.

All plotted external statements start at `|t| ≥ 3`, below the graph's
starting height. Bellotti's pinned v1 and our complete region include the
closed edge; the other external statements use open edges. Exact edges
cannot be distinguished by a drawn line, so they are recorded in
[metadata.json](metadata.json). The external analytic proofs are not
imported into the Gaussian theorem chain. See the
[complete literature-frontier table](../zero-free-literature-frontier.md)
for later source versions, supplementary formulas and retrieval status.

## The checked comparison band

The grey band marks the extended interval covered by
[the Lean comparison](../../RiemannGaussian/ZetaGaussianExpandedComparison.lean):

```math
L_* < L \leq 480000,
\qquad (981/50)L_*=450000\log L_*,\qquad 288000<L_*<289000.
```

The earlier constant-plateau comparison covers the interval from `L_*`;
the new proof uses the full adaptive region to extend it through `480000`.
It retains the plus-two height correction and proves the lower width
`18/(25L)` on `[300000,480000]`, above all the plotted benchmark widths.
The approximation `L_* ≈ 288346.768` only positions a graphic. The new
upper endpoint is certified, not asserted maximal. The shaded interval is
**not** an upper height limit for our actual zero-free region.

Numerical crossings visible outside the grey band are illustrations, not
additional Lean comparison theorems. Eventual bounds, including our own
log-log component, are omitted because their coefficient-dependent starting
heights have not been numerically evaluated. External finite RH verification
is also outside this analytic edge-width comparison and has not been imported.

## Reproduce and maintain

The evergreen inputs are [metadata.json](metadata.json), the current
[proof status](../proof-status.json), and the imported Lean definitions.
[ExportZeroFreePlot.lean](../../scripts/ExportZeroFreePlot.lean) produces
expression trees and checks their real-valued meanings against the width
definitions. It also checks the actual starting height, the headline
benchmark envelope, the exact crossover enclosure and the ceiling.
Every formula proof and terminal theorem undergoes a transitive axiom audit.

After the ordinary build, dashboard and theorem-graph regeneration:

```bash
python3 -m venv .lake/plot-venv
.lake/plot-venv/bin/pip install -r scripts/requirements-plots.txt
lake env lean -DwarningAsError=true scripts/ExportZeroFreePlot.lean
.lake/plot-venv/bin/python scripts/build_zero_free_plot.py
.lake/plot-venv/bin/python scripts/build_zero_free_plot.py --check
```

Optional: add `--png .lake/zero-free-regions/comparison.png` for a local
raster preview. The standalone SVG uses embedded font outlines for consistent
rendering and has accessible title and description elements.

The generated [formulas](formulas.json) and [audit](audit.json) travel with
the SVG. The audit links exact Lean declaration lines and the existing
theorem-explorer audit, records input hashes, and explicitly distinguishes
formula proofs from floating-point drawing. Ordinary CI recompiles the
exporter and rejects stale graphics or metadata before publication. The
pre-commit hook applies the same check. This process does **not** run the
optional exhaustive numerical certificate.

After a presentation change, run the existing GitHub README browser check;
it verifies the prominent graph, enlargement link and desktop/mobile fit as
well as the actual GitHub math renderer. Source, proof and literature changes
must be reflected in the metadata and generated artifacts together.
