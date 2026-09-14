# Current RH proof direction

[Open the current proof explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/).
The default view ends at
[`exists_original_band_critical_profile`](../RiemannGaussian/ZetaRieszCriticalProfile.lean),
the furthest checked bound in the active signed Riesz carrier campaign.
**RH remains open.** This is a finite bound with the parameter conditions
shown in its Lean statement, not a proof that its right-hand side is small
enough to close the contradiction.

## Direction and obstruction

A hypothetical zero to the right of the critical line forces a nonzero
normalized source in the original signed arithmetic carrier. The
[separate source view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=source-limit)
shows the compiled theorem and its zero hypothesis. The campaign seeks an
independent arithmetic estimate incompatible with that source.

The current bound carries the actual squarefree support, Möbius signs,
logarithmic phases, filter coefficients and full complex frequency-fibre
averages into a finite conditioned-energy recurrence. At the initial scale
pair `a=0,b=1`, the proved critical homogeneous exponent plus every positive
epsilon now supplies both actual quotient moments. A finite induction bounds
every descendant energy and replaces the complete initial allowance,
including its deep remainder, by `B*p^beta` with `beta<0`. Its coupled cutoff `p^S<=X` and
actual padded quotient threshold stay explicit. The remaining correlation,
sampling and positive block-normalization costs have **not** been proved
small enough for the contradiction. Quantitative parameter costs, resonance
and the required combined weighted arithmetic saving remain open. The
[proof notes](zeta-riesz-conditioned-energy.md#critical-exponent-in-the-original-initial-profile)
give the exact identities and bounds.

Stronger zero-free regions reduce the remaining strip and supply analytic
inputs. The numerical certificate is a separate result about the proportion
of simple critical-line zeros. Neither result supplies the missing signed
arithmetic estimate. This explorer does not draw a proved arrow across that
gap or estimate a percentage of RH completed.

The **Critical moments** view proves the actual global exponent
`2k(u+1)-k(k+1)/2+eps` for every `k>=2,u>=k,eps>0` at all sufficiently
large original endpoints. One uniform improvement above each fixed positive
defect closes the infimum argument; no analytic moment budget is assumed.
Both moments in the actual Korobov product sum now receive that exponent,
retaining the full joint resonance envelope and quartered Gaussian cost.
The [precise theorem and limits](vinogradov-korobov-framework.md#critical-high-moment-exponent-and-actual-product-sum)
do not assert `eps=0`, all smaller moment orders, or evaluated constants
and thresholds. Uniform parameter costs and joint resonance still need
estimates before this yields the required zeta growth bound.

The **General recurrence** view retains the full result at every finite
scale pair. The **Information audit** still proves that changing normalization
alone improves only the deep remainder; intermediate energies are unchanged
after restoring their source scale. Their new independent bound comes from
the profile induction. Constants, improvements and terminal thresholds are
not numerically evaluated. No arrow to an RH contradiction is asserted.

## Evergreen presentation

[Campaign metadata](rh-proof-explorer/metadata.json) is the single source for
the stable direction, current terminal status path and the per-commit latest
update. The theorem names resolve through the compiled
[project status](proof-status.json); statements, source lines, dependencies
and transitive axioms come from Lean. Mathematical families use the shared
[family taxonomy](theorem-explorer/metadata.json).

The README contains one generated section, with a nested **Latest Update**.
Change the direction only when the active branch or its strategy materially
changes, recording the reason. Every commit increments the latest-update
sequence and describes that commit, including presentation or maintenance
work without claiming new mathematics. Replace the entry; do not append a
history. Update the frontier path only to an actually compiled theorem.

After the ordinary Lean build and project-status generation, run:

```bash
THEOREM_GRAPH_METADATA=docs/rh-proof-explorer/metadata.json \
THEOREM_GRAPH_OUTPUT=.lake/rh-proof-explorer/lean-graph.json \
  lake env lean -DwarningAsError=true scripts/ExportTheoremGraph.lean
python3 scripts/build_rh_proof_explorer.py
.lake/browser-venv/bin/python scripts/test_rh_proof_explorer.py --refresh-preview
python3 scripts/build_rh_proof_explorer.py --check
.lake/browser-venv/bin/python scripts/test_github_readme.py
```

The preview is an actual Chromium screenshot of the default explorer,
including its current endpoint and mathematical-family zones.
[Capture metadata](rh-proof-explorer/preview.json) binds the PNG to the graph,
UI, campaign metadata, browser requirements and capture script. CI checks
these hashes and exercises the actual page, source links, hover, zoom and
endpoint switching on desktop and mobile. It captures a fresh image for
inspection without requiring platform-identical font rasterization.

The tracked hook checks the staged update against HEAD; CI checks each
committed update against its parent. The Pages artifact publishes this view
at `/rh-proof/` beside the zero-free and numerical-certificate explorers,
with source links pinned to the exact verified presentation commit. Ordinary
builds never rerun the exhaustive numerical certificate for this view.
