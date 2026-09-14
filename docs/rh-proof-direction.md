# Current RH proof direction

[Open the current proof explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/).
The default view ends at
[`actual_band_le_conditioned_iteration`](../RiemannGaussian/ZetaRieszConditioningTransfer.lean#L189),
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
averages into a finite conditioned-energy recurrence. Sampling costs,
positive block normalization, the deep remainder and every intermediate
conditioned energy are retained. Their combined budget has **not** been
proved small enough for the contradiction. Initial global mean-value
conditioning, improved high-moment exponents and the required weighted
arithmetic saving remain open. The [proof notes](zeta-riesz-conditioned-energy.md#direct-transfer-to-the-finite-conditioning-recurrence)
give the exact identities and bounds.

Stronger zero-free regions reduce the remaining strip and supply analytic
inputs. The numerical certificate is a separate result about the proportion
of simple critical-line zeros. Neither result supplies the missing signed
arithmetic estimate. This explorer does not draw a proved arrow across that
gap or estimate a percentage of RH completed.

The **Auxiliary advance · first global moment saving** view now follows the
full unweighted mean value into the actual finite conditioned-energy
allowance and an independent global exponent improvement of `1/(3k)` for
every `k>=2,u>=k`, at every sufficiently large cutoff. Prime selection,
exceptional-coordinate absorption and all endpoint transfers are proved.
[The precise theorem and remaining moment obstruction](vinogradov-korobov-framework.md#first-global-high-moment-exponent-improvement)
remain separate from the original weighted-carrier endpoint. No arrow from
this auxiliary result to an RH contradiction is asserted.

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
