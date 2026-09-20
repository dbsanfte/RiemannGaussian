# Current RH proof direction

[Open the current proof explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/).
Its default now follows the **harmonic-cost route** and ends at
[`tendsto_remainder_add_reserve`](../RiemannGaussian/ZetaRieszHarmonicWindow.lean):
the exact source retained by the narrowed lower-prime-count sum, unpaid
middle wing and positive reserve. The independent joint arithmetic floor
remains open. No first restricted zero exclusion or RH proof is claimed.

## Direction and obstruction

Prove a first restricted contradiction by completing the evaluated
harmonic-cost argument. Retain the exact head-plus-central limit
`-m²c(u)`, the proved frequency-sector savings and the deletion of complete
high-prime-count classes. Bound the surviving lower-count response and
wing together, preserving signs, phases and endpoint weights. Initially
target simple exposed zeros in `1/2<u<exp(-2/3)`, where
`u=3/2-Re(rho)` and the original remainder tends to `-(1-c(u))<0`.

The [current arithmetic ledger](zeta-riesz-harmonic-wing.md) distinguishes
three new estimates. Both lower-count outer logarithmic tails decay
geometrically, uniformly in height, leaving `25N/16<log n<=5N/2` across the
original harmonic range. On `1/2<u<exp(-11/16)`, this narrows further to
`7N/4<log n<=9N/4`. On that smaller interval, an actual wing block has real
normalized contribution at least `15m²/544`; the opposite high-leg wing
decays. Only the intervening wing orders and narrowed lower-count sum
remain unpaid. Their exact sum plus the positive reserve retains the
original `-m+m²c(u)` source.

For simple exposed zeros, a cofinal real floor `-eta` with
`eta<1-c(u)+15/544` for this smaller joint remainder would close the
contradiction. The
[conditional criterion](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=harmonic-floor-criterion)
shows that floor as an explicit **unproved hypothesis**. Simplicity and
exposure are also explicit; no zero-free region for arbitrary zeros follows
from these component bounds. Extending the new wing estimates across the
full original interval remains part of the goal.

The
[source view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=source-limit)
shows the existing full harmonic source after the complete high-prime-count
deletion. The
[paid-component view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=harmonic-paid-components)
shows the positive reserve, geometric tails and exact remaining support.
All earlier masks, original floor-defined length and unrestricted
multiplicity remain visible in their Lean statements.

Every new lemma should evaluate an actual contribution, quantitatively
reduce this unpaid budget, or discharge a necessary contradiction
hypothesis. The prior
[conditioned-energy](zeta-riesz-conditioned-energy.md),
[arithmetic-cycle](zeta-riesz-arithmetic-cycles.md) and
[owner-window](zeta-riesz-owner-windows.md) results remain supporting tools;
they are not additional obligations on the active route. Stronger proved
zero-free regions can provide analytic inputs. The numerical certificate is
separate and does not supply the missing signed floor.

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
