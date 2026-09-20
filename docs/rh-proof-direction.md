# Current RH proof direction

[Open the current proof explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/).
Its default follows the **harmonic-cost route** and ends at
[`tendsto_arithmeticRemainder_add_reserve`](../RiemannGaussian/ZetaRieszJointCofactor.lean).
An independent geometric estimate now pays the original unpaid wing
**together with** an explicit complete signed composite companion. The
remaining arithmetic difference retains the exact source and positive
reserve. Its independent floor remains open; no first restricted zero
exclusion or RH proof is claimed.

## Direction and obstruction

Prove a first restricted contradiction by completing the evaluated
harmonic-cost argument. Retain the exact head-plus-central limit
`-m²c(u)`, the proved frequency-sector savings and the deletion of complete
high-prime-count classes. Bound the surviving lower-count response and
wing together, preserving signs, phases and endpoint weights. Initially
target simple exposed zeros in `1/2<u<exp(-2/3)`, where
`u=3/2-Re(rho)` and the original remainder tends to `-(1-c(u))<0`.

The [joint cancellation ledger](zeta-riesz-joint-cofactor.md) gives the
literal companion `T_N` and proves
`|u^(N+1)(V_N+T_N)| <= C_gamma(N+1)^2 exp(-N/64)` for the original unpaid
wing `V_N`. For each fixed `abs(gamma)>1`, one constant works across
`1/2<=u<exp(-2/3)`; the starting order may depend on `u`. No hypothetical
zero or cancellation premise is used. The complete marked cofactor
response, saturation boundary, clipped prime prefix, repeated-prime
diagonal and unit term are all accounted for. Neither summand is
separately proved to vanish.

On the [positive-reserve range](zeta-riesz-harmonic-wing.md)
`1/2<u<exp(-11/16)`, let `F_j` be the actual lower-count response in
`7N_j/4<log n<=9N_j/4`, retaining every original finite mask. The new target
is the arithmetic difference `Q_j=u^(N_j+1)(F_j-T_(N_j))`. Under the
original exposed-zero hypotheses, Lean proves that `Q_j` plus the positive
reserve tends to `-m+m²c(u)`. The reserve is eventually at least `15m²/544`
in real part. The companion includes **all** admissible cofactors; its
identification with a finite masked subfamily is not assumed. Comparing
the supports, paying the off-support terms, and preserving the prime
incidences and complementary derivative allocations are the next steps
toward a signed bound for this difference.

For simple exposed zeros, a cofinal real floor `-eta` with
`eta<1-c(u)+15/544` for `Q_j` would close the contradiction. This joint
arithmetic floor remains open. The
[earlier conditional criterion](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=harmonic-floor-criterion)
shows the corresponding floor for the preceding remainder as an explicit
**unproved hypothesis**. The two remainders differ by a quantity tending
to zero, with the strict margin allowing that transfer. Simplicity and
exposure remain explicit. The new joint bound covers the full original
harmonic interval; extending the positive reserve and narrowed source
window across that interval is a separate obligation.

The
[source view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=source-limit)
shows the original full harmonic source after high-prime-count deletion.
The
[joint cancellation view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=joint-wing-cancellation)
shows the new independent estimate and its exact coefficient identity.
The
[paid-component view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=harmonic-paid-components)
retains the positive reserve, geometric outer tails and earlier support.

Every new lemma should evaluate an actual contribution, quantitatively
reduce this unpaid budget, or discharge a necessary contradiction
hypothesis. The prior
[conditioned-energy](zeta-riesz-conditioned-energy.md),
[arithmetic-cycle](zeta-riesz-arithmetic-cycles.md) and
[owner-window](zeta-riesz-owner-windows.md) results remain supporting tools;
they are not additional obligations on the active route. Stronger proved
zero-free regions can provide analytic inputs. The numerical certificate
is separate and does not supply the missing signed floor.

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
