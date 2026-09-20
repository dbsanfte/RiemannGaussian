# Current RH proof direction

[Open the current proof explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/).
Its default follows the **harmonic-cost route** and ends at
[`tendsto_nondominant_exact_source`](../RiemannGaussian/ZetaRieszNondominantCarrier.lean).
The complete wing/companion comparison, all off-mask corrections, the full
positive reserve and the allocated dominant-prime sector are now paid or
evaluated. The smaller signed carrier retains the exact source. Its
independent floor remains open; no first restricted zero exclusion or RH
proof is claimed.

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

On `1/2<u<exp(-11/16)`, the
[allocation and reserve ledger](zeta-riesz-joint-allocation.md) compares that
complete companion with every original finite mask. Its exact allocation
fraction satisfies `0<=theta<=1`; no prime incidence is counted twice.
All off-mask corrections vanish, including the weighted high-count terms
and complete outer tails. The full reserve is evaluated, giving the exact
remaining cost

$$
c_{\rm ret}(u)=\frac{\log(32/13)}{-2u\log u}-\log(19/13)<\frac{37}{40}.
$$

The [dominant-prime bound](zeta-riesz-dominant-sector.md) then pays the whole
unassigned contribution whenever an eligible selected prime carries at
least `13/20` of `log n`. Both geometric rates are strictly below one;
the estimate is independent of zeros and uniform in height and count
cutoff. The original prime cutoff and factorial kernel together pay the
missing allocation endpoint. On every nonzero surviving label, every prime
factor now has `log p<13/20 log n`.

The actual target `nondominantRemainder` keeps the original signed Riesz
coefficient, complex phase, all masks, unassigned fraction `1-theta`, and
all surviving counts together. Its window is `7N/4<log n<=9N/4`.
All reductions from the original arithmetic difference vanish for arbitrary
moving heights. Under the exposed-zero hypotheses its exact limit is
`-m+m²c_ret(u)`. For simple exposed zeros its real part is therefore
eventually below `-3/40`.

An **independent** cofinal real floor at `-3/40` for this smaller carrier
would close the contradiction. This joint arithmetic floor remains open.
Balanced products remain in the sum; bounding their assigned companion
does not bound their unassigned original response. The
[earlier conditional criterion](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=harmonic-floor-criterion)
shows the corresponding floor for the preceding remainder as an explicit
**unproved hypothesis**. Simplicity and exposure remain explicit. The
earlier wing/companion bound covers the full original harmonic interval;
extending the reserve evaluation and new deletion across that interval
is a separate obligation.

The
[source view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=source-limit)
shows the original full harmonic source after high-prime-count deletion.
The
[joint cancellation view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=joint-wing-cancellation)
shows the earlier independent estimate and its exact coefficient identity.
The [allocation](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=joint-allocation),
[exact reserve](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=exact-wing-reserve)
and [dominant sector](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=dominant-prime-sector)
views expose the new reductions and their complete hypotheses.
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
