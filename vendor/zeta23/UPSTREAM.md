# Zeta23 baseline source

This directory vendors the transitive Lean source closure needed for
`Zeta23.Final`, `Zeta23.ThmD.Final`, `Zeta23.FinalMult`, and
`Zeta23.ThmD.Mult` from
[`anthropics/zeta-23-lean`](https://github.com/anthropics/zeta-23-lean),
commit `2bafb8c88f177284a2123b5fefa2ff84e2365eb6` (2026-08-28).

The source is Apache-2.0 licensed; see `LICENSE` and `NOTICE`. It is retained
under the upstream `Zeta23` namespace and is not original RiemannGaussian
research.

Compatibility-only changes made for the earlier Lean 4.33.1 gate:

- deprecated set/extended-natural lemma aliases were replaced by their stated
  successors;
- three unused-binder diagnostics were repaired without changing theorem
  statements or proof terms;
- three tactic invocations were normalized and three diagnostic-only `#check`
  commands were removed so the dependency builds without replayed info output;
- eight trailing-whitespace instances were removed for the repository gate;
- comments were reworded so the repository-wide lexical placeholder ban does
  not mistake historical prose for an unfinished proof.
- unused-binder, unused-section-variable, and unused-simp diagnostics in the
  multiplicity-aware closure were repaired without changing theorem
  statements.

The current Lean 4.34.1 migration pins Mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. It updates deprecated conditional,
finite-product and logarithmic-derivative lemma aliases and removes a
redundant circle-norm simplification argument. Both the package configuration
and its standalone lockfile use the matching dependency revision.

The historical `FromPNTPlus/Sobolev.lean` and `FromPNTPlus/Fourier.lean`
copies now place their declarations in namespace `Zeta23.FromPNTPlus`.
Their mathematical definitions and theorem statements are preserved, with
qualified helper names. This isolates 152 overlapping global declarations
from OpenAI's separately pinned PrimeNumberTheoremAnd compatibility port.
OpenAI's sources remain unchanged, and this package still builds independently
with its existing Mathlib dependency.

The vendored package itself enables `warningAsError`. RiemannGaussian wrapper
theorems are independently audited for their complete transitive axiom sets.
