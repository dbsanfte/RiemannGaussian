# Actual flag extension helper

New sole-owned repository module: `RiemannGaussian/SemiprimeMacroFlagExtension.lean`.

It imports the existing graph signal types and macro bit-array arithmetic, without importing or modifying GraphSemantics. `buildFlags` constructs values on the literal `MacroGraph.FlagSignal d` type. `buildFlags_or` proves every actual OR-gate recurrence, `terminal_buildFlags_iff` proves terminal truth exactly when some source digit flag is true, and `unique_flags`/`existsUnique_flags` prove no extra flag-extension choices remain once digit values are fixed. `previous` and `terminal` use the actual graph predecessor and last-wire indices, including d=1.

`inputFlag_exists_iff` and `terminal_inputFlag_iff` additionally connect the actual low-digit check `2<=decode(word0)` and high-digit checks `decode(wordi)≠0` to `2<=operand words`, for bits>0. These are reusable for the graph converse; they do not assume graph acceptance and do not assert the whole graph extension or counter runtime.

Strict build command:

```
cd /home/dbsanfte/riemann/formal
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true -o .lake/build/lib/lean/RiemannGaussian/SemiprimeMacroFlagExtension.olean RiemannGaussian/SemiprimeMacroFlagExtension.lean
/home/dbsanfte/.elan/bin/lake env lean -DautoImplicit=false -DwarningAsError=true /tmp/semiprime-executable-counter-20261027/CheckFlagExtension.lean
```

Logs: `flag-build.log`, `flag-audit.log`. The audit imports the root module, runs the scoped 15-linter suite, and examines every generated declaration's transitive axioms. Only `propext`, `Classical.choice`, `Quot.sound` are permitted.
