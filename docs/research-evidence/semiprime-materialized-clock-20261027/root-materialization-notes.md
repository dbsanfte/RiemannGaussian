# Search control and packing addresses

Three new modules preserve the original deterministic source choices and packing
address order while exposing actual finite traversals.

- `SemiprimeMaterializedWords` executes local-completion expectation, all active
  support scans, both scores at every comparison, and every sequential choice.
  It retains the terminal producer's work. Fixed support size s gives an
  alphabet factor `(A+1)^(s+1)`, including all control visits.
- `SemiprimeMaterializedWordSearch` constructs the literal original support
  lists (at most four indices), proves exact original `computedWords` equality
  after the explicit elementary-score contract, and gives actual reverse-list
  reads costing at most `3*(N+1)^2`. Support-list/index acquisition and terminal
  word access remain explicit in this generic module; the new specialized
  environment work is intended to instantiate them.
- `SemiprimeMaterializedPacking` computes each incidence label once, builds
  each complete universal-type bucket once, computes the common minimum once,
  and then emits every selected or leftover address using cached bucket scans.
  Its value is exactly `vertices.map (i, P.lookup i |> map (Fin.val,word))`.
  This includes the original first-position convention and incomplete leftovers.
  No inverse finite-type oracle, supplied packing, or supplied source row occurs
  in the runtime `acquire` interface. The actual label producer remains an
  explicit input whose entire reported work B is retained.

Writing M for incidence count, D for the universal type count, the packing
ledger is bounded by

```
M*(B+3)+1
+ D*(M*(7*Q+4)+3)+1
+ D*(M+3)+1
+ M*(D*(7*Q+4)+3*M+8)+1
+ M+4.
```

The comparison of universal words executes all Q coordinates. Incidence tag
comparison, coordinate access within functional word inputs, physical list/array
addressing, allocation representation and rational arithmetic must still be
refined to primitive bits. These modules prove a selected scalar/list-control
ledger, not a whole-program bit clock. Arbitrary input producers are never
silently priced as unit work.

All three strict builds, the combined ordinary-root fifteen-linter audit, all
214 generated declarations / 125 theorem constants' transitive standard-axiom
audits, and isolated byte-identical rebuilds pass. No old source was edited.
