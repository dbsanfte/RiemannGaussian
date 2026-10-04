# Joint signed balanced-mask cancellation

The actual balanced prime contribution and its **original signed native
complement** cancel at the test height `19*pi`, despite both having
divergent absolute mass. This is a checked actual-prime cancellation test,
not a hypothetical-zero estimate or a new zero-free result.

The leaf is
[ZetaRieszSelbergMaskCancellation.lean](../RiemannGaussian/ZetaRieszSelbergMaskCancellation.lean).
It preserves the existing balanced pair box, full complex phase, moving
length, both factorial prefixes, complete-period support, diagonal
conventions and original dyadic schedule. It introduces no new prime
subdivision or carrier completion on an isolated mask.

Write `B_N = balancedPrefix u y N` for the full original balanced-prefix
contribution and `D_N = maskRest u y N` for the exact sum on
`nativePairMask \ balancedProducts N`. The finite ledger is exact:

```math
B_N+D_N=\operatorname{prefixPairDefect}(u,y,N).
```

Every original prefix correction stays in `B_N`; it is not paid or
credited again. Neither piece is declared small. The pre-existing
whole-support completion bound is applied only to their assembled sum.

For a genuine ordinary-prime moment bound with radius `R`, the leaf proves
the signed estimate

```math
|\operatorname{Re}B_N+\operatorname{Re}D_N|
\le 26C^2(u/R)^N+E_{\rm whole}(N)+E_{\rm diagonal}(u,N),
```

where the two displayed errors are precisely the already-paid whole-mask
and square-diagonal budgets. This does **not** assert `R > u` at an exposed
zero.

## A quantitative joint cancellation test

At the fixed test height `y = 19*pi`, the existing signed-pole region gives
a concrete radius `100011/200000`. It exceeds the original radius ceiling
`10001/20000`. Consequently one existential height-dependent constant
`C > 0` gives, for every original radius and `N >= 65536`,

```math
\|B_N+D_N\|
\le26C^2(100010/100011)^N
  +E_{\rm whole}(N)+E_{\rm diagonal}(u,N)
\longrightarrow0.
```

The previously proved **signed** balanced endpoint growth remains:

```math
\operatorname{Re}B_N\longrightarrow+\infty.
```

The new exact ledger now proves the corresponding actual complement
behaviour:

```math
\operatorname{Re}D_N\longrightarrow-\infty,
\qquad
\|B_N\|+\|D_N\|\longrightarrow+\infty.
```

Thus the complement cannot be given a separate constant cofinal floor,
even on the original dyadic schedule. Nevertheless the **joined** real
contribution has the displayed geometric bound in both directions.
This establishes which boundary cancellation a valid mask-preserving
argument must retain; it does not turn either divergent term into a paid
sector.

## Why the same radius argument does not close the ceiling

The leaf also proves a precise source obstruction. If the actual normalized
ordinary-prime array has a nonzero limit and satisfies a moment bound
`C/R^k`, then necessarily `R <= u`. Otherwise the bound forces that same
array to tend to zero. For an exposed zero its limit is `-m`, with the
actual positive analytic multiplicity retained, so a source-subcritical
whole-array bound cannot simply be imported from the test-height case.

In particular, the test does not supply the independent **42/25** upper
bound for the whole source-carrying `joinedPhysical`. It takes place at
heights already covered by a zero-free region; `19*pi` is not asserted to
be a zero ordinate. No new constant-ceiling credit, simple floor, zero
exclusion or RH proof is claimed.

The next substantive input must constrain the selected signed arithmetic
resonance while retaining its whole native complement. Further absolute
payment of either masked piece loses the cancellation proved here.

## Local validation

The optional leaf build uses warnings as errors. The scoped check runs the
namespace linters and checks every theorem's transitive axioms against
`propext`, `Classical.choice` and `Quot.sound`. No new numerical probe is
needed: all new inequalities follow from checked actual-prime theorems and
an exact finite signed ledger. The qualitative-PNT entry order inherited
by the divergent balanced term is existential, never numerically certified.

The new audit preserves all 377 preceding source, validation, probe and
audit pins. No old file is changed; `AGENTS.md` receives only the recorded
append. Root registration, public README/explorer metadata, wider gates,
CI, commits and pushes are outside this local slice. Concurrent semiprime
work is preserved.
