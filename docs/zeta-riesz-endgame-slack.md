# Sufficient endgame thresholds and their slack

The floor and ceiling remain unproved. `ZetaRieszEndgameSlack` certifies that
we can ask for weaker arithmetic bounds without changing `joinedPhysical`,
its exact source, the radius interval, multiplicity or any masks.

For `1/2 <= u <= 10001/20000`, Lean proves the **source-side** bounds

```math
\frac{23}{25}<c_{\rm ret}(u)<\frac{4601}{5000},\qquad
c_{\rm ret}(u)=\frac{\log(32/13)}{-2u\log u}-\log(19/13).
```

The source at multiplicity `m` is `-m+m^2*c_ret(u)`.
For a simple source, every cofinal floor `-a-o(1)` with
`a < 1-c_ret(u)` contradicts that exact limit. For multiplicity at least
two, every cofinal ceiling `b+o(1)` with `b < 4*c_ret(u)-2` suffices.
`multiple_source_ge_double` proves the latter is the smallest multiple
source. **A strict gap is necessary for these limit-only endpoints**;
equality with the source cannot contradict an error merely tending to zero.

These criteria now have checked rational instances:

| Required arithmetic bound | Previously sufficient | Weaker sufficient target |
| --- | ---: | ---: |
| Simple-source floor | `-0.079-o(1)` | `-0.0798-o(1)` |
| Multiple-source ceiling | `1.5+o(1)` | `1.68+o(1)` |
| Signed remainder energy | `3/(320*(N+1))` | `987/(100000*(N+1))` |

The last row is an explicit **open** arithmetic target. It applies to the
`wideRemainingEnergy` of the current global phase payment at the original
whole-population adverse cutoffs, count crop, weights, masks and dyadic
schedule. With the unchanged profile price `P<=129N/200`, Lean proves

```math
E\le\frac{987}{100000(N+1)}
\quad\Longrightarrow\quad
\sqrt{\max(E,0)P}\le\frac{399}{5000}=0.0798.
```

The squared-cost margin is exactly `189/100000000`. The existing geometric
payments are included once in `WidePhasePayment.joinedError`, which tends
to zero. `eventually_relaxed_floor_of_energy` connects that **explicit
arithmetic premise** to the relaxed floor for the original `joinedPhysical`.
No premise is inferred from the exposed-zero source or a numerical probe.

The energy target is **5.28% larger** than the prior sufficient budget,
and the ceiling is **12% larger**. The negative floor allowance itself
increases by about 1.01%. These percentages measure relaxation of the
requested bounds, not progress achieved in bounding the arithmetic sum.

For scale only, numerical endpoint evaluation gives:

| `u` | Simple source | Double source |
| --- | ---: | ---: |
| `1/2` | `-0.079929339846` | `1.680282640616` |
| `10001/20000` | `-0.079871797035` | `1.680512811860` |

The source gaps at these endpoints remain positive. These decimals are
diagnostics, not interval certificates; the rational Lean bounds establish
the validity throughout the radius interval. The generic endpoints also
permit radius-dependent thresholds approaching the exact source with any
fixed positive gap, if that makes a later arithmetic estimate easier.

There is useful slack, especially in the ceiling. It does **not** remove
the exponential source growth or prove cancellation in the remaining
central signed sum. The next arithmetic task is to establish the relaxed
budget, or a direct floor above the exact simple source. No zero exclusion
is obtained until such an independent estimate is proved.

Nine public proofs pass focused warnings-as-errors direct/targeted Lean,
ordinary root import, all 14 namespace linters and standard-axiom checks.
See `docs/riesz-endgame-slack-audit.json`. Earlier source and arithmetic
theorems are preserved unchanged. No commit, push or wider publication
gates are run.
