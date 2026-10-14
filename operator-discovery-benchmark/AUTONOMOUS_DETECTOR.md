# A detector stage with frozen search rules

This implements the bounded pilot requested in
[DETECTOR_INDEPENDENCE_HANDOFF.md](DETECTOR_INDEPENDENCE_HANDOFF.md).
It runs alongside the guided experiments; their arithmetic and analytic
semantics retain their existing definitions. The new stage can return any
admissible program or relation. Its discovery path has no assertion requiring
a nominated operator formula.

From this directory, start a **fresh** run with:

```bash
../.venv/bin/python run_expanded_probe.py --autonomous-only
```

Use `--autonomous-run-dir autonomous-results/my-run` to choose a fresh destination.
Sealed runs cannot be overwritten. The lower-level command is
`../.venv/bin/python autonomous_search.py run --output-dir autonomous-results/my-run`.
After a lower-level run passes, publish its report with
`../.venv/bin/python autonomous_report.py --run-dir autonomous-results/my-run`.
The main report reads the latest independently checked stage separately.

For deterministic replay:

```bash
../.venv/bin/python autonomous_search.py replay \
  --run-dir autonomous-results/my-run --output-dir autonomous-results/my-run/replay
```

## What is frozen

`autonomous_protocol.py` writes `protocol.json` before response tables are
computed. It pins source hashes, primitive semantics, integer/rational feature
families, seeds, cutoffs, logical operation budgets, archive criteria,
promotion rules, inference dictionaries and data splits. Candidate batches and
relation proposals are written and hashed before their next evaluation.

The baseline exhaustively enumerates its declared cost-bounded scalar-kernel
and bilinear templates, plus a reproducible finite sample of matrix inverses.
This is exhaustive within those templates, not within all typed programs.
The adaptive arm makes equal attempts across eight declared mutation families.
Each later batch depends on development observations under frozen rules.

`autonomous_grammar.py` supplies indices, comparisons, quotient/remainder,
bounded sums, rational weights, sequence products, finite matrix maps and
composition. Signed weights and nonlinear programs are allowed. Neither
multiplicativity nor positivity is a prerequisite. Inputs include the
constant-one zeta coefficient sequence, unrelated rational sequences and
complex rational sequences. Arithmetic is exact in Q and Q(i).

Sequence indices are 1 through N. Matrix maps may use any input inside that
declared cutoff; this lookahead is explicit. Sums are clamped to 0 through N.
Zero index divisors, singular matrices, dimension limits and exhausted operation
budgets produce recorded domain failures. Every macro stores its original body
and domain. No finite identity grants analytic convergence or zero preservation.

## How selection and language growth work

The learner proposes response aliases and sparse nullspace relations from
training observations. Each proposal includes exact residuals, its program
feature dictionary, rational coefficients and pivot-conditioning information.
Development validation tests changed sizes and generic inputs.

The archive preserves several criteria: short descriptions, response diversity,
validated relation participation, and empirical prime contrast beyond declared
index-residue features. Actual prime labels come from the evaluator, never from
coefficient production. The prime score is a development statistic over four
fixed output buckets; it does not certify prime information at untested scales.

Automatic promotion selects repeated typed subtrees by reuse and compression
under the frozen validation rule. The resulting macros preserve semantics by
exact expansion. Their usefulness is numerical evidence; naming a reusable
expression creates no theorem. Free indices and the original type are explicit.
A second adaptive arm disables promotion for the identical expanded mutations,
under the same attempted-generation allocation and operation limits. Its results
are reported even if promotion provides no improvement.

Certificate attempts currently support commutative pointwise polynomial
identities. They use universal polynomial normalization and finite corroboration
with the existing `exact_arithmetic.py` backend. The independent checker repeats
the normalization and implements scalar, sequence and matrix semantics separately.
Unsupported maps/sums/conjugations remain numerical leads, not false laws.

## Evaluation boundary and its limits

Generator/selector workers have an exact file allowlist and deny network and
subprocess operations. Tests attempt access to final/private files and external
operations. This blocks accidental leakage in the supplied Python workers; it
does not protect against hostile code or a privileged programmer.

Anonymous named calibrations are reported separately. Synthetic targets are
chosen in the evaluator using fresh OS entropy after the language is frozen.
The evaluator constructs unsigned/signed kernel combinations with a separately
implemented interpreter and shares only response tables. Targets and seeds
are committed privately until final evaluation. This removes model choice of
the particular target; the target family remains restricted to the language.
It is not evidence of historical novelty or completeness.

The archive and anonymous fitted programs are sealed before the evaluator
draws a **new** final seed. Final cases include larger, intermediate and irregular
scales, generic complex inputs, sparse inputs, and a deliberate finite-pattern
mimic. The final evaluator can reject a law or report a domain/resource failure;
it cannot promote productions or retune selection. Replay reuses development
data only. Final outcomes are a separate terminal report.

After inspecting a final result, regard that data as development evidence for
future changes. Freeze a new specification and draw fresh final cases next time.
Hash integrity alone does not create statistical independence.

The remaining design assumptions are listed in every protocol. This is greater
independence from individually nominated answers, not an assumption-free search.
Historical novelty, new all-scale prime information and ordinary-zeta/RH
relevance retain separate audit statuses. The verified-new list is unaffected
by program counts, finite fits or macro names.

## First implementation results

The first attempt, `autonomous-results/pilot-001`, failed its acceptance check:
restricting promotion to sequence expressions left no reusable production.
Its original source, protocol and observations are preserved; its final cases
are spent development evidence. It was not published as a successful run.

`autonomous-results/pilot-002` broadens promotion to any typed subtree, with
explicit free indices. It used a new frozen protocol, new synthetic target
entropy and fresh final cases. Eight independent gates passed, replaying
96,943 exact coefficients. Named anonymous recovery was 4/4; independently
sampled in-language recovery was 2/2; both false controls were rejected.
Seven additional public language contract tests passed.

Three baseline subexpressions were promoted automatically. Promotion admitted
127 of the paired 192 mutations, versus 116 without promotion. Each final
archive had 31 distinct behaviors that completed all declared evaluation cases:
30 were shared and each arm retained one different behavior. This pilot shows
automatic language growth and changed selection, with no net improvement in
final behavior count. It proves no new global estimate or historical novelty.
Use the run's `report.txt`, `summary.json` and `verification.json` for its
complete evidence and resource/domain failures.

## Automatic proof attempts alongside independent discovery

The earlier guided signed-shift family now has a frozen automatic global-bound
experiment in `compensated-shift-results/family-gap-run-001/`. It tests every
recorded parameter pair, including known finite-failure controls. The proposed
bounds remain conjectural until exact polynomial certificates and a written
uniform tail argument cover **every** composite integer. The independent
checker reconstructs the rational polynomials with a different implementation.

That experiment proves seven bounds, supplies ten actual counterexamples, and
retains four numerical leads beyond the declared proof budget. Its fixed
selection rule chooses the smallest certified bound subject to the separate
all-order zero-signature gate: parameters `1/3,5/7`, bound `2/39`. This is
automatic selection inside a guided family; it is not an output of the new
generic grammar pilot. Complete native-zeta numerical checks cover
the representative pair `1/3,2/3`, with its separately proved bound `7/110`,
and the automatic winner `1/3,5/7`, with bound `2/39`. The latter two cases
were sampled after selection closed and independently repeated with changed
precision, coefficients, integral rescaling, tails and negative controls.

The first automatic-winner native attempt failed an overly strict comparison:
the complete integral's certified enclosure was wider than the coefficient
series' tail, although the two enclosures overlapped and the altered-prime
control remained disjoint. Its original source and observations are retained
in `selected-native-attempt-001/` as development evidence. A revised frozen
comparison uses rigorous enclosure overlap with declared radius caps and
disjoint negative controls. That protocol drew fresh cases and passed all six
independent gates. This is numerical corroboration of written identities,
with no adaptation or reselection of the operator.

Recheck and publish the signed certificates with:

```bash
../.venv/bin/python run_expanded_probe.py --compensated-only
```

To regenerate its arithmetic/native observations, use
`run_compensated_probe.py --refresh-observations`. It selects a fresh frozen
family directory and retains older family experiments. Replacing development
observations does not retroactively make a guided family independent of its
design assumptions. The main report preserves the two stages' origins, proof
statuses, dependencies and counts separately. Neither stage establishes a
historically new operator, new independent prime-distribution estimate or RH.
