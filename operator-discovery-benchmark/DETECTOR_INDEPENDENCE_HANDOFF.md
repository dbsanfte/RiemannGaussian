# Handoff: make operator discovery less dependent on the model's preferred ideas

Date: 2026-10-07

## User request and status

The user wants the detector to extract unforeseen arithmetic operators and estimates from numerical evidence. Their concern is that the model's familiarity with prior art influences the constructions it chooses to investigate.

After discussing that limitation, the user requested: "let's feed this back to the main thread and implement your suggestions", then chose this Markdown handoff so the main thread can read it.

This document records the requested changes and acceptance criteria. It does not implement them. The side conversation made no detector-code changes and did not interrupt the main thread's existing investigation. Implement these changes in the main thread, alongside its existing work.

## What the current detector actually automates

The inspected implementation has genuine automatic search within supplied representations:

- `search.py` learns short programs from anonymous impulse-response tables. The learner does not receive operator names. Its assumptions include linear or bilinear behavior, short index expressions, small integer coefficients, and a restricted kernel grammar.
- `creative_search.py` enumerates words in supplied residue-space primitives, groups numerical matches, and probes relations at additional primes. Its enumeration currently uses ten primitives and words of length at most four.
- `estimate_search.py` generates twenty smoothing kernels and seven hundred growth hypotheses, fits constants on training scales, tests larger scales, and invokes available proof methods. The kernel construction and exponent families are supplied by the programmer.
- `cancellation_rewrite_search.py` feeds unresolved estimates into a supplied family of arithmetic rewrites and attempts certificates for the resulting bounds.

These searches do not need a separate prompt for each candidate. However, the programmer still supplies the primitives, search limits, fitting families, scoring criteria, and certificate methods. Several targeted experiments also select constructions and assert anticipated results. Such assertions can be useful regression checks; they do not establish that the result was independently discovered.

Treat the current system as a collection of bounded searches and guided experiments. It has not yet demonstrated an autonomous ability to develop a substantially different search language. Historical novelty and new uniform prime-distribution information remain separate requirements.

## Objective

Make numerical evidence, reproducible search rules, and independent evaluation drive candidate selection. A successful run should be able to return a formula or structural relation that the model did not nominate beforehand.

Complete absence of assumptions is not a meaningful acceptance criterion. A search always needs a representation, resource limits, and a selection rule. The practical objective is independence from model-selected candidate answers, with the remaining assumptions explicit and auditable. Familiar primitives can still generate unfamiliar mathematics.

## 1. Freeze the search protocol before observing outcomes

Create a machine-readable run specification before computing candidate scores. Record the grammar version, primitive semantics, enumeration or sampling rules, seeds, resource limits, data splits, numerical tolerances, and selection criteria. Hash the specification and candidate batches, and retain rejected candidates and rejection reasons.

Run the generator and selector without language-model calls, literature lookups, or access to anticipated answers. Model-written code necessarily retains design assumptions; document them rather than describing this as bias-free.

Use two explicitly recorded modes:

- A fixed baseline that enumerates or samples from a frozen grammar.
- An adaptive discovery mode whose mutation and promotion rules are frozen, but whose later candidate batches may depend on discovery data. Freeze each batch before its next evaluation.

Adaptive search must not use the final evaluation data. A reproducible seed alone does not prevent post hoc tuning.

## 2. Broaden the program language through general constructions

Start an independent search stage with typed programs over scalar index expressions, arithmetic sequences, and maps between representations. Make the initial language and exclusions explicit. Candidate productions can include arithmetic on indices, comparisons, integer quotient and remainder, bounded sums, rational scalar weights, composition, sequence products, and finite matrix operations with declared domains.

Permit signed combinations and nonlinear compositions. Do not require every intermediate construction to be multiplicative, associative, positive, invertible, or expressible as an Euler product. Those properties can become measured or proved outputs.

Keep finite semantics precise: declare cutoffs, lookahead, normalization requirements, singular-input handling, and operation costs. Finite array identities alone must not imply analytic convergence or preservation of ordinary zeta zeros.

Use cost-bounded enumeration for a small transparent baseline and reproducible stochastic exploration for larger programs. Track exploration of different production families so that the search cannot silently spend its entire budget on one familiar family. Random sampling inside a narrow language does not make that language broad.

Existing named operators can be calibration targets or optional starting modules. They should not supply the expected answer to the general discovery stage.

## 3. Infer structure from behavior, without supplying the target law

Collect response tables on the zeta coefficient sequence and unrelated rational or complex inputs. Test different scales, integer structures, residue sizes, and parameter values.

Use general algorithms to propose relations from those tables: sparse relation fitting, nullspaces, recurrence inference, response-kernel fitting, rank or spectral patterns, and cross-scale behavior. Record the feature dictionary used by every inference method; a narrow dictionary is another assumption.

An inferred relation should carry its training observations, fit residuals, complexity, numerical conditioning, held-out failures, and domain. Keep unstable fits and accidental finite matches out of the theorem registry.

Avoid assertions in the discovery path that require a specific anticipated formula. Keep named-operator recovery and expected-result assertions in a separate calibration or regression stage. The discovery runner should accept any admissible output supported by its protocol.

## 4. Preserve multiple ways for a candidate to be interesting

Maintain an archive across several criteria rather than optimizing only a score shaped around a familiar theorem. Useful criteria include predictive accuracy on discovery-validation data, description length, stability across scales and precision, algebraic structure, and information about actual primes beyond a declared baseline.

Distinguish nontrivial information from restatement: returning a prime indicator reconstructed from a supplied prime oracle does not establish a new prime-distribution estimate. Keep prime labels and factorization queries in an evaluator with explicit provenance when the coefficient producer claims to use no such oracle.

Keep RH relevance as a separate audit. An unfamiliar construction may deserve preservation before an ordinary-zero bridge is found. A zero-preserving rewrite may deserve mathematical verification without being counted as new arithmetic information.

## 5. Let useful inferred structure expand the grammar

Add automatic promotion of repeated useful subexpressions or learned relations into reusable productions. Use a declared rule based on reuse, compression, validation performance, and resource limits. A promotion must preserve the original semantics and store its dependency graph and evidence.

The selector should perform promotion without the model choosing a favorite expression. Label numerically inferred productions as conjectural unless a universal certificate exists. A compressed subexpression is a reusable program, not automatically a new theorem.

Run an ablation with promotion disabled. Compare whether promotion enables additional validated structures or more efficient discovery under the same resource budget. Increasing the number of names in a catalogue is not sufficient evidence of improvement.

## 6. Make evaluation genuinely separate from adaptation

Use separate discovery, discovery-validation, and final evaluation datasets. Generate fresh final evaluation cases after the candidate batch is frozen. The generator and adaptive selector must not read those cases or use their outcomes to tune the same run.

Test large and intermediate scales, irregular scales, unrelated generic inputs, and arithmetic families that break a candidate's apparent pattern. Check cancellation-sensitive results at higher precision or with interval arithmetic where appropriate.

Once final results have been inspected and used to revise the system, those cases become development evidence. A subsequent run needs fresh evaluation cases. Hashes establish integrity and provenance; they do not by themselves make data inaccessible or independent.

## 7. Keep discovery broader than the available proof methods

Give each candidate an explicit status, such as numerical lead, counterexample found, unresolved comparison, finite identity verified, universal arithmetic theorem proved, or analytic theorem proved on a declared domain.

Retain strong numerical leads that the existing certificate methods cannot prove. A missing proof method is distinct from a counterexample. Numerical growth fits cannot establish an estimate over every scale, and a proved finite-dimensional identity cannot establish an ordinary-zeta continuation theorem.

Make certificate attempts automatic where supported, and check successful certificates independently. Preserve the named dependencies of any imported theorem. A consequence of a supplied sieve theorem must not be presented as discovery of that sieve theorem.

Historical novelty, new independent prime information, and an RH-strength estimate require their own audits. Do not increase the verified-new count merely because the search found a previously unlisted program.

## Suggested implementation sequence

1. Add a separate search runner and generic program-language module. Avoid changing the semantics of existing verified stages while introducing this experimental stage.
2. Implement frozen specifications, deterministic replay, complete candidate provenance, and distinct data splits first.
3. Add behavioral relation inference and an archive supporting multiple selection criteria.
4. Add rule-based grammar promotion and its ablation.
5. Connect the archive to existing proof checkers without discarding unsupported numerical leads.
6. Run a bounded pilot, inspect its failures, then integrate its separately scoped results into the main report.

Possible filenames, subject to the main thread's implementation decisions: `autonomous_grammar.py`, `autonomous_search.py`, `check_autonomous_search.py`, and an `autonomous-results/` directory. These are proposed names, not existing implementation claims.

## Acceptance criteria

- The same frozen specification and seeds replay the same generated programs and selected archive.
- Candidate generation and selection require no model calls and no expected operator formulas.
- An anonymous known-operator benchmark demonstrates recovery, with named calibration results reported separately.
- A synthetic benchmark containing an operator unknown to the search's target labels tests recovery beyond the named calibrations. Use a separately generated or independently held target; a model-authored toy benchmark alone cannot demonstrate independence from the model's preferences.
- The generator's prime-oracle access, supplied mathematical features, and imported proof dependencies are inspectable.
- Automatic promotion is exercised and compared with a run in which promotion is disabled.
- Fresh final evaluation includes deliberate finite-pattern counterexamples and rejects at least the relevant false controls.
- Numerically promising candidates survive in the archive when available proof methods cannot certify them.
- No finite success is promoted to an all-scale bound without a universal argument, and no historical novelty is inferred from unfamiliarity.

The first pilot may yield only known operators or unresolved leads. Report that outcome faithfully. The key initial deliverable is a reproducible discovery process whose outputs are not selected one by one by the model.
