# Accumulated research checkpoint, 25 October 2026

This checkpoint publishes the local Suzuki proofs, semiprime research evidence,
and existing engineering proposals at the user’s request. It does not claim a
complete RH proof or a guaranteed sixth-exponent factorization algorithm.

The 14 Suzuki modules are registered in the ordinary library. The strict build
and the scoped audit passed for 236 declarations, including 215 theorem
declarations and generated helpers, with 15 declaration linters per module and
only the standard axioms. The conditional RH transfer retains its unproved
subpolynomial arithmetic premise; the explicit three-eighths estimate does not
close that premise.

- [Full declaration audit](suzuki-lean-audit.json)
- [Checked source fingerprints and commands](suzuki-validation.json)
- [Constructor algebra self-test](fermat-cover-self-test.json), run with
  `../.venv/bin/python scripts/probe_semiprime_fermat_multiplier_cover.py --self-test`.
  These finite checks validate the implementation, not a factoring rate.
- [Portable semiprime recurrence checkpoint](../semiprime-recurrence-checkpoint-20261025/README.md)

The repository’s tracked commit hook checks the ordinary build, declaration
linters, compiled project status, generated explorers, campaign update, and
plots. Browser checks exercise the current desktop and mobile views. Remote CI
and Pages are verified against the exact pushed commit separately; this file
records the source checkpoint rather than predicting their result. Exhaustive
optional numerical-certificate verification is not part of this publication.
