# Exact symbolic replay of cancellation formulas

26 October 2026. Standard-library Python only, scratch only. No semiprime fixtures, factoring-success campaign, dependency installation or repository edits.

Replay from the formal repository root (write results outside the frozen packet):

```sh
python3 docs/research-evidence/semiprime-packed-residue-20261026/check_cancellation_identities.py --output /tmp/semiprime-cancellation-replay.json
```

Result: **14 exact coefficient checks passed.** The checker represents multivariate polynomials as sparse exponent-tuple dictionaries over Z and clears all rational denominators before comparison. No floating-point evaluation or random substitutions are used.

Checks cover the unregulated Ward determinant cancellation; regulated Schur numerator; opposite-replica sign; universal adjacent Casoratian and its finite three-step telescoping instance; cone Cayley factorization (8); both full/noncovariant Wronskians treating K,K_r,K_T as independent formal symbols with the displayed source derivative rules; and the replica-reset DJ log-jet simplifications. The DJ portion additionally checks a physical two-leaf determinant/weighted adjugate and the exact formal P=0 substitution in the general jet formulas. Its arbitrary-rank determinant lemma and physical log-jet derivation remain paper proofs, not claims about a large emitted symbolic leaf matrix.

The JSON records each check's scope and inputs. This validates the cleared coefficient algebra only. It does NOT validate native unit/order premises, componentwise Laurent extraction, coverage, factorizations, gate decisions or complexity. In particular a checked cleared ratio does not license division by its denominator at a singular composite-ring specialization.
