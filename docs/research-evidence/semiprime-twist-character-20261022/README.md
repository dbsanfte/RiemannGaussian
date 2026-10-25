# Twists and characters: 22 October 2026

This packet records the resumed semiprime investigation at repository base
`6e969fd6`. The user specifically prioritized colour, twist and character
cancellation. Its constructive result is a whole-query Cayley transformation
whose complete unit correction costs soft O(J+sqrt(L)). The transformed
collision product still needs acquisition; no improved all-input factoring
exponent or new Lean theorem is claimed.

## Start here

- [Paid Cayley companion](reports/cayley-paid-companion.md): every original
  local collision survives, the full correction is acquired without a
  length-L seed list, and reciprocal arguments become negatives.
- [Retained Gaussian lift character](reports/corrected-cross-order-root.md)
  and its [independent review](reports/independent-retained-lift-character-review.md):
  a computable quartic phase survives on a lift, with an exact cross-order
  cancellation law. The corrected map kills this global character in one
  step; it supplies no further phases under literal iteration.
- [Selected-shift overlap screen](reports/selected-shift-overlap.md): a
  supplied shift can be tested against every canonical anchor in soft O(J),
  including localization when the hidden fields choose different partners.
  A universally useful small shift collection remains unacquired.

The [higher-symbol report](reports/cross-twist-symbols.md) keeps the extra
quartic/octic phases and their actual public-input algorithms. The
[anchor report](reports/actual-anchor-overlap.md) and
[normalization review](reports/normalization-and-chain-review.md) charge
outside-product center normalization and its resulting varying strides.
The [discriminant sieve](reports/paid-discriminant-sieve.md) strips the
known square content from the actual integer-root equation and charges
CRT enumeration. The [character-algorithm audit](reports/character-algorithm-audit.md)
and [structured identities](reports/structured-twist-addendum.md) retain
the hypotheses of the inspected literature. None supplies the missing
universal acquisition bound.

## Replay and scope

From the repository root, the optional algebraic convention checks run as:

```sh
python3 docs/research-evidence/semiprime-twist-character-20261022/probes/check_corrected_root.py
```

That script also runs `check_formulas.py`: 1120 local Gaussian checks,
1012 reciprocal-parameter checks, 92 octic checks, and 548 corrected-map
checks with four iterations. The defining local symbols use supplied
primes only in the test oracle; the Gaussian symbol algorithm itself uses
public Gaussian numerator and denominator inputs.

The implemented Cayley companion reuses the existing GMP-packed
`MonicBatch` backend. Use Python with `gmpy2` installed:

```sh
.lake/plot-venv/bin/python docs/research-evidence/semiprime-twist-character-20261022/probes/check_cayley_companion.py --repo-root . --test
```

The 96 deterministic controls compare the acquired companion with literal
products, cover all four gcd masks modulo 77, and include empty products,
repeated evaluation points and five invalid-domain rejections. Reference
prime factors occur only in controls. The production routine consumes
the prepared-subgroup promise; unit checks do not certify that promise.
It generates block seeds and evaluation nodes of order sqrt(L), with no
full length-L seed list. Its counters record this work rather than a
measured complexity exponent.

These checks validate algebraic conventions and composite-ring arithmetic.
They do not establish coverage of semiprimes, an asymptotic factoring rate,
or a Lean proof. No benchmark campaign or ordinary CI target is added.
See [validation.json](validation.json) for the root replay and review scope.

## Provenance

The report files are verbatim scratch reports from the three authorized
Sol 6.1 investigations and independent reviews. References to their old
`/tmp` paths and statements that those agents made no repository edits are
historical; the portable copies are listed in
[archive-provenance.json](archive-provenance.json). The archive preserves
their text instead of presenting a later relocation as a fresh validation.

[source-pins.json](source-pins.json) fingerprints the five external primary
PDFs without copying them. The main journal supplies the exact scope of
the inherited QRH input; this packet adds no analytic assumption or
zero-free-region claim. The manifest covers this packet's final text and
probe outputs, with the existing backend pinned separately. Earlier
frozen packets and public proof metadata are unchanged.
