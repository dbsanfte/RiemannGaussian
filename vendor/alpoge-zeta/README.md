# Alpöge’s zeta estimates and Landau criterion

The optional verification script selects source files from Levent Alpöge’s Lean archive. The concatenated archive has SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Paths in this directory reproduce the original `lean/src` tree. [Author’s announcement and archive links](https://alpo.ge/remark.pdf)

| Verifier option | Archive modules selected | Use |
| --- | ---: | --- |
| `--global-landau` | 20 | Prime deficit, prime versus integer discrepancy and quadratic class at every fourth power |
| `--cubic-samples` | 20 | A uniform bound on the averaged prime tail at fourth powers |
| `--fixed-prime-band` | 27 | Ordinary-prime shortfall on cofinal windows |
| `--prime-band` | 25 | Prime harmonic estimate and converse |
| `--window-mass` | 35 | Cofinal positive-deficit, prime versus integer discrepancy, quadratic class and signed correlation criteria |
| `--principal-level` | 33 plus one definition slice | Direct zeta implication from windows on the geometric principal cyclic level |

The fixed-band selection has manifest SHA-256 `7430a8ef8f18ee8cb30fe17653c2cc72b554c2680ab7763bbc8787c81adf9652`. The 20 and 25 modules for the global arguments are verbatim. The full directory holds 56 files across the overlapping selections. The window argument uses 31 additional analytic modules. In the archived `mellinGchiOfNeOne.lean`, two `convert` tactic sites needed adjustment for Lean 4.34.1. Its original SHA-256 is `22192caa33f0e9b840298329573ca3ea15e3e5d9e60624efcda3562f8ddff26a`. The port has SHA-256 `617c8156fb27da037303aa8ea169cfc8c335b2e0b2c0e6afbedd6da18bdbbc4c`. All theorem statements are preserved. The manifest digest for the 35-module window argument is `8db2c39e811def552dc2ec2e178e351a806095723c8757c1c66b05acc674fb9e`. The 25-module global manifest digest is `a89aec6d6db8c954706cec21d4bbcc3243450a911010d55306a76f3d075de712`.

Run `python3 scripts/verify_alpoge_mined_bounds.py --window-mass` from the repository root to check the cofinal window criterion. [Verifier](../../scripts/verify_alpoge_mined_bounds.py) and [fixed-band arithmetic route](../../docs/arithmetic-proof-shortening.md)

The fixed-band verifier checks the pinned source bytes, then substitutes
specific Mathlib imports for `import Mathlib` in temporary copies of
`DedekindLFunctions.CharFamily` and `GammaFactorNonvanishing.RhOfRight`.
It elaborates and replays all 27 selected archive modules using the original
declaration text in both copies. [Fixed-band verifier](../../scripts/verify_alpoge_mined_bounds.py)
