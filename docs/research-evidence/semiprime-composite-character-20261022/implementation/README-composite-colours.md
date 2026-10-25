# Composite-colour reference metadata

`composite_colours.py` implements only the public prime selector, individual prime screens, canonical unit rows, and the complete CRT square-colour lists from `../composite-colour-catalog.md`. It neither prepares gamma nor computes long H values, Gauss target families, or a full factorization algorithm. It does not certify that the input is semiprime.

Run from this directory:

```sh
python3 composite_colours.py 1009
python3 -m unittest -v test_composite_colours.py
```

Import `preprocess(N)` for the integrated metadata result. `canonical_rows(N,m)` and `catalog(m)` also work independently for supplied odd composite moduli. `catalog(m)['palettes']` is a dictionary from tuples of local Legendre signs (prime factors ordered increasingly) to sorted explicit residue lists. The CLI converts tuple keys to a JSON list. Row fields `E=N+a+ell` and `e=E-m*m*kappa` distinguish the unnormalized and translated target exponents; row `ell` is a linear coefficient, not the auxiliary-prime field named `ell` at the top level.

Selection uses exact integer sixth roots and repeated doubling Eratosthenes sieves, returning the first prime ell strictly above twice that root with ell=3 mod4. Put m=(ell-1)/2, so m is odd and m^6>=N. The asymptotic soft metadata bound uses the independently reviewed public-prime supply bound ell=O(N^(1/6)); the code has no assumed cap and doubles until it succeeds. Sieve work through the final limit is soft O(ell). Each distinct known prime dividing m and ell is screened individually against N. A proper result returns `FACTOR`. Equality of N to a public prime returns `INPUT_EQUALS_PUBLIC_PRIME`, not a spurious proper factor. The latter cannot occur for the intended distinct-prime semiprime contract.

For the coprime branch the catalog marks square residues by enumeration at each prime power, constructs the two local colored lists including their common zero, and combines them by CRT Cartesian products. It never loops over every global residue for every color. With T the final colored output count, T<=m(1+log m), local scans total at most m, and CRT pair visits total at most 2T. Intermediate colors and final lists are genuinely materialized. Per-row inverse/Legendre operations and exact canonical identities cost polylogarithmic arithmetic per row/prime factor. Sorting and all output descriptors add logarithmic factors. Thus structural arithmetic/output work is soft O(m+J) for polynomial-size native integers. Python's runtime is not a formal fast-integer complexity certificate; the soft bit ledger assumes fast integer arithmetic where necessary. No quadratic palette generation is hidden behind the reference implementation.

The `ledger` reports row, color, residue-output, local-scan and CRT-visit counts and explicitly records zero long-H values. The five test groups check exact prime-power/squarefree masks against direct quadratic images, zero/nonunit residues, true-tag integer coverage on deliberately small algebraic inputs, sieve minimality/contracts, individual-prime saturation repair, and exact bounded antipodal sums. These are bounded correctness checks, not a success-rate campaign or evidence for a universal factoring bound. They make no large-order/prepared-gamma claims about their small inputs.

For intended native application, the independently reviewed source bound is 13<I<(17/16)m²+3<4m² on the retained branch P<=Q, P,Q>16m², N<=m^6. This implementation supplies the algebraic masks but does not verify those hidden-factor hypotheses. Original gamma preparation, original exponent-gap/annihilator recovery, and the missing simultaneous H evaluator remain external contracts. No optional PackedGauss wrapper is included; the separately owned `composite_gauss_aggregate.py` may consume the row/catalog API without copying frozen code.
