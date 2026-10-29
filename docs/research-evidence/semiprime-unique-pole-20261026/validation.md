# Exact diagnostics for the selected-pole identities

26 October 2026. Run from the formal repository root:

```sh
python3 docs/research-evidence/semiprime-unique-pole-20261026/check_pole_identities.py --output /tmp/semiprime-unique-pole-replay.json
```

The standard-library script uses exact arithmetic in F_101, q=2 and a six-point clock. It compares the executed companion-polynomial recurrence against independently formed dense multiplication matrices and determinant cofactors. Six row fixtures include a unique hit, repeated nonhit roots, no hit, and multiple hits. All steps, including singular ones, are checked. The separate Newton divided-difference recurrence and final positive-sign locator are compared against those values.

Other checks clear the barycentric row identities as polynomials, compare the selected modular-inverse coefficient against a direct finite sum, verify reciprocal-product factors and frozen-numerator residues, and test the finite Pearson endpoint identity. Six little-q-Jacobi lengths check both terminal polynomials, the numerator monomial, nonterminal unit coefficients and the zero terminal coefficient. One arbitrary-state diagnostic shows that equal top two coordinates do not determine the next evaluation for arbitrary polynomial states; it is explicitly NOT an attained native counterfamily or a lower bound.

All 264 checks passed. The full counters are in [pole-identity-checks.json](pole-identity-checks.json). The scripts intentionally use small direct algorithms as independent diagnostics; they are not the proposed production implementation or evidence for a scaling rate. Composite-ring guards, uniform native coverage, the mixed-relation decoder and bit complexity are reviewed paper arguments. No factor-field simulation, native order acquisition, factoring-success campaign or Lean build was performed.
