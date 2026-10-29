# Primitive Boolean arithmetic connector for actual macro entries

New owned file: `RiemannGaussian/SemiprimeMacroEntryBitPrimitives.lean`; frozen `SemiprimeMacroEntryExecution.lean` is unchanged.

## Executed arithmetic, not unit-cost annotations

`Expr` contains physical Boolean literals and addition/subtraction/multiplication constructors. `execute` really calls `fitBits`, `residueAddBits`, `residueSubBits`, and `modMulBits` (the latter executes Boolean multiplication plus restoring division). It never calls `bitValue`, native decoded addition/multiplication/modulo, or a desired ring evaluator in its data path. Every child and backend clock is accumulated, including the report/reference overhead. `meaning` is only a proof specification.

For a positive physical modulus and canonical input literals, `execute_bounds` proves fixed modulus-width canonical outputs, `execute_correct` proves the exact ring expression value, and `execute_clock` bounds the full primitive bit backend clock by

`nodes(expr) * (128*(W+1)^2+128)`.

`nodes` explicitly counts repeated child traversals; no shared subexpression cache or free packed evaluation is assumed.

`powerExpr` compiles powers to actual modular multiplications; exact syntax size is `1+e*(nodes(base)+1)`. `dotExpr` compiles the actual polynomial DFT output. Under count,stride,frequency <= n its syntax size is at most `1+count*(4+n^3*(nodes(base)+1))`. `execute_dotExpr` simultaneously gives the DFT formula, canonical fixed-width output, and explicit polynomial BIT primitive clock. The only supplied statements are canonicality of actual input words, index bounds and a finite literal base expression; there is no supplied evaluator correctness/performance oracle.

`portBits_value` connects actual ordered port lists to the frozen public binary decoder. `equalBits` uses two real borrow comparisons, with exact integer equality and <=24W+7 clock. `lessBits` uses a real subtractor final borrow, exact strict inequality and <=12W+3 clock. `carryEquationBits` executes a physical power-of-two shift, two ripple additions and equality; its specification is the INTEGER carry equation, with no modular weakening, and its clock is <=100W+100 when offset/input words have length <=W. `residueEqualityBits` executes both compiled ring expressions and the final physical comparison, proves exact equality of their ring meanings using canonicality, and charges the whole primitive cost.

## Remaining full entry assembly (not claimed proved)

These theorems now supply every expensive arithmetic primitive needed by the executable local table, but there is not yet a single theorem that its full ordered vertex checker is the composed bit program with a polynomial global clock. The exact next construction is:

1. Construct the physical modulus using existing `fermatModulusBits (replicate n false)` (its value/width/construction clock already proved). Generate root four with literal `[false,false,true]`, inverse root via `powerExpr root4 (n-1)`, and inverse normalization via zero minus the power of literal two at exponent n-(depth+1). All validity proofs reduce to the actual Fermat modulus, not primality.
2. For each actual source/DFT/scale/product/carry/OR/check role, gather `portBits` in the already proved ordered offsets. Perform `lessBits` canonical/source-width gates BEFORE invoking the canonical-expression correctness theorem; invalid words must yield false, not a promised valid input oracle.
3. Use `dotExpr`/`residueEqualityBits` for every DFT output, scaling and point product; `carryEquationBits` plus strict bounds for carries; literal Boolean gates for flags. Fold every finite array of checks with an executed AND and accumulated clocks, charging input-word copying and loop/index operations.
4. Prove the resulting Boolean result equals `executableEntry` by vertex cases using the already frozen table equivalence. Sum the bounds with actual r,t<=n and word width n+1. This is a deliberately polynomial, not FFT-fast, local entry implementation: high polynomial degree is harmless for the intended subexponential counter asymptotics, but no such full clock theorem is imported before that composition.

Thus this is a concrete backend connector and proof reuse plan, not a completed whole-entry or whole-counter primitive runtime theorem. The whole counter's rational height/storage and source-layout execution are additional independent interfaces.

## Final validation

Strict autoImplicit=false/warningAsError=true compile PASS. All 15 scoped root linters PASS. All generated declarations/transitive axioms audited: 180 declarations, 89 theorems, only standard propext/Classical.choice/Quot.sound. Audit source/log and individual build log are adjacent.
