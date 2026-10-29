# Actual integer parity/binomial coefficient acquisition

New modules: SemiprimeBinomialExecution, SemiprimeBinomialExecutionTracked, SemiprimeBinomialExecutionBounds. Frozen vendor/source files were not edited.

## Exact initialized supplier

The lower Pascal solution is explicitly z_s=(-1)^A*(-2)^s. `lower_spec` proves L*z is the alternating target by the finite binomial theorem, including the zero extension beyond each row degree. The upper U solve is a reverse-index cached unitriangular convolution: every next coefficient is its acquired target minus a finite dot product of PREVIOUS cached coefficients. There is no division or general Gaussian inverse. `upper_spec` keeps U's essential below-diagonal zero condition and proves the actual recurrence solves U*c=z. B=L*U and determinant-one uniqueness then prove `parity_eq` to the existing integer BinomialInterpolation.parityCoefficients.

The runtime coefficient function has only A,R as arguments. No matrix, polynomial, supplied target coefficient vector or inverse oracle is required. `chooseRow` itself builds Pascal rows by cached addition; it does not execute Nat.choose. Matrices and noncomputable inverse coefficients occur only in the correctness proof.

The preferred fully tracked supplier also acquires (-1)^A by A actual negations and the lower target powers by a cached multiply-by-minus-two recurrence. Its executable API is `acquiredParity A R : Fin R -> Int`, with `acquiredParity_eq` to the SAME vendor vector. All sources are initialized internally.

## Work

The upper solve reports exactly R² integer arithmetic calls and R² coefficient/target reads. The full tracked acquisition reports arithmetic `A*(R+1)+A+R+R²` (Pascal additions, sign negations, target products, solve) and conservative read ledger `2*A*(R+1)+R²`. The Pascal read report charges even its unused zero-boundary read, so it is an upper ledger, not an assertion that the branch actually reads that extra cell.

Array construction, pushes/copying, loop/index arithmetic and integer BIT costs are separate from this scalar/read ledger. Every loop has polynomially many iterations in NUMERICAL A,R: Pascal A*(R+1), target R, upper solve R². Array pushes may copy their entire retained prefix without changing polynomiality. Retained integer sizes are proved below, so schoolbook integer arithmetic gives a constructive polynomial bit algorithm in A,R. This is not a polynomial-in-log(A) claim for arbitrary binary A. On the actual source branch A<=Q, and Q,R are the paid public layout parameters.

The earlier core `parity` also acquires Pascal and the solve, but constructs targets by ordinary integer powers. Charge an additional conservative O(R*(A+R)) integer products for that core path. The optimized tracked acquisition count must not be silently assigned to a caller that still uses the core path. The universal-row wrapper currently caches core coefficients once per requested row and may repeat acquisition across rows/constraints; the full matrix size times this polynomial work must be paid. A caller can instead hoist `acquiredParity A R` once and pass its coefficient closure to the generic entry/row(c) frontend.

## Integer and scratch heights

`chooseRow_bound` bounds every acquired Pascal entry by 2^A. `solve_bound` bounds every coefficient of EVERY cached solve prefix by Z*(total*M+1)^len for kernel entries <=M and target magnitudes <=Z. `dot_bound` bounds every finite scalar dot prefix BEFORE cancellation. Applied to parity M=2^A and Z=2^R, every final coefficient has

`|c_j| <= 2^R*(R*2^A+1)^R <= 2^[R*(A+clog2(R+1)+1)]`.

The same bound is proved for the fully tracked acquired vector. The retained next lower target power has magnitude 2^R. All quantities are INTEGERS, with common denominator 1; there is no denominator-growth or unknown-unit condition. A dot product's raw product/subtotal and the target subtraction add only O(A+log(R+1)) bits to the displayed coefficient envelope. Pascal intermediate rows at stages a<=A are bounded by 2^a. Hence every actual integer arithmetic input/output is polynomial-bit in A,R, independently of lucky cancellation or an output-size oracle.

## Validation and scope

All three individual strict builds PASS (autoImplicit=false/warningAsError=true). Root import plus all15 scoped linters and all-generated/transitive axioms PASS: 222 declarations, 111 theorems; standard propext/Classical.choice/Quot.sound only. No noncomputable runtime definition is used. BinomialSmoke executes the acquired function directly, including empty/singleton cases and alternating-value controls; captured outputs and the pure API type are adjacent. These are local diagnostics, not a factorization/performance campaign.

This pays the actual source binomial/parity solve. It does not prove the full public source constructor or the entire counter's primitive-machine runtime. The arithmetic/read ledger and integer bounds support that later composition without a supplied coefficient oracle.
