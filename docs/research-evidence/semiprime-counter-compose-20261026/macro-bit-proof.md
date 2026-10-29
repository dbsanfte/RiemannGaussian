# Actual macro-array and OR-chain bridge

New owned module: `RiemannGaussian/SemiprimeMacroBitNetwork.lean`. Earlier modules and frozen evidence unchanged. Read the frozen `factor_network.py` source, especially `transform`, `make_input`, and equality subdivision.

## Proved actual stage arithmetic

`ResidueWord` is the canonical subset of literal `(n+1)`-bit words. `residueWord`, `residueValue_word`, `residueValue_injective` establish a real binary/ring encoding with no primality assumption or arbitrary finite enumeration.

`MacroArrays` explicitly contains first DFT output `(j1,k2)`, twiddle output `(j1,k2)`, and second DFT output `(k2,k1)`. `MacroValid` is the actual three-stage equation system from the compiler: source slot `j1+r*j2`, first root `w^r`, twiddle `w^(j1*k2)`, second root `w^t`, and normalizer only at the second stage. Each first DFT gate can bundle all t outputs, and each second DFT gate all r outputs; the displayed per-output equations are their conjunction, not independent new physical signal families.

`buildMacro_valid` derives existence; `macro_valid_unique` derives uniqueness of **all canonical intermediate bits**. `macro_valid_output` derives equality with the flat DFT through the already proved arithmetic macro identity, rather than assuming transform semantics. `macro_extension_count` proves that introducing these actual intermediates preserves the zero/one contribution for any downstream predicate on final words.

`flatOutput` uses the literal `k=k2+t*k1` finite-index equivalence. `flatOutput_value` proves the normalized flat output equation. `inverseRoot=4^(n-1)` is public and `inverseRoot_mul` proves it is the actual inverse of four; `inverseRoot_period` and `inverseRoot_power` prove all period/reflection relations. `macro_valid_inverse` / `flatOutput_inverse` derive **exactly** the normalized inverse equation of `SemiprimeMacroFermatNetwork`, including zero-frequency reflection. `length_normalizer_exists` derives its existence from the previously proved ring unit, not a field/oracle premise. No unknown-order/root-of-unity assumption occurs.

## Proved actual flags

`orOutputs` constructs the actual sequential one-bit OR outputs. `OrValid` gives the local equations and exact output-list shape. `or_valid_iff`, `or_unique_extension`, `or_output_length`, `or_terminal` prove existence, unique bits, one output per non-initial digit, and the exact terminal flag.

`digit_tail_positive` and `digit_or_nontrivial` prove the actual lowest-digit >=2 / higher-digit !=0 convention. `input_digit_evaluation` links the literal little-endian digit list to the previous operand definition. `actual_input_flag` proves the digit flags and OR-chain replace the previously direct decoded-operand nontriviality test. This is not an assumed flag-semantic equivalence. Actual source top-digit narrower width is still a public input-range refinement, not proved by this module.

## Exact concrete signal and scope counts

The tagged `WordSignal n` family is exactly: 2n input words, 3 stages times 3 transforms times n words, n point-products, n+1 carries. `word_signal_count` proves `13*n+1`.

`FlagSignal digits` is exactly 2*digits digit flags and 2*(digits-1) OR outputs. With digits>0, `flag_signal_count` proves `4*digits-2`. Each word has n+1 actual bit ports, each flag one. `signal_bit_count` therefore proves

`(13*n+1)*(n+1)+4*digits-2`.

`subdivided_bit_count` proves twice this count under the explicit two-host equality-copy signal type. This is a cardinality theorem of the concrete generated/tagged signal family, not a theorem that an arbitrary builder has exactly two endpoints per bit. The existing Boolean module separately proves equality subdivision preserves counts.

`arithmeticArities` gives first DFT `2*t*(n+1)`, scale `2*(n+1)`, second DFT `2*r*(n+1)`, product/carry `3*(n+1)`. `arithmetic_arity_bound` proves their uniform bound `(2*(r+t)+3)*(n+1)`. The public balanced-axis bounds relating r,t to sqrt(n), and n^2 to original input bit length, remain numerical compiler obligations; no O(L) or runtime theorem is inferred merely from the count formula.

## Exact remaining integration boundary

This is a substantive small-port **stage and signal-family** bridge, not yet a single accepted-assignment/count theorem for the frozen compiler graph. Still needed: assemble both forward transforms, products and inverse transform with the digit/carry relation; instantiate `macro_extension_count` through that whole shared intermediate network; give each tagged bit its actual unique producer/consumer port and prove the endpoint bijection; integrate actual digit/OR-chain outputs and final checks; prove top-input-bit limits and actual public parameter selection; apply equality subdivision to the complete graph; establish balanced r/t and linear-wire bounds in original bit length.

In particular, the exact signal-family count plus the earlier larger-relation factor-count theorem is **not yet** a proof that the frozen small-port graph has that same contraction. No generic semantic-equivalence hypothesis, counter oracle, free dense array, or runtime assertion is inserted to cover this gap. The next task can now focus on graph assembly/port indexing rather than re-proving Fourier, inverse, canonical-bit or OR arithmetic.

## Verification artifacts

Strict individual compile: `macro-bit-build.log`; root+leaf scoped 15-linter/generated-declaration/transitive-axiom audit: `CheckMacroBit.lean`, `macro-bit-audit.txt`. Only propext, Classical.choice and Quot.sound permitted. No sorry/custom axioms/native_decide; external full build not restarted.
