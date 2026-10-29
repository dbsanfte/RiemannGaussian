# Constructed Boolean multiplication relation: proved scope

New module: `RiemannGaussian/SemiprimeBooleanNetwork.lean`. No earlier repository modules or frozen evidence modified.

## Concrete correctness bridge

- `encode`/`decode` are standard `BitVec.ofNat` / `BitVec.toNat`, hence literal least-significant-first binary words, not an arbitrary cardinality enumeration. `decode_encode`, `encode_decode`, `wordEquiv`, `bit_ports_bijective`, `bitPortsEquiv` prove exact finite-width/canonical and Boolean-port bijections.
- `operand` is the actual radix digit sum. `operand_succ`, `operand_bound`, `operand_injective`, `operandEquiv` prove that the fixed digit array represents **each** integer in `[0,(2^bits)^digits)` exactly once. The inverse of `operandEquiv` is obtained by finite bijectivity and carries no algorithmic cost claim.
- `Extension` has actual `(n+1)`-bit coefficient words, **n-bit** carries including both boundaries, and two Boolean nontrivial flags. Coefficients are constrained below the Fermat modulus; carries fit below `2^n` by the prior strict quarter-capacity theorem. `Valid` uses literal normalized inverse/point-product expressions and INTEGER carry equations. No convolution-correctness or graph-semantic equivalence is assumed.
- `valid_sound`, `valid_complete`, `valid_unique` prove soundness, existence and unique bit extension for each nontrivial product. Existence derives coefficient and physical carry bounds from the actual quarter-radix hypotheses and the arithmetic module. `extension_count` proves contribution exactly one or zero.
- `Check` explicitly enumerates individual canonical, inverse, carry, endpoint and flag vertices. `localCheck` spells out their predicates; `localEntry` is their actual 0/1 value. `valid_iff_local` and `local_product` derive the local tensor-product semantics.
- `local_contraction_counts_factor_pairs` proves the displayed local Boolean tensor-product contraction is exactly the number of ordered nontrivial **integer** factor pairs below the input capacity, with target integer the displayed public target-digit sum. There is no count oracle premise.
- `equality_subdivision_count` proves that inserting one Boolean equality relation per duplicated edge has exactly one copy extension and preserves the contraction. Together with `bitPortsEquiv` this applies to literal ordered bit ports, not only abstract words.

## Numerical hypotheses / remaining compiler interface

The count theorem requires `n=macroLength d=4*bits`, `bits>0`, `digits<=bits`, and public target digits `<2^bits`. It concludes target `N_target=sum_k target[k]*(2^bits)^k`. To identify it with the compiler's supplied N and include **all** nontrivial factors, the public parameter/digit bridge still must establish `N_target=N` and `N<(2^bits)^digits` (plus the compiler's specific n/d choice). These are numerical obligations, not an assumed network semantic theorem.

The constructed finite relation is explicit but **does not have the frozen compiler's small-port/linear-wire bound**. Each inverse predicate directly reads the input digit arrays (and one output coefficient), using the normalized dense DFT expression already proved arithmetically correct. The flag predicate directly tests the decoded operand >=2. The actual compiler instead has first-stage DFT, twiddle and second-stage DFT intermediate word arrays and digit/OR-chain flag vertices. Those exact intermediate arrays and port-index wiring are not yet constructed/formally related here. The per-inverse scope can be O(L) rather than O(L^(3/4)); copying its repeated inputs and equality subdivision does **not** restore the missing O(L) total-incidence bound. Therefore this module closes concrete Boolean counting semantics, but cannot yet substitute for the small-port compiler in the subexponential resource proof.

Next narrow task: add canonical first/twiddle/second stage word arrays and their local predicates, derive unique extension from `macroFourier_eq_fourier` (and its inverse/reflection), replace global flags by the concrete digit/OR chain, and prove the explicit original/subdivided port graph has the intended occurrence and size bounds. The current word and digit bijections/count proofs can then transport that graph's arithmetic relation without assuming correctness.

## Verification

Strict standalone compile (`-DwarningAsError=true`) with output `.olean`; root+leaf `#lint+` and generated-declaration/transitive-axiom audit in `CheckBoolean.lean`, output `boolean-audit.txt`. Only standard axioms permitted; no sorry/custom axioms/native_decide. External full build not restarted. No full truth tables or finite factoring controls used as mathematical proof.
