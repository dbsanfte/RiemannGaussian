# Actual generated interpolation instruction safety

NEW `SemiprimeSourceArrayProgramSafe` and `SemiprimeSourceArrayCompilerSafe` only. No frozen source edits.

The first module proves safety of actual emitted addCode, dotCode, and full mulCode. It accounts for BOTH scalar operations per convolution term: the individual stored multiplication product and every chronological partial accumulator. It does not infer temporary safety from the final coefficient or from cancellation. Internal compositional `*_safe_known` lemmas accept exact original scalar products/prefix expressions, and are discharged from original representations by the whole-source specialization in the second module.

`compile_safe` follows the ACTUAL cached-child AST compiler and its actual updated environments. Both child code sequences are composed via safe_append. Initialized output IDs and their exact coefficient values follow the independently proved actual compile_spec. Register preservation carries original zero/one/literal inputs through every child prefix. Original leaf bounds and original full-tree node cap provide one common denominator/numerator cap for every subtree.

Crucially, an individual multiplication product is a length-one original convolution slice; an accumulator is a length-m slice. Frozen subtree_convolution_slice therefore bounds both with the same full-tree original cap. This avoids the spurious doubled-node width that would result from treating independently lifted child bounds as unrelated. Addition outputs are original parent coefficients. No supplied intermediate Fits/state/minor answer appears in compile_safe.

`source_safe` specializes to the ACTUAL SourceInterpolationExecution.code using executed parity coefficients, actual unit sample prescriptions and the proved original Leaves/node count. ALL emitted scalar instructions fit at exactly stateBits A Q R+1. Original caps are proved ≤2^stateBits; one extra physical bit makes the required strict fits. SourceArrayProgramLowering.lower_safe/run_refines can now consume this theorem instead of assuming Safe.

`literal_representation` follows the actual constants traversal. `source_literal_bounds` proves every literal in the actual original code has reduced numerator/denominator ≤2^stateBits. This supports root's concrete initial bank encoder; it does not assume a pre-encoded word bank.

Remaining joins: actual initial-bank construction/encoding and lowering are owned separately; full producer/control/public integration and whole source-machine clock are not claimed by these safety theorems. Existing scalar literal acquisition/digit extraction and primitive scratch/address implementation remain governed by their explicit existing boundaries. No second arithmetic backend is introduced.

Status: final SOURCE FROZEN. Canonical strict/root15/all-generated std3 PASS61decl61thm. After upstream IR/Blocks/Compiler final freeze, both canonical strict builds were refreshed and both isolated strict objects remain byte-identical. Final source/object/dependency pins recorded. Exact pins in array-program-safe-verification.json.
