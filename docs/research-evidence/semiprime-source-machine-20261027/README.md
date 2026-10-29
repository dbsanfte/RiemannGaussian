# Addressed source simulation and remaining source structure, 2026-10-27

Status: **verified constructive progress; complete original-input primitive-bit scaling remains open**.

This packet adds an executable finite rational-instruction interpreter whose operands are acquired through Boolean-address scans. Each visited payload is copied, every address test/decrement executes, and every instruction runs the existing physical arithmetic/GCD/fitting circuit. A complete memory copy preserves each store version, so the bound assumes no free sharing. Exact value, validity, register-growth, physical-width and polynomial report bounds are proved.

The actual twelve-instruction source-offset block is the first concrete refinement through this interpreter. All intermediate fit conditions follow from original source-scale/offset bounds, including the two reciprocal intermediates. It has literal four-bit operand addresses, seven initial registers and nineteen final registers. Its returned first word equals the original `offsetRun` value. A further theorem substitutes the actual scheduled scales and original universal bank into a fixed polynomial resource bound for this block's reported Boolean work. Its conservative width is acceptable because those scheduled magnitudes are themselves polynomial in the original materialized resources; no such claim is made for arbitrary binary-sized magnitudes.

Seven initial physical registers remain an explicit acquisition interface. The existing public caller is unchanged. This block and interpreter are not a completed lowering of the entire source algorithm or a whole-machine runtime theorem.

Parallel proofs close specific source-structure gaps: all actual Pascal/target/solve/raw-arithmetic prefixes and their stored payload/counter bounds; actual packing/address/block/name IDs and allocation-to-report bounds; and actual copied-word/universal enumeration backing, payloads and original indexed dimensions. Both executed indexed word producers remain charged. Payload and persistent-store views remain distinct from a complete heap, stack, pointer or circuit-scratch representation.

All eight new modules pass strict compilation, ordinary-root linting, all-generated standard-axiom audits and byte-identical isolated recompilation. See the [verification record](verification.json) and [manifest](manifest.json) for exact counts and actual compiler-import source/object pins.

Read the [packing state notes](packing-state-notes.md), [parity state notes](source-parity-state-notes.md), [enumeration notes](enumeration-state-notes.md), [offset refinement](offset-program-notes.md), and [next compiler/state joins](next-source-machine-join.md). Independent reviews cover the [source structure](review-source-structure.md), [execution model](review-source-machine.md), and [offset/storage/resource bound](review-offset-simulator.md).

The prior actual physical-Hermite retained-report subpower theorem remains proved. The remaining full-cost work is to compile the other actual source blocks, acquire their physical inputs, handle comparison/branch/finite-loop control, bound auxiliary state and bind public construction/schedule/floor/decoding. Then the existing public resource-rate theorem can be applied to the complete simulation. No practical speedup, new long-query exponent, commit or push is claimed.
