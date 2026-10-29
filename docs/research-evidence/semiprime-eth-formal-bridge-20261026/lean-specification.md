# Specification audit of the available Lean SAT result

26 October 2026. Read-only specification/dependency-interface audit at checkout commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. Source root is `openai-math/lean/` beneath this scratch directory. No duplicate build or source change. **The full closure build is pending; this report does NOT call the result kernel-verified.** The parent's textual closure scan reported2569 modules and no axiom/sorry/native_decide in the solution closure; that is evidence about source, not a replacement for successful elaboration/kernel checking.

**Disposition:** the exported theorem has a genuine fixed-width, finite primitive-bit-machine exact-counting specification, with real input encoding length and all-prefix total visited-tape space. No semantic oracle or supplied algorithm contract appears in that exported signature. It covers the weaker square-root-log SAT endpoint advertised in docs/378, not the paper's standalone TheoremD.1 or our new large-scope macro-tensor reduction.

## 1. Comparator versus solution

`docs/378.md` states fixed k>=2, exact canonical k-CNF counting, time polynomial in encoding length times2^O_k(n(log log n)²/sqrt(log n)), and polynomial total visited space. It explicitly distinguishes the manuscript's sharper AppendixD bounds from that formalized endpoint.

`ComparatorChallenges/SubexponentialSAT.json` names solution module `OAI.Algorithms.SubexponentialSAT.Main` and theorem `...SqrtLogSpace.exact_count_and_sat`. It permits only propext, Quot.sound and Classical.choice, and disables nanoda. The comparator `.lean` contains `sorry` in the expected-statement placeholder. That is NOT the solution proof, and should neither be counted as an admitted solution nor silently imported as its proof.

The actual [Final.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean), lines74 onward, exports the same theorem structure. Its source proof obtains a compiled program from `compiled_exact_count_and_sat`, then returns its guarded primitive machine and the two fixed tapes. `Main.lean` imports the actual final modules, not the comparator challenge. I compared the substantive definitions below against their comparator copies; no weakened replacement of count, input size, primitive step or prefix-space contract was found.

## 2. SAT semantics and exact physical output

[SAT.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SAT.lean) defines assignments as V->Bool, literals by variable and polarity, clauses and CNFs as finite sets, and evaluation by the expected existential-within-clause/universal-over-clauses semantics. At lines238–241 the count is the CARDINALITY of the actual finite set of satisfying assignments. It is not an approximate count, residue, nonempty witness encoding or a redefined complexity measure. Declared unused variables remain in Fin n and are included in the2^n assignment space.

The final machine's count tape is required to equal `Tape.mk₁` of the WHOLE binary count word, and its answer tape to equal the one-bit positivity answer. Its terminal state is the same answer. The theorem also asserts the count word decodes to SAT.count and has length<=n+1. `EncodingBounds.lean` defines zero's word as `[false]`, other words as `Nat.bits`, and proves the decoding and length lemmas. Thus it does not merely leave an unspecified pointer or a stack containing a semantic number. The compiled theorem uses tape256 for the count and tape1216 for the answer, among1220 fixed tapes.

`Factor.lean` separately supplies genuine local Boolean-factor semantics and finite sum/cardinality identities. Its table type only reads its declared scope. However that module explicitly supplies NO runtime theorem for arbitrary factor tables; its semantic generality must not be confused with a fast generic factor evaluator.

## 3. Encoding and input-size reality

[Encoding.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Encoding.lean), lines18,51,200–207, encodes natural fields in unary on a binary alphabet, frames list entries with escapes, encodes each literal as twice its index plus polarity, sorts literal/clauses' numerical lists, and prefixes the declared n. This is not a succinct binary-index format, but it is genuine explicit syntax. It contains no satisfying-assignment truth values or SAT.count lookup.

Source proofs show injectivity, including distinction between different declared variable counts. They bound

    n+F.card+2 <= formulaBitLength F
      <= n+2+(4+(8n+8)k)*F.card

under width<=k. `EncodingBounds.lean` further gives length+1<=(8k+7)(n+F.card+1)². Thus the polynomial length factor does not hide an exponentially long input or an uncharged semantic oracle. Canonicalization and unary coding have polynomial ordinary overhead at fixed k. The final theorem only promises correct execution on these canonical encodings; it need not handle arbitrary malformed bit strings.

## 4. Is the measured step really a finite bit operation?

Yes at the stated interface. [Computation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Computation.lean), lines273–308, defines a finite tape count and finite state count. The control selects ONE tape using its current finite state, reads that tape's head in Option Bool (bit or blank), and either halts, writes one symbol or moves that tape ONE cell. The other tapes are unchanged. The transition is a function on finite state/head domains with finite-valued move/write actions. Tape contents are the only unbounded configuration data.

`Trace step time initial final` counts those actual successful primitive transitions. It is not an assignment of a small cost to an arbitrary mathematical function. Although earlier modules also define macro simulations, the final exported theorem uses this PrimitiveMachine and its primitive locatedStep trace.

`GuardedCompiler.lean` compiles the fixed Boolean program through stack mutations to these moves/writes; push and pop have explicit finite action sequences, and the guarded compiler's fixed overhead is7. Its `noncomputable` finite reindex uses `Fintype.equivFin` to name a FINITE control set. This does not add an oracle: for fixed k it is one finite transition table, chosen before all inputs. The specification does not promise a single uniform meta-algorithm producing these tables for every varying k; that is consistent with its fixed-k quantifier.

## 5. Uniformity, constants and no supplied leaf oracle at the endpoint

The quantifier order is

    forall k>=2, exists machine,countTape,answerTape,C,A,S,d,e,
      forall n,F of width<=k, exists time,final,... .

Machine, tape count, state count and positive constants depend on k ONLY, not on n or F. Runtime is

    C*(actual_input_bits+1)^d
       *2^(A*n*(log log(n+16))²/sqrt(log(n+16))).

The shifted real-log expression is defined independently in `SqrtLog/StatementScale.lean`; noncomputability of real logs here only specifies a numerical bound. It is not a machine instruction. All n, including small exceptional cases, are covered by Final's explicit finite fallback, rather than a hidden sufficiently-large-only promise. Growing k, growing clause degree or arbitrary large-arity tensors are NOT uniformly covered by these constants.

The final endpoint has no hypothesis supplying a sparse counter, replacement design, factor oracle, circuit evaluator or numerical resource certificate. Inspecting the immediate proof chain: Final calls `NativeLargeEntry.run`; that assembles setup, global budgets and `NativeLeafContract.uniform_contract`. The latter discharges its local-execution contract from its own `local_execution` theorem and leaves only explicit numerical bounds/threshold facts, which the outer proof supplies. Internal composition lemmas DO have contracts as hypotheses, as expected, but they are not exported unsatisfied in `exact_count_and_sat`. This is a source-interface check, not an independent audit of all2569 proof modules.

## 6. All-prefix space is actual visited-cell space

[VisitedTape.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/VisitedTape.lean), lines14–63, instruments every tape with absolute head position and minimum/maximum positions. The input span is included initially; blank tapes count their initial cell. Each actual move changes the selected position by±1 and updates its extrema. Writes and halts leave positions unchanged. `locatedStep_erase`/`locatedTrace_erase` show that erasing this passive monitor gives the same primitive execution and step count.

`visitedSpace` sums the lengths of these intervals over ALL tapes. It therefore bounds blank cells traversed and the initial input footprint, not just nonblank symbols left at halt. The final theorem quantifies every prefixSteps<=time and EVERY matching execution prefix, bounding visitedSpace by S*(input_bits+1)^e. The monitor is mathematical instrumentation rather than an uncharged machine subroutine, which is appropriate for a space measure; it does not change the transition semantics.

## 7. What this formal source does and does not cover for factoring

Available source-level endpoint: deterministic exact bounded-width CNF counting and SAT, on one finite primitive machine per fixed width, with the stated weaker rho time scale and all-prefix polynomial space. Pending a successful build, that is a well-specified proof candidate matching the comparator; it is not yet reported here as a completed kernel check.

Not supplied merely by that endpoint:

* The paper's TheoremD.1 for arbitrary implicit Boolean tensor networks and its sharper tensor contraction bound.
* The new generic-polynomial application using Prop3.4/Lemma4.7 with w=O(n^(3/4)), streamed2^w truth-table evaluation and total incidence degree2n.
* The macro-FFT multiplication encoding, its O(L) Boolean-wire count and arithmetic/canonical-word correctness.
* An integer factoring theorem with2^o(log N) primitive time or the original selected-residue acquisition algorithm.

The new older-route review derives a MATHEMATICAL generic-polynomial extension from the lower-level paper lemmas. It cannot be obtained by substituting k=w(n) into this fixed-k endpoint. A formal port must instantiate and compile the general design and streaming evaluator, prove their charged arithmetic/time/space bounds, and connect the actual macro network/count to factor recovery. Some reusable finite-factor or arithmetic modules may help, but this audit does not assert they already complete those bridges.

**Final qualification:** no specification-level loophole found in the available fixed-width SAT statement. Completion of its pending Lean build and the additional generic-network/factoring bridges are separate claims and must be reported separately.
