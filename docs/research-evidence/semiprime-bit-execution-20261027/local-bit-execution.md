# Actual physical-word local interpolation

Three new modules execute the local tensor interpolation on Boolean rational words, prove exact refinement to the frozen rational-array evaluator, derive a public polynomial buffer width, and bound the actual recursive primitive clock. No frozen source is edited.

## Runtime input/output

`LocalBits.EntryWord` contains a physical SignedWord and its actual callback clock. Its rational encoding simply attaches the literal denominator-one bits. There is no integer/rational answer encoder or truth-table list in the interpreter. The caller must supply an actual local entry-word routine; the interpreted integer is used only in the logical `table T` refinement.

`localEvaluateBits template J w T inputs : JetReport` takes physical rational-word coefficient arrays. At a leaf it calls the actual integer callback once and executes the bit-jet scaling of a literal one buffer. At a nonleaf it computes/caches the false and true recursive results once, then executes physical negation-by-scaling, one-minus-port addition, the two convolutions and the final addition. All these arithmetic stages invoke JetBits and hence actual RationalBits Boolean arithmetic/GCD/reduction/fitting and physical dot loops. The output contains physical words and the sum of their real primitive clocks, callback clocks and the stated literal-buffer/control charges.

`localEvaluateBits_size` and `localEvaluateBits_bounded` prove physical array shape. The boundedness result alone does NOT imply arithmetic correctness: fitting also bounds a truncated invalid run. The next theorem independently proves sufficient capacities and preservation of every arithmetic value.

## Correctness without desired-output Fits

`LocalBitsCorrectness.local_correct` assumes only:

* legal initial physical denominators;
* a shared positive initial denominator d and coefficient bound B for each retained port coefficient;
* actual integer table values of absolute value at most one;
* a numeric buffer-capacity inequality derived solely from J,d,B,w.

It returns exact low-coefficient equality to the frozen `LocalArrayFrontend.localEvaluate`, legal output words, and the derived output representation with denominator d^w and numerator envelope `localBase(J,d,B)^w`. It does not assume a local answer, a desired-output Fits proposition, or branch-output bounds. The induction applies to the ACTUAL false/true restricted tables and suffix ports; it supplies all intermediate common representations to the physical scale/add/dot correctness lemmas. Convolution products and every partial dot sum fit from those input representations and term counts.

The numeric cap is

`(d+1)^w + (localBase(J,d,B)+1)^w + d+B+2`,

with `localBase=2*J*(d+B)`. It controls negation, one-minus-port, each child denominator, and both multiplication numerators together. `cap_dyadic` and `local_correct_at_public_width` discharge this numeric condition from J,d,B <=2^b at

`bufferWidth(b,w)=(2*b+3)*(w+1)+3`.

This is a polynomial WORD-BIT width. It must not be confused with the original maximum factor scope w; there is no new exponential in bufferWidth. The prior local common-denominator representation theorem and dyadic localBase bound are used on the actual restricted truth branches, rather than incorrectly reusing a full original-table mask as though it were every suffix table.

## Actual clock theorem

`LocalBitsBounds.local_clock` charges every actual leaf callback, both recursive branches and all physical primitive stages. If each callback clock is <=E, its actual signed integer word fits the physical template, initial arrays are physically bounded by that template and have size <=J, then

`clock <= 2^w * (E + (w+1)*nodeBudget(J,Wbits))`.

The nodeBudget is an explicit polynomial composed of the JetBits scaling/addition/convolution budgets, including the primitive rational-word clocks, flat jet address/copy charges and literal buffers. The arithmetic term is polynomial in J and Wbits; it is not a post-hoc cost assigned to an already supplied rational output. No correctness/height premise is used to manufacture the clock; physical shape is bounded independently. Conversely the correctness theorem proves that the sufficient public width avoids losing values.

The clock has the SAME stated scope as JetBits: actual Boolean rational arithmetic plus declared conservative flat-address/cell charges. It does not yet execute/charge the natural-number clock bookkeeping, arbitrary function-encoded outer port access, or the global callback/assignment/control representation. Entry acquisition must really return the reported words, and its clock bound must be established by the actual entry checker. These are separate from the local word arithmetic refinement, not free original-input factoring work.

## Executed diagnostic

`LocalPhysicalSmoke.lean` runs the physical evaluator for the AND table on ports `1/2+X` and `1/3-X`, J=3, using only literal physical numerator/denominator words and a real Boolean callback. The public sufficient template has 30 bits. Actual Lean evaluation returns

```
([1 / 6, -1 / 6, -1], 4543524)
```

The rational interpretation is used solely to print/check the final physical output, not by the arithmetic algorithm. The 4,543,524 value is the executed report clock, not the coarse theorem bound. This diagnostic checks a nontrivial rational multiplication/cancellation and actual executability; it is not a factoring fixture or asymptotic benchmark.

## Remaining acquisition and composition

The initial physical corrected ports and their source-derived common bounds still must be acquired and joined to this call. A physical Horner/corrected-port implementation is a natural next step; the present modules do not claim to have implemented it. The global summary/fibre/support/Hermite physical execution, exact entry-checker hookup, all control/lookup/storage charges and final original-integer factor recovery are also outside this local theorem. The full guaranteed factoring bit-time goal remains open.

Runtime callbacks and arrays contain no Polynomial or Layout indices. The frozen rational evaluator and all interpretations occur only in specifications/proofs. No `sorry`, custom axiom or native_decide is used. Strict/root15/all-generated verification logs and isolated source/object pins are kept in this scratch packet; all three new namespaces pass 15 linters, with90 generated declarations/59 theorem constants using only the standard three axioms.
