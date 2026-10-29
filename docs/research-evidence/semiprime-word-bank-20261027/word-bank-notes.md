# Original-input physical candidate bank

The six SourceWordBank modules construct the entire candidate coordinate bank and Boolean ID menu from original r,Q only. No word function, encoded bank or requested row is a runtime argument to acquire. The internal generic row helper takes only actually acquired physical colour cells; the original endpoint supplies those cells itself.

## Actual data path and ordering

colours acquires the literal ascending finite colour indices and calls the existing actual Boolean-increment natural encoder for each original colour. Every resulting coordinate is a denominator-one physical RationalWord. rowsWith caches its smaller-dimensional physical tails, acquires the actual head-major Cartesian pair list, and copies every head payload and tail row before constructing the next row. Colour acquisition happens once before the Q-stage row recursion. There is no deferred coordinate-function chain or original Word closure in the returned bank.

The row-coordinate theorem is an exact ordered list equality with SemiprimeFiniteEnumerations.words, not a permutation or set relation. The separate root MenuOrder theorem identifies that canonical list with the actual indexed zero-first/filter-tail menu. SourceWordBankIndexed.ids_indexed composes these exact orderings; tie behavior is therefore preserved. The proof-only decode function is explicit canonical lookup at bitValue(id), defaulting to the zero original word, with no Classical.choose. It is absent from all acquisition and lookup data paths.

IDs are constructed by actual Boolean additions starting at the literal empty magnitude. Each current ID is physically copied; the next increment and complete recursive report are retained. Their decoded values are exactly0..r^Q−1. ids_decode is exact ordered equality with the original canonical word list; decode_injective holds on actual acquired IDs. The literal defaultID=[] is actually present, decodes to the original zero word, and the menu is nonempty for positive r, including Q=0.

readRow scans the actual physical row list using physical nonzero tests and Boolean decrements. Every visited row is fully copied and paid. A genuine out-of-range lookup returns the literal empty row. Valid-ID lookup yields exactly Q original coordinates; every returned word is valid and has width≤r+1. The original acquired_representation theorem supplies coordinate semantics and validity without a generic BankRep advice premise.

## Explicit cost and size

The complete original acquisition theorem bounds the ACTUAL bank.clock by budget r Q (r^Q), requiring only positive r. With A an independent materialized cardinality resource:

```
colourBudget(r) =3(r+1)^2+r(20(r+1)^2+8)+4
rowStage(r,Q,A)=r(4A+3)+1+rA(Q(8(r+1)+9)+8(r+1)+14)+1+4
budget(r,Q,A)=colourBudget(r)+2+Q*rowStage(r,Q,A)+3
              +A(30(2A+1)+30)+1+A+4.
```

budget_mono proves componentwise monotonicity and budget_monomial constructs fixed C,k before all diagonal resources. This is polynomial in the ACTUAL acquired alphabet cardinality A=r^Q; it is not a claim that r^Q is polynomial in its binary description.

All actual acquired ID arrays have length≤2r^Q, including high-zero padding. Every original row has Q physical payloads of width≤r+1. readRow_clock_original bounds valid-ID lookup by

```
(r^Q+1)*(copyBudget(r+1,Q)+15*(2*r^Q+1)+30).
```

It derives the address-width cap from the generated IDs, rather than accepting requested output/Fits/lookup cost. Generic readRows_clock additionally covers arbitrary addresses under their literal physical length cap. All row copies, pair-list construction, collection, ID increments/copies and final list-length work occur in the retained reports.

Native natural recursion/control, finite-colour/index metadata, runtime report aggregation and the full allocator/tape representation remain explicit interfaces. No complete public original-input primitive-machine clock or caller switch is claimed by this isolated bank. The returned rows and IDs themselves are actual physical data, and downstream count/predicate/control modules can consume them without original Word functions.

## Validation

Canonical strict compilation, ordinary-root15 and every-generated transitive standard3 checks PASS143 declarations/99 theorem constants across six modules. Independent isolated objects and exact pins are recorded in word-bank-verification.json. Structural execution controls acquired the2×2 bank in canonical order, actual ascending IDs0..3 and physical row2=[1,0]; the Q=0 case returned one empty row and ID0. These are construction controls, not factorization or timing examples.
