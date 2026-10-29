# Physical corrected-port execution

Two NEW sources are final and frozen: SemiprimeCorrectedPortBits and SemiprimeCorrectedPortBitsBounds. Canonical strict builds, ordinary root15 lint and every-generated-declaration standard-axiom audits PASS: respectively 71 declarations/53 theorems and 28/23 (99/76 total). Only propext, Classical.choice and Quot.sound occur transitively.

## Executed path

Runtime definitions consume Array RationalWord sources and a RationalWord node. They never decode to Q to perform arithmetic. shiftFrom caches one recursive suffix, calls actual multiplyBits on its affine [node,1] multiplier, physically copies the original source coefficient into the constant slot, then calls actual addBits. Copying a constant is value-equivalent to the old multiply-by-one step and avoids an unnecessary physical arithmetic call. maskShift physically copies a coefficient or zero according to independent constant/positive-degree Boolean flags. acquireCorrected shifts EVERY source row, masks it and physically adds it to the retained prefix. acquireCorrectedFin has no Layout/Polynomial index.

Every invoked arithmetic report survives in the returned JetReport.clock, together with coefficient address/copy and finite recursive/control allowances. JetBits supplies the attached Boolean rational instructions and flat coefficient addressing. The initial source/node word acquisition, caller-specific source-family getter and the execution/encoding of natural clock metadata remain explicitly separate; arbitrary function-valued input generation is not claimed free or already implemented here.

## Exact semantic interface

shiftFrom_correct, shiftRow_correct, maskShift_decode, acquireCorrected_correct and acquireCorrectedFin_correct prove EXACT full decoded-array equality to the corresponding frozen LocalArrayFrontend coefficient arrays. The result also proves Valid output denominators. These compare full arrays, not only a requested endpoint coefficient.

The correctness premises concern ORIGINAL source coefficients with one common Representation(q,d,B), an integer node t, t.natAbs<=T, and numeric source-length/sum envelopes. Every Horner convolution scalar product and partial sum is covered by JetBits' common-denominator proof using the source suffix bound. Every final addition and corrected-column prefix is bounded before execution. No output coefficient, shifted answer, corrected-port answer, intermediate Fits, or coefficient-generation oracle is supplied.

The derived public width is

```
portWidth b R = 3*b + (2*b+2)*(R+1) + 3.
```

Given d>0 and d,B,T,J,n<=2^b, port_numeric_bounds derives d<2^W, HornerBound<2^W and n*HornerBound<2^W. acquireCorrectedFin_at_width discharges all internal numeric-fit premises at that actual template. A caller may use any larger common template by monotonicity. Physical source/node words must separately be acquired, Valid and width bounded for the clock; integer t is proof-side only and absent from the runtime arithmetic.

## Width and complete stage clock

Bounds exports acquireCorrectedFin_bounded, acquireCorrectedFin_size and acquireCorrectedFin_clock. The last has the stable interface

```
acquireCorrectedFin_clock template source tw R J A base correction
  template_positive node_width source_widths source_sizes
```

and bounds the actual returned clock by portBudget(template.length,A,R,J,n). It is an explicit fixed polynomial: n times R+1 Horner steps plus all row masks and corrected-prefix additions, with the actual cubic rational-word operation bounds. Input row size<=A is required; take A=R+1 when acquiring exactly the original coefficient span. Coefficient flat-address reads are included; no unbounded hidden initial word callback is included.

Structural output width/size follows the actual fitting/copying program; correctness simultaneously derives the required fits from ORIGINAL representations. Structural width alone is not used as a claim that arbitrary overflowing input arithmetic is correct.

## Runtime control

CorrectedPortSmoke.lean runs actual physical arithmetic on literal words for 1+2X at node 2. The row output is #[5,2,0], the independent positive-degree-only mask gives #[0,2,0], and the full one-row corrected execution reports clock 122337. This is a deterministic data-path/compiler control, not native coverage or factoring evidence and not an empirical runtime bound.

No frozen source, sealed packet, journal or AGENTS file was changed. The intended next join supplies actually acquired source words and uses this executor in nativeLocal/group, retaining both source acquisition and these physical clocks. A complete original-input primitive-bit/address/tape theorem is not asserted by this stage alone.
