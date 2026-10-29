# Actual local interpreter height attachment

Two new modules only; all frozen interpreter files unchanged. LocalExecutionHeight strict/root15/all-generated PASS (63 declarations, 44 theorems). LocalExecutionBitBounds strict/root15/all-generated PASS (30 declarations/theorems). All generated constants use only propext, Classical.choice and Quot.sound. No executable runtime polynomial index was introduced: new runtime-facing inputs remain rational coefficient arrays; polynomial witnesses occur only in theorem premises.

## Exact state coverage

* builtLayout_source_bound obtains the native constructor's actual integer-cleared row and its bound, then bounds literal source-array coefficients from their coefficient equality. It does not assume requested Taylor heights.
* shiftFrom_bound applies to every recursive suffix start/len. The common source denominator d is unchanged at an integer node. horner_constant_bound covers the scaled coefficient array; shiftFrom_product_bound covers its multiplication buffer, shiftFrom_product_term every scalar product, and shiftFrom_product_prefix every dotPrefix accumulator before final addition. Every earlier output cell of the multiply loop is covered by the same coefficient bounds with its shorter width. Every addJet/scaleJet cell is written independently, with no additional scalar accumulation.
* maskShift_bound preserves bounds; acquireCorrected_bound applies to every n, hence every sum prefix, and acquireCorrectedFin_bound covers its finite wrapper.
* LocalTrace is a proof tree following the ACTUAL false and true truth-callback restrictions and tail ports. Each LocalStepSafe records neg/no arrays, both products, all scalar product terms, all convolution accumulators and actual node output. nativeLocal_trace uses the actual Array.ofFn-cached input reports, not a memoization assumption. Integer table leaves have absolute value at most one.

## Quantitative bounds

Write H(l)=B*(1+J*(T+1))^l when original source numerators are bounded B and integer |t|<=T. Horner buffers have denominator d and bound H(l); products/accumulators have explicit p*H(l)*(T+1), and corrected-input prefix n has numerator n*H(R+1), same d. A w-port subtree uses denominator d^w and numerator [2J(d+Bport)]^w, with branch products using d^(w+1). No normalization or cancellation is used to bound an intermediate.

If d,B,J,T,n<=2^b, H(l)<=2^[b+(2b+2)l]. Explicit normalized RationalBits.Fits theorems give Horner width 2b+(2b+2)l+1, corrected-prefix width 3b+(2b+2)(R+1)+1. When port bounds d,Bport,J<=2^c, all local output widths are (3c+2)w+1 and multiplication/prefix/term widths (3c+2)(w+1)+1. The completed nativeLocal call from SOURCE arrays fits width [3(2b+(2b+2)(R+1))+2]w+1. These are polynomial in input bit budget, row degree and local arity. representation_fits converts proved representations, not an assumed output fit, to the existing primitive rational backend interface.

## Scope

This supplies the missing executed local prefix height premise. It does not implement a new bit-backed traversal or prove a whole-machine theorem. Primitive operation execution, source coefficient acquisition work, array/control encoding and global controller composition remain separate attachments. Source array equality to native polynomial coefficients is a semantic input supplied by the source frontend; the height conclusion is constructor-derived.
