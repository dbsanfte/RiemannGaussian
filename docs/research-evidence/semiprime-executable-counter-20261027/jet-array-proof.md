# Cached arithmetic and actual shifted-row heights

`SemiprimeJetArray` defines computable rational coefficient arrays. Its inverse
builder makes one recursive call for the preceding stored prefix, reads that
prefix, and appends exactly one newly computed coefficient. It does not execute
the uncached inverse recurrence separately at every index. The array contents
are proved equal to the algebraic recurrence and then to the normalized Hermite
local quotient.

For retained width J, the actual quotient operation has at most
`3J^2+J+1` rational arithmetic operations and `2J^2+J+1` coefficient reads.
The output array has exactly J coefficients. These counters charge arithmetic
and reads, not primitive bit time or allocation. In particular, extracting a
Lean array implementation to a tape machine still requires a refinement and
control-cost argument.

`SemiprimeJetArrayHeight` derives its bounds from input representations, not
assumed inverse/output heights. For normalized a_0=1 and input coefficients
with common positive denominator d and integer numerator bound B, set
`H=J(d+B+1)+1`. Inverse coefficient k has a representation with denominator
`d^k` and integer numerator magnitude at most `H^k`. Reducing a fraction cannot
increase either bound. All partial multiply-add sums in the inverse recurrence
are also bounded. Padding to one common denominator `d^J` gives numerator bound
`H^J` for the whole retained inverse array.

For actual input arrays H and L with respective denominator/numerator bounds
`dH,BH` and `dL,BL`, and L_0=1, every actual quotient output has denominator at
most `dH*dL^J` and numerator magnitude at most
`J*BH*(J*(dL+BL+1)+1)^J`. These bounds have polynomial bit length when the
input bounds and J do. They do not assume rational operations cost one bit
operation. Partial convolution sums, all global counter accumulators, and their
primitive encodings still need the complete execution attachment.

The new `SemiprimeTaylorHeight` supplies an actual row input to this interface.
An integer polynomial of degree at most R with coefficient magnitude at most B,
shifted by an integer t with |t|<=T, has coefficient magnitude at most
`(R+1)*B*(2*(T+1))^R`. The proof uses the exact finite Taylor/binomial formula,
including coefficients beyond the degree. Shifting commutes with the literal
denominator-clearing identity. Applied to `SourceRowHeight`, the theorem gives
every actual built row's shifted coefficients the SAME positive denominator
`2^(R-1)*(Q!)^(Q+1)`, with the constructor-derived bounded integer numerator.
There is no supplied native-row height premise or factor of the universal
alphabet dimension in this numerator bound.

The array module, extended height module and Taylor module all pass strict
compilation, ordinary-root scoped 15-linter checks, and transitive standard-axiom
audits of all generated declarations. Independent semantic reviews and source
hashes are recorded separately. The full runtime claim remains open.
