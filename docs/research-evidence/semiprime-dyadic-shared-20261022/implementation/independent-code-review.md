# Independent implementation review — PASS within the stated fixed-direction scope

Reviewed stable sheared_norm.py, test_sheared_norm.py and README.md, and independently read sheared-norm-low-precision-review.md. Replayed once with `python3 -m unittest -v test_sheared_norm.py`: all five groups passed. These controls verify algebra and guards, not native coverage or runtime asymptotics.

## Composite-ring arithmetic and actual acquisition

The constructor uses rational product-tree moment summation, pointwise scalar multiplication and explicit inverse-transposed-Vandermonde recovery. It does not call the determinant or cyclic matrix oracle during acquisition. Monic remainders avoid field-only leading-coefficient division. Series inversion checks its constant coefficient. Interpolation checks inverse nodes and derivative denominators; a proper nonunit is distinguished from gcd=N saturation. In the saturated bad-node case, pairwise fallback can recover an available proper collision factor. This fallback is outside the promised separated-node complexity, as documented.

Every successful derivative-unit guard certifies the required node-difference units. The theoretical prepared-order promise supplies this guarantee uniformly; code does not pretend to verify hidden local orders. Gamma and t are allowed as arbitrary coefficients for the norm identity, while the native application must separately supply its preparation promises. `eta` is separately guarded as a unit. Negative Laurent exponents remain metadata until evaluation at a unit.

The inverse moment formula, including its `-node` derivative factor, is correct. Empty support now rejects omitted nonempty inputs. General sparse_product still relies on its documented FULL candidate-product support contract; deliberately violating that contract is used only as a negative test, not as valid acquisition.

## Candidate support, shear and optional precision

At each p, the removed floor shear is restored in the conjugation sign and before testing actual exponent parity. Both norm and dual tangent products use the complete width-four-plus-ceil(L/p) candidate strip BEFORE filtering. The code's floor/ceiling bounds safely include all input and pre-filter product monomials, including negative and large shifts.

For precision h, inputs are reduced modulo z^h, q=min(p,h-1), and the full products through z-degree 2q are reconstructed with radix 2q+1. Only AFTER exact recovery and parity validation are j>=h discarded. Thus high product terms cannot alias the retained coefficients. The h=1 case correctly uses radix1, only j=0, and still propagates the tangent direction. Precision larger than the final norm degree is harmless; invalid nonpositive/noninteger values are rejected.

The independent low-precision proof's support O((q+1)(1+L/p)), separation span below16m^2, and summed soft O(h+L) bound check out, including h=1. The implementation ledger uses the actual q and radix, rather than charging a full dense degree. The theoretical fast-kernel version is a constructor for ONE shift and ONE supplied direction.

## Independent controls

The direct moment sum and ordinary sparse convolution are separate checks on the interpolation core. The Leibniz determinant oracle constructs the multiplication matrix independently and uses no pivot inversions; it checks both norm and dual tangent at several unit Y and z values. The optional-prefix oracle independently computes full z-polynomial determinant coefficients, then compares retained coefficients, rather than comparing two instances of the same Graeffe algorithm. Its explicit missing-high-support countercontrol demonstrates low-coefficient corruption under premature support truncation. The trace oracle uses a separate matrix inverse/power computation for its chosen valid test input.

Controls cover startup m=1, negative and large shifts, both shear parities, U degree exactly2m, zero direction, h=1/intermediate/full precision, invalid contracts, and proper/saturated interpolation collisions. Test factors are confined to test-node preparation; the constructor receives neither hidden factor. No extra benchmark or success campaign was run.

## Cost and remaining scope

README accurately states that schoolbook multiplication/remainder make this Python reference generally quadratic up to logarithms; it is not a near-linear timing certificate. The proved near-linear bound uses fast univariate kernels in the same acquisition architecture. No full collision query, all-moving-direction contraction, native factor controller or 1/6 total factorization theorem is implemented. There is no blocker within the documented reference scope.

## Reviewed hashes

- sheared_norm.py: `2118c7c71ac218608025d5b62846b7e4ac44e9e3cca6b91d09f8b766f2e8278f`
- test_sheared_norm.py: `d064b68a80f60bed8436a7c37df68af401998e2a27e59a16dbc2552948343adc`
- README.md: `4270d05e2918890901202fd4edcc581b220a6edc85490504dfd789564ee1d564`
