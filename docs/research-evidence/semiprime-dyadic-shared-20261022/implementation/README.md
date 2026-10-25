# Sheared norm and tangent reference

Run from this directory:

    python3 -m unittest -v test_sheared_norm.py

No external Python packages are required. `sheared_norm.py` implements the actual dyadic algorithm, not a determinant-based substitute:

- integral Laurent shear at each stage;
- actual conjugation sign using the REMOVED shear;
- known candidate sparse support before the even-power filter;
- geometric moments through product-tree rational summation;
- pointwise multiplication and inverse-transposed-Vandermonde recovery;
- derivative-unit node guards, with explicit proper/saturated distinction;
- dual-number tangent cross-products and restoration of exact Laurent exponents.

The public entry point is

    norm_tangent(m, s, gamma, t, u, modulus, eta, precision=None)

It returns `(norm, tangent, ledger)`. `m` must be a power of two, the modulus odd, and `u` is the coefficient list of the supplied polynomial U, of degree at most 2m. Returned dictionaries map `(z_degree, Y_exponent)` to residues and represent

    Norm_(X^m=Y)((X+gamma)^2 - z*t^2*X^s*(1+gamma*X)^2 + eps*U)
       = norm + eps*tangent,  eps^2=0.

`precision=h` optionally returns only coefficients z^j with j<h; h must be a positive integer. The default retains the full norm and tangent. At each rank-p stage it retains q=min(p,h−1), reconstructs the COMPLETE product through j=2q using Kronecker radix 2q+1, then filters spatial parity and discards j>=h. Discarding high product terms BEFORE moment interpolation would alias them into low coefficients.

Negative Y exponents are exact integer metadata. They can be evaluated only at a unit Y. The tangent is an UNNORMALIZED norm derivative. Its ratio to the norm is the relative trace U/F. `trace_prefix` specializes Y=1 and expands that ratio. A user requesting the trace of B/(1-z*f/g) supplies U=B*g; it must not supply B alone.

The interpolation unit eta must have separated powers on the actual exponent span; the prepared local-order bound >16m² suffices, including the tangent degree bound. The code does not factor the modulus to verify orders. It checks interpolation derivative denominators and raises `NonunitError` if separation fails. The exception's `divisor` is a proper factor when strictly between 1 and the modulus; equality to the modulus is a saturated collision and is NOT reported as a proper factor. A bad-input saturated fallback checks individual node differences to find a proper factor if available.

`eta` need not equal `gamma`. The constructor treats gamma and t as coefficients and does not enforce t²=gamma: the polynomial norm identity remains valid without that relation. The source application supplies it separately.

## Complexity scope

The reference really uses product trees, rational generating functions, Newton series inversion and remainder-tree multipoint evaluation. It does NOT solve a dense Vandermonde system and does not form a full-rank cyclic multiplication matrix during acquisition.

Its elementary polynomial multiplication and monic remainder kernels are SCHOOLBOOK. Therefore the present Python program is generally quadratic (up to logarithms) in the coefficient lengths. It is a correctness reference, not a bit-time certificate. Substituting fast univariate multiplication/remainder kernels yields the theoretical near-linear product-tree operations proved in the companion report. The precision version has soft O(h+L) arithmetic cost for supplied U degree L, including h=1: each stage has O((q+1)(1+L/p)) support slots, and these sum to soft O(h+L). The full-version bound is soft O(m+L). Bit complexity also includes coefficient bits log N and exponent metadata log(2+abs(s)); arbitrary huge integer shifts are not unit-cost metadata. The logarithmic number of rank stages is suppressed. In particular, no algorithmic change to the sparse/shear/dual-number logic is needed. Validation/invalid-node fallback costs are separate from the promised separated-node run. Memory and timing of this Python program are not claims about native factorization complexity.

The ledger records each stage's shear, residual slope, support size, and maximum Kronecker exponent. Tests verify that the span stays below 16m². The theorem proves the tighter universal bounds, including negative shifts.

## Independent controls

Five test groups cover:

- geometric moments against direct scalar sums, inverse moment recovery, and sparse product against independent convolution;
- norms AND tangents against an independent Leibniz determinant of multiplication by F+eps U in (Z/N)[X]/(X^m-Y), at multiple scalar z,Y values;
- negative and large shifts, both shear parities, startup m=1, and U of degree exactly 2m;
- trace prefixes against an independent multiplication-matrix inverse/power oracle;
- prefix coefficients against an independent symbolic-in-z Leibniz determinant, including h=1 and a countercontrol showing that premature high-z truncation corrupts LOW interpolated coefficients;
- a deliberately proper node-collision gcd, a saturated collision, zero tangent and invalid contracts.

The composite test modulus is 1009*1013. Its known factors are used ONLY by the independent test setup to supply primitive interpolation nodes; the constructor receives neither factor. These are exact algebra/control checks, not empirical native coverage or running-time evidence.

No long collision query, native row acquisition, or factoring engine is implemented. The direction U is fixed and explicitly supplied.
