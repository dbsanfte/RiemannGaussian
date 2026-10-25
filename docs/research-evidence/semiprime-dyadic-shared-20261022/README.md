# Sparse dyadic norm acquisition and the remaining shared row computation

2026-10-22. Active goal: achieve and prove deterministic semiprime
factorization in soft O(N^(1/6)) bit operations. This packet proves a
new acquisition primitive and records attempts to apply it to the full
collision query. The full query and sixth-rate factorizer remain unproved.
This is mathematical algorithm research with independent review and a
correctness reference; it is not a new Lean theorem or a runtime certificate.

## Acquired result

Let m be a power of two. The paid preparation supplies a unit eta whose
order modulo each hidden prime exceeds 16m^2. For any native-size integer
shift s and ONE supplied polynomial U of degree L <= 2m, consider

    F(X,z) = (X+gamma)^2 - z*t^2*X^s*(1+gamma*X)^2,
    Norm_(X^m=Y)(F + epsilon*U) = Q_m + epsilon*V_m,
    epsilon^2 = 0.

There is a deterministic algorithm acquiring BOTH Q_m and V_m modulo z^h
in soft O(h+L) bit work for 1 <= h <= m. Full output costs soft O(m+L).
The suppressed factors include log N, log m and the bit length of s.
The algorithm handles negative shifts and composite coefficient rings.
It does not construct a rank-m multiplication matrix.

The mechanism is an exact support bound. At norm rank p, coefficient z^j
has spatial exponents in an interval of width two around sj/p. Thus the
denominator has at most three possible monomials per z coefficient. One
U insertion widens the interval by only O(L/p). An integer shear removes
the large shift before geometric evaluation. All encoded exponent
differences stay below 10m^2, so the prepared eta makes interpolation
denominators units in Z/N.

With q=min(p,h-1), the complete product of the truncated inputs has
O((q+1)(1+L/p)) candidate monomials. Recover that COMPLETE product through
z-degree 2q, then discard degrees >=h. Summing over dyadic p gives

    O(h*(1+log(m/h)) + L*(1+log h))

support operations before the usual logarithmic arithmetic factors.
The case h=1 costs O(log m+L). Interpolating only the retained product
support would corrupt low coefficients; the implementation includes an
independent countercontrol for that error.

The ratio V_m/Q_m is the relative trace of U/F. After Y=1, a supplied
weight B is obtained by U=B*g for F=g-z*f. Thus the constructor supplies
fixed-weight power traces, including arbitrary monomial shifts of the
rational base. The same proof applies to any supplied f,g of degree at
most two in F=g-z*X^s*f; the reference program implements the displayed
squared-base specialization. Trace division additionally requires g to
be a unit in the cyclic algebra, which the native prepared base satisfies.

Proof and reviews:

- [Norm and tangent construction](reports/sheared-norm-constructor.md).
- [Independent denominator review](reviews/sparse-norm-constructor-review.md).
- [Independent tangent and transposition review](reviews/tangent-transposition-review.md).
- [Low-precision proof](reviews/sheared-norm-low-precision-review.md).
- [Root integration and bit-cost review](reviews/root-integration-review.md).

This result is uniform over the stated inputs. It is not a finite
semiprime coverage experiment. It also does not yet acquire the different
weights needed by all native rows.

## Exact remaining sharing problem

The aligned native power piece is

    H_a = CT[rho_(u*a)(B) R^a],
    B = W^N,  R = W/X,  u = N^(-1) mod m.

The new constructor pays the sequence for one fixed weight and one
shift. Here the weight changes with a. Equivalently, if B_k are the
acquired coefficients of B and Q_k=Norm(1-z*R*X^(u*k)), the needed series is

    sum_(a>=1) H_a*z^a/a = -(1/m)*sum_k B_k*log Q_k(z).

Each summand is computable by the new primitive. A shared algorithm for
their weighted sum within the total soft-m budget has not been proved.
Linearity in a tangent direction does not turn different shifted norm
bases into one fixed base.

The first coefficient-index fold is fully contracted, with two explicit
rational kernels and a halved coefficient list. Later folds carry affine
output tags and changing phase weights. The tempting bound
p*min(p,m/p)*(1+m/p^2)=O(m) is correct if each branch really has the
required supplied scalar direction. Packing phase coefficients into one
vector does not prove this: their contraction with R^sigma is precisely
the unresolved operation. At the terminal phase rank it recovers the
original H_a problem.

- [Exact additive fold](reports/additive-contraction.md) and
  [independent review](reviews/fold-review.md).
- [Weighted logarithms and affine updates](reports/weighted-log-directions.md).
- [Phase-direction cost ledger](reports/phase-direction-ledger.md).
- [Resampled coefficient recurrence](reports/resampled-displacement.md).

Even acquiring H_a would require a further proved integration of the
native ell_j powers, the long seed interval and same-leaf recovery. No
trace equality is being used as a substitute for an original collision.

## Direct scalar route and full-goal audit

The existing
[unconditional preparation and bounded-leaf controller](../semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md)
already pays the public base, exceptional order branches, all target
acquisition, and decoding. It leaves this sufficient query: for any
supplied row subset A and common covered seed interval [a,a+ell), acquire

    product_(delta in A) product_(a<=i<a+ell)
        (beta^(N+delta) - beta^(m^2*i)) mod N,

or a proper factor, in soft O(m) bits. Binary restriction then localizes
a saturated product in O(log m) calls. A bounded global leaf gives the
exact factor sum. This bounded route requires no additional QRH premise.
The existing general query bound remains soft O(m^(3/2)).

The [full-controller audit](reports/full-controller-audit.md) distinguishes
that mathematical composition from the current noncomputable Lean
interfaces and incomplete implementation. A successful new query would
still need an integrated bit ledger and executable/formal controller.

The direct scalar investigations retain all original differences:

- [Geometric block-resultant application](reports/sheared-norm-scalar-application.md)
  pays its short block and coefficient prefix, but leaves its long product.
- [Geometric Newton coordinates](reports/q-newton-contraction.md) make
  q-dilation bidiagonal with a paid one-column quotient defect; the
  determinant contraction is unacquired.
- [Native half-tag transport](reports/native-dyadic-transport.md) proves
  bounded odd shifts into four seed phases; their startup queries remain.
- [Finite stationary compensation](reports/stationary-phase-contraction.md)
  keeps the original collision polynomial as a surviving power.
- [Source-retaining reciprocal defect](reports/source-retaining-functional.md)
  preserves whole-local equality, but its joint acquisition is unpaid.

These exact operations identify possible sharing rules. None is a general
impossibility theorem or an improved factoring exponent.

## Reference implementation and preservation

Run the standalone [reference implementation](implementation/README.md):

    cd docs/research-evidence/semiprime-dyadic-shared-20261022/implementation
    python3 -m unittest -v test_sheared_norm.py

It uses actual product-tree moments, inverse-transposed-Vandermonde
recovery, shears and tangent propagation. Its polynomial kernels are
schoolbook, so this Python reference does not have the proved fast-kernel
bit complexity. Five test groups check against independent determinant,
coefficient and trace oracles, including negative shifts, degree-2m U,
precision one, truncation aliasing, and proper/saturated node failures.
[Independent code review](implementation/independent-code-review.md)
and [implementation bit audit](implementation/precision-and-bit-audit.md)
record that distinction.

Twenty investigator artifacts were copied verbatim; root authored this
integration and its review. The [validation record](validation.json),
[provenance](archive-provenance.json) and [source pins](source-pins.json)
record the checks. All 143 entries in the preceding seven frozen packets
are preserved. The new manifest excludes itself. No external papers are
copied, and no full build, new Lean backend, commit or push is part of
this research pass.
