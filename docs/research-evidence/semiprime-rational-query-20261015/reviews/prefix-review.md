# Independent review of the q-Newton prefix algorithm

2026-10-15. Root mathematical review. PASS.

Reviewed report SHA256:
`6ed478a66c92b7f27065c490a7bee1cfc7f771a0f41ee80ef4fc570336f883ec`.
Report: `implicit/q-newton-prefix-initialization.md`.

For Q_n=(q;q)_n and chirp chi_k=(-1)^k q^(k(k-1)/2), the coefficient
identity P_n(z)=sum_(k<=n) chi_k Q_n z^k/(Q_k Q_(n-k)) gives
F_n/Q_n=(A*B)_n with A_k=chi_k s_k/Q_k, B_k=1/Q_k. This is an exact
formal-weight identity, not a finite-ring pointwise inference.

Generating J moments by a rational tree uses denominators of constant
term one. The weight-dependent numerators multiply only parameter
denominators, preserving a soft-linear straight-line representation
without expanding the formal weights. A single truncated convolution
then acquires all first J values. Acquiring chirps, q powers, Q_n and
their reciprocals takes O(J) arithmetic and one certified parameter-unit
inverse. The backward recurrence for Q_(n-1)^(-1) is correct. The local
order promise licenses every factor 1-q^r; arbitrary q is not granted it.

The reverse prefix transform correctly divides by B(t), whose constant
term is one, then rescales by known units. Fast polynomial arithmetic
can be implemented by exact modular/integer polynomial methods; no
analytic accuracy or inverse node differences is implicit in this step.

At a later start n the required moment weights include P_n(z_j), so the
report correctly declines to initialize that distant state for free.
After deduplicating identical integer offsets, target differences are
units on the stated actual supply because their nonzero exponent
differences have magnitude <=4m^2 below both local orders. This licenses
the separately charged full-state interpolation observation; it is not
an algorithm for the unpaid state jump.

The matrix-q-factorial paragraph keeps recurrence order and coefficient
degree in its cost. Nothing in the prefix algorithm improves the general
long-query bound or supplies all-semiprime routing outside the promise.

No correction required. Source-pin byte verification is recorded by the
final evidence manifest; this mathematical review makes no new Lean,
benchmark, or full native-source-closure claim.
