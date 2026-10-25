# Independent joint-Hadamard recurrence review

23 October 2026. **PASS on the corrected final source.** Reviewed
`joint-hadamard-recurrence.md`, SHA256
`9e93a8b82e4728a37a01b14a55357d7d496cc85dcfe493a9d8ed3f98e2966ba3`.
The inherited padded-source pin is the reviewed `recurrence-design.md`
`ccf5ea70118db47e8e6f01a3360a6d0161e41f34c6065e1537b931cdd6f9b718`.
No source/tracked edits, numerical tests or extra literature were used
by this audit.

The sole wording precision requested was incorporated: the concluding
soft-B action claim now concerns acquired ORDINARY matrix operators.
Hadamard masks retain only their stated supplied-rank-k Cauchy-action
guarantee; their application to the unknown product is still unpaid.

The identities and unit/cost scope check as follows:

1. Entrywise, A_B=A_1*T^-1 because the quotient of the two entry
   multipliers is Sigma_B. T is invertible since every dyadic plus
   factor is a unit in the odd-order subgroups. No inverse of A_1 or
   A_B is taken, including on native q-adjacencies. The ordinary
   product Leibniz formula has the stated sign. Substituting it before
   and after T gives equation(3), with q^(-B) and q^(1-B) exactly as
   displayed. The lower-power corrections really telescope, but the
   aggregate T([S,Y]Q) remains an unacquired operation.

2. For a supplied rank-k input, the reciprocal-Sigma kernel reduces
   to two Cauchy sums per generator away from overlaps. In a hidden
   field, q^B*y_j=y_i iff q*z_j=z_i, since B is dyadic and the local
   groups have odd order. The latter equality is publicly determined
   by the bounded literal offsets, and all remaining denominators
   are units. At an overlap Sigma_B=B*z_i^(B-1), so excluding its
   Cauchy pole and inserting this explicit regular value is legal.
   Fast regular-part MPE and unit derivatives give the claimed soft(kB)
   action; no representation of [S,Y]Q by small k is presumed.

3. Commuting the FULL Stein equation with the heterogeneous pair Z,qZ
   yields equation(5) exactly. Its diagonal multiplier (1-q)z_i is a
   proved unit. Lagrange interpolation gives Eleft in(6): the apparent
   ratio of power differences cancels into reciprocal Sigma_B, which
   remains a unit even at an actual q-adjacency. Thus the forcing
   operator is real acquired data, but not a short generator for the
   unknown heterogeneous displacement.

4. Multiplying the reciprocal kernels in opposite orientation cancels
   Sigma_B and gives alpha_i*beta_j as in(7), including zero numerator
   rows without division by them. For a MIDDLE S, the full two-index
   sum is exactly(8), with b_j=1/h_y'(y_j), c_j=1/h_z'(z_j) and the
   ratio r_i(z_k)/r_i(z_j). It cannot be replaced by the diagonal-middle
   rank-one contraction. The divided-difference split has the positive
   (v-u) factor and leaves precisely a contraction with [S,Z].

5. Under trace pairing, the adjoint is D1*X-QD0*X*K, with the stated
   noncommuting factor order. This proves residual identity(9).
   X_w actions and tr(X_w U) are paid because U has rank two, but
   tr(S R_w) is not thereby computed. Reverse differentiation of the
   first term gives diag(Eleft U E_B), as stated, rather than diag S.

6. All padding, odd-order/unit, derivative and bounded global-leaf
   guarantees are inherited from the exact reviewed square overquery.
   No new seed enlargement or recovery premise is inserted here.
   Fast operator actions are distinguished from acquired columns or
   Hadamard-product contraction. The explicitly quadratic completion
   is only an implementation upper bound; no universal complexity
   lower bound, negative all-input theorem or improved query exponent
   is claimed.

The finite joint identity is a valid algebraic simplification. The
report accurately leaves its actual scalar/diagonal acquisition open.
