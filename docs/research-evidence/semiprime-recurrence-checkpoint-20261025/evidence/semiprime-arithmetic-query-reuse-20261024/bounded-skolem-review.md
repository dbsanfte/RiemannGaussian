# Root independent review of the bounded Skolem audit

24 October 2026. **PASS**, for exact final `bounded-skolem-audit.md`, SHA256 `b79225a64b0a63f25384e35125d656e327c506979f0f41c465ed2a90f97e7f06`.

I read the source end to end and checked Theorems 3.1 and 3.6, Lemma 3.2 and their proof descriptions in the cached v3 primary text. The claims are fixed-order INTEGER recurrence statements: bounded existence reduces to EqSLP and is in coRP; the function version includes both finitely many exceptional indices and arithmetic progressions. The auxiliary prime and its decimation are polynomially bounded in the input length only for fixed order. The amended report uses the actual inherited order bound greater than 16H and L<4H; it no longer asserts an unprovided greater-than-16L promise.

The integer initialization is valid: multiplication by the known quadratic lift of q has the displayed 2-by-2 matrix; four diagonal blocks produce the degree-three polynomial values; the tensor square realizes the norm with constant dimension 64. Entries, recurrence coefficients and a constant number of starts have O(log N) bits up to fixed constants, so all classes can be initialized in soft k. D<0 and a nonzero lift make the integer multiplication matrix nonsingular. There is no initialization gap in this particular application.

The missing implication is correctly located: the Skolem candidate list covers exact zeros of the chosen integer lift, while the desired event is divisibility by an unknown factor. Changing only the terminal EqSLP call to gcd does not preserve candidate completeness. For the literal tensor realization at the hidden prime, an identity power includes the I2 tensor Q^3 block, hence requires Q^(3M)=I. Roughness and 3|k imply ord(q^3)=ord(q)>L, so that realization requires M>L. This is a scoped cost finding, not a lower bound for other realizations or modular zero algorithms.

This literature audit gives no new long-query speed and is not an ingredient in the positive signed-weight theorem. No source/shared files were changed by this review.
