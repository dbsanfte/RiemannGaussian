# Independent scalar transported-recurrence audit

24 October 2026. Root review. PASS for the scoped identities, executed
algorithms, costs and original recovery in `scalar-closure.md`, SHA256
`6f9ae09d1b514b49beb00d03a921d1eb217a699ff7a92d140445c70e6d1a3755`.
No source edits are required.

The monic modulus transport is essential and correct:
F_(v+a)(q^-a X)=q^(-aJ) F_v(X). It justifies transport of the right
remainder between different quotient presentations. The Pochhammer
product contributes q^(ab), whose norm is q^(abJ). Evaluating at the
actually known scaled roots proves the scalar merge including all zeros;
no fixed-quotient endomorphism or inverse of a terminal scalar is assumed.

The start S_1(v)=(-1)^J q^(-vJ) F(q^v) is actual acquired data. For blocks
shorter than J, the ordinary common polynomial is its remainder; after
that threshold the number of degree-J states is O(L/b). Summing these
levels gives the stated soft(L+J), not soft(J+sqrt L). Keeping only scalar
merges does not initialize their many different starts.

The transposed cut has J floor(L/b) actual points, each q^(-ba)Y_j. For
each original factor the unit factor is -q^(ba), proving both the sign
(-1)^(Jbt) and exponent J*b^2*t*(t-1)/2. Monic multipoint evaluation needs
no distinctness inverses and permits zeros/repetitions. The exact tail
and all point acquisition give soft(J+b+JL/b), hence the existing bound
after optimization. None of the short inputs is charged as a free oracle.

Saturated point values can be descended in the actual P_b factor tree:
the sum of degrees along a path is O(b). A proper gcd factors; a global
leaf retains its actual row and bounded original index. Interval shifts
retain their offsets and row restrictions retain their acquired roots.
The standard native decoder receives only original scalar leaves, not
auxiliary remainder or subresultant pivots.

The bounded-chain statement uses the GLOBAL beta order correctly. With
|r|<=L, |delta_j-delta_h-Hr|<=4H+HL<256H^2, so a global equality forces
the integer exponent to vanish. The retained offsets occupy a width-4H
interval, hence at most five per residue class modulo H. The source
expressly does not extend this to unbounded global q-orbits or one local
field, and does not claim a general complexity lower bound.

The literature claims are limited to the primary sources actually
inspected by the source author; a failed full-PDF fetch is disclosed. No
uninspected output-sensitive resultant theorem is used as a correctness
or complexity premise of either executed algorithm. Their proofs above
are independent of those search results. The report's final classification
of unchanged whole-query exponent is accurate.
