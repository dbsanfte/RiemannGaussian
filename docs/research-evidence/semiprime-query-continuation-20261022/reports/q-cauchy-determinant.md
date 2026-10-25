# q-Cauchy determinant attempt on the original scalar factors

This is a focused determinant check, not a new fast-operator claim. No soft O(J+sqrt L) acquisition was obtained.

Keep x_j=beta^(N+delta_j), z_i=q^i, and V=product_(j,i)(x_j−z_i). The actual native exponent/carry data are untouched. Within each set, differences are units: after integer-offset deduplication, target offsets have span below the prepared local-order bound, and 0<|i−i'|<L<ord_P(q),ord_Q(q). Cross differences are precisely the unknown source and may not be inverted as if they were units.

## Exact square-block determinant and the clearing issue

For a square block with J targets and J seed points, put P(T)=product_(r<J)(T−z_r). With Delta_x=product_(j<k)(x_k−x_j) and Delta_z similarly,

 det[1/(x_j−z_r)]
   =(−1)^(J(J−1)/2) Delta_x Delta_z / product_j P(x_j). (1)

This is the scalar determinant identity itself, not a statement about fast matvecs. To avoid assuming a source inverse, clear every row using P(x_j) and form

 M_(j,r)=product_(s!=r)(x_j−z_s).

The polynomial identity becomes

 det M=(−1)^(J(J−1)/2) Delta_x Delta_z.                (2)

Thus the denominator-cleared determinant is a UNIT even at a true cross collision. The collision product has canceled exactly. A controller that replaces the original query by det M would fail; it is not a fraction-free detector with equivalent support. This is a concrete algebraic failure of that proposed determinant reduction, not a lower bound on other structured algorithms.

One short block is genuinely paid in soft O(J): acquire P and evaluate it at all acquired x_j by product trees/MPE. This computes the block product and supports the original leaf localization. It is already the known short-block operation. Equation (1) does not reduce the number of long blocks; it puts the unknown block product into the Cauchy determinant denominator.

## The primary shifted-factorial determinant does not silently pay a long row scale

Chu–Wang–Zhang, *Partial Fractions and q-Binomial Determinant Identities*, CUBO12(3),1–12 (2010), Theorem1 pp2–3, gives a generalized Cauchy determinant of shifted-factorial fractions. Its supplied entries have lengths j and j+1 for column j. Specializing the parameter sequences to q powers produces q-binomial determinant identities. Distinct complex nodes and defined fractions are assumed in the paper; after clearing denominators it is a universal polynomial identity and can be used over Z/N with guards.

If the determinant has J columns, these supplied factorial lengths are O(J), not the desired L. Moving all columns to lengths L+j introduces the common row factor (x_j;q)_L (or its reciprocal), because

 (x;q)_(L+j)=(x;q)_L*(x q^L;q)_j.

For the original source use the shifted-factorial argument x=q^A/x_j and multiply by the known unit x_j^L for a seed interval starting at A. The remaining column factors are short and paid, but the common row scale is exactly the original long q-Pochhammer evaluation. It cannot be omitted: its product is where the original zero support resides. The generalized identity therefore provides no paid acquisition of that scale in this specialization. The theorem is not being dismissed; this is its exact input/normalization audit for the proposed use.

Any attempted inverse of a cross factor must return a proper gcd or handle saturation through the original controller. The short intra-set Vandermonde units do not prove those cross inverses exist.

## Low-rank determinant route still requiring an actual contraction

The original resultant can be written as det H_L(C_F), with the q-Newton multiplication/dilation operators from the frozen audit. The Cauchy construction explains why an inexpensive cleared interpolation matrix can have constant determinant while the desired determinant is unacquired: the latter is a row normalization, not an operator-action cost. A structured Schur-complement or displacement algorithm would have to recover these long normalizations or acquire a restriction-stable singularity detector WITHOUT first assuming cross inverses. No such contraction was derived here.

The native delta_j congruences could conceivably impose an additional identity on those row scales. The Cauchy identity holds for the exact native targets, but supplies no such extra arithmetic equation. No independence-of-targets degree argument is used as a negative theorem about the native specialization.

## Result and source pin

This pass verifies the exact determinant quotient, its source-erasing fraction-free cancellation, and the supplied-entry cost of the relevant primary q-Cauchy theorem. It does not supply the requested near-linear long determinant and does not improve the existing soft O(J+sqrt(JL)) query bound. Original rows, seed interval, and bounded same-leaf recovery remain the intended source.

Primary PDF: https://www.scielo.cl/pdf/cubo/v12n3/art01.pdf . SHA2568204818559984291b32e295df466b6d969836c3148dba3318d8ce0d14737bd4d. Only the theorem and its short proof/model were used; no unverified runtime theorem is attributed to it.
