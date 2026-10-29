# Independent review: core-query.md

26 October 2026. Read-only algebraic review; no experiments, repository edits, or new research. **PASS:** the exact transform, bulk/boundary partition, and full moment-rank argument are correct under the stated native guards. No substantive correction identified.

## Factorial coefficient transform

The coefficient of epsilon^r in C=(c epsilon;q)_M is

    C_r=(-1)^r c^r q^(r(r-1)/2) [M choose r]_q.

Taking C_(r-l)/C_r and writing x=q^r yields exactly the report's Eq. (2): the exponent is l(l+1)/2, including its sign and c^-l factor. For l>r, the numerator contains 1-q^0 while the displayed denominator remains invertible, so the zero convention is valid without a hidden negative-index coefficient.

For 0<=r<=M and 1<=h<=J, the denominator difference q^r-q^(M+h) has exponent gap M+h-r in [1,m]. Thus it is a certified unit. Each C_r is also a unit because its Gaussian-binomial factors use only nonzero short q-differences. The broader guard through 2m suffices for every factor used. No F-value inverse occurs.

The independent ratio is

    w_r/C_r=q^(-Jr) prod_(h=1)^J
                       (1-q^(M+h))/(1-q^(M+h-r))
             =K_J/D_J(q^r).

This verifies the normalization and all q powers of H_T. Combining it with the coefficient identity gives H_T(q^r)=K_J F(z1*q^r). Under m>2J, M>J, so J+1 unit-separated bulk nodes are available. Their Vandermonde determinant is a unit over R, proving the polynomial identity H_T(X)=K_J F(z1 X) over the composite ring. This is stronger than a generic-field calculation and justifies the exact native conclusion.

The stated balanced acquisition of H_T is legitimate: its summands have one nested product of factors 1-X*q^(-r) and one complementary nested product of factors X-q^(M+h), with scalar weights acquired in soft J. The same interval split used for the epsilon core applies. K_J consists of J short unit factors and costs soft J.

## Boundaries and native labels

Requested coefficient indices are 0,...,m-1. The bulk is 0,...,M and the residual indices are M+1,...,m-1, exactly J-1 positions (empty when J=1). The moment support's additional index m is the unrequested endpoint. The report consistently removes it rather than assigning it the original decoder. The residual evaluations cost soft J by monic multipoint evaluation, and a bulk of m-J+1 remains Theta(m) in the long regime.

For the stored orientation v_j=beta^(E_j-H/2), z1=eta³=beta^(3H/2), hence v_j/z1=beta^(E_j-2H), as stated. This does not license a new interval: the report correctly returns through actual opposite-row metadata and the original physical index. The J=1 gcd diagnostic has the printed coefficient/sign, and is correctly labeled an algebraic diagnostic rather than an attained native reciprocal example.

## Moment rank and large determinant

Over either local field, the m+1 clock nodes are distinct and all w_r nonzero. A monic degree-J F removes at most J nodes; the surviving support R is at least m+1-J>J+1 when m>2J. The full moment Hankel rank is exactly R: its leading R-square minor on the surviving support factors as V diag(weights) V^T, with V square invertible. This does not imply every smaller leading minor is nonzero, a qualification the report explicitly includes.

After subtracting the endpoint contribution, the full m-square Hankel determinant has one full-support Cauchy–Binet term. Its Vandermonde-square and all weights are units, giving exactly the original product's local-zero/nonunit predicate. The report does not count the long moment list or determinant readout as acquired from the short descriptor.

The conclusion is appropriately narrow: the coefficient-functional transform recovers the original F, and the entire moment sequence does not collapse to J states at a collision. This is not a lower bound against nonlinear native/conic algorithms or a restriction on prefix-oracle localization. The complete cost remains soft(J+sqrt(Jm)).
