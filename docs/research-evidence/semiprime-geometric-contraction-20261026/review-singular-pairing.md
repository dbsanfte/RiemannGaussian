# Independent review: finite singular pairing

Disposition: PASS for equations (1)–(9), acquired modes/normalizations, composite-ring scope and retained acquisition boundary. No numeric diagnostic was needed. The known affine pencil's modes are endpoint modes, not supplied physical hit vectors.

The row-scaled column polynomial in §1 has the correct two affine parameters u+v and u q^h+v, hence the two-Newton determinant and sign normalization are correct. On v=1-u, all s>=1 factors contain 1-1, leaving (2). q^h-1 is a screened unit, and the u_k separations use only short unit gaps. For f_k, the ratio q^k(X-b)/(X-bq^k) gives eigenvalue1 after multiplying by (q^-k X-b)/(X-b); cleared equality also covers a vanishing displayed factor. Its degree k<J ensures a nonzero evaluation vector. More precisely these form a generalized pencil eigenbasis: A-M is invertible because R_i-1=(q^h-1)T_i/(T_i-b), a unit. Thus the monic Newton polynomials indeed provide the claimed paid basis/inverse conversion without a dense matrix.

At k=0, M fixes constants and evaluation at0 is its left1-eigenfunctional. The projector 1*l^T and l_j=-D(0)/(T_jD'(T_j)) have correct sign and normalization sum l_j=1. Each l_j is unit after the actual row-separation gate. The clock projector k_i=-W(0)/(x_iW'(x_i)) is similarly correct; individual requested factorial weights cost soft sqrt(h), while the full h-vector is NOT claimed acquired. W(0) and W'(0)/W(0) are cheap exact endpoints; logarithmic derivatives need not themselves be units.

Both partial fractions (6) check by residues and the value at infinity. Their evaluation at0 gives sum l_j/T_j=-D'(0)/D(0) and sum k_i/x_i=-W'(0)/W(0). These yield BOTH signs in (7):

B=W'(0)/W(0)+D(0) sum_i k_i/[x_i D(x_i)]
 =-D'(0)/D(0)-W(0) sum_j l_j/[T_j W(T_j)].

They hold with multiplicities in the clock/row rational function only after the stated actual separation gates (which make the displayed simple weights lawful); no ungated D' inverse is assumed. D+delta regularization on the first side requires the deformed interpolation functional too. Its remaining sum has residue k_I/x_I at the good simple delta pole, as stated; the whole B also has its displayed D(0) factor. This is not confused with a physical leaf jet or with a globally meaningful inverse at the collision.

The supplied-c identity (8) is exact. Substituting unknown c=theta does not acquire that theta, and no illegal 0/0 cancellation at x=c is performed. Affine transport (9) is the actual full W ratio; at c=0 it has GP endpoint cancellation, while a nonzero center does not inherit that formula. The report does not assert a lower bound for another way to evaluate that ratio. All known endpoint and q-shift gates retain original-K unit/extractor accounting. The completed retuned query is an upper bound soft K^(4/3), with original K^(5/4) fallback, not a new selector.

## Attempted use of the acquired coefficient end strips

I also inspected selected-condensation.md's actual residual rather than assuming an arbitrary lack of information. Its prefix-weighted mixed rational functional has numerator/denominator degrees O(J), and its polynomial moments through M can be acquired in soft(b+c+M): evaluate the acquired prefix-weight arrays' polynomials at q^k and Q^k (monic MPE/chirp-Z), then multiply the two axis moment values. A Taylor strip of the rational source at0 is likewise computed in soft(J+M), all unit-constant denominators being retained. These polynomial terms are regular in the physical delta and have ZERO selected residue.

An exact alternative to explicitly emitting that Taylor polynomial is useful for source normalization. For any proper p(t)/H_delta(t) with H_delta(0) a unit, set

E_M(t)=t^-M p(t) mod H_delta(t), degree E_M<degree H_delta.

The inverse power is acquired by monic modular arithmetic in soft(degree H_delta * log M), including any FIXED delta jet. Then

p/H_delta = P_(M-1)(t)+t^M E_M/H_delta,
P_(M-1)=(p-t^M E_M)/H_delta, degree P_(M-1)<M.

Thus the selected residue is exactly preserved by the shifted rational remainder; no discarded polynomial part contributes. For the four-shift residual, fixed delta precision four suffices componentwise for its possible pole orders <=4. This applies to both source numerators, preserving their ratio. It does not acquire the residual functional: the denominator H_delta and its unit-node poles remain, with a reweighted t^M numerator. At a unique pole E_M evaluates to p/t^M, so its multiplication by t^M restores the full original nonzero amplitude. This is an executed regular-part cancellation, not evidence that the residual is zero.

The acquired first/last sqrt(h) strips of R_b can supply analogous polynomial/end contributions, but no identity here expresses the remaining unit-point Cauchy sum purely as those strips. The exact missing term is the shifted-grid quotient correction in qdifference-contraction.md (4), or the rational residual just displayed. No arbitrary information-insufficiency or computational lower bound is inferred. A new pairing exploiting this inverse-power gauge or the original two-GP structure could still contract it.
