# Independent sparse norm acquisition review

Let P(X,z)=(X+gamma)^2-z*t^2*X^s*(1+gamma X)^2, with integer s, allowing Laurent X powers. Define Q_p(Y,z)=Norm_(X^p=Y) P(X,z), p a power of two. This note audits the actual known-support multiplication constructor, rather than merely its sparse description.

## Exact support, including the pre-filter product

Q_p has z-degree at most p. Its coefficient of z^j has Y-exponents e satisfying

 sj/p <= e <= sj/p+2.

Proof: selecting j z-terms in the p conjugate factors contributes X^(sj), while the remaining ordinary polynomial factors have total degree at most 2p. Norm invariance leaves only X-exponents divisible by p. This argument is formal and division-free via the monic resultant; no split field is assumed as computational input. Each j has at most three integer exponent slots, hence O(p) known support.

BEFORE parity extraction, Q_p(Y,z)Q_p(-Y,z) has j in [0,2p] and

 sj/p <= e <= sj/p+4.

It therefore has at most 5(2p+1) support slots. The product is even in Y, and replacing Y^2 by T gives Q_(2p)(T,z) exactly. No sign or auxiliary twist is missing: this is transitivity of norm through Y^2=T. In particular the p=1 startup is the displayed P(Y,z), and the first product is P(Y,z)P(-Y,z).

## Explicit exponent encoding with a safe span

Choose v=floor(s/p), r=s-vp in [0,p), and shear each exponent to ebar=e-vj. On the pre-filter product support, 0<=ebar<=2r+4<=2p+2. Encode

 lambda=j+(2p+1)*ebar.

This is injective on all candidate support slots because 0<=j<=2p. Its span is at most 4p^2+8p+2. For every nonterminal multiplication p<=m/2 and m>=8, this is less than 16m^2. Negative s causes no difficulty: floor shear still gives nonnegative ebar; the original Laurent monomials are units when evaluated.

The second factor must retain the shear sign correctly. If Qbar(Y,z)=Q_p(Y,zY^-v), then the encoding of Q_p(-Y,zY^-v) is Qbar(-Y,(-1)^v z), not always Qbar(-Y,z). This is a necessary implementation convention. It affects values, though not support or the even-Y output property of the UNSHEARED product. After recovering the product, undo the shear BEFORE testing actual Y parity, or equivalently test ebar+vj for evenness.

## Paid multiplication through transposed Vandermonde inversion

For the O(p) candidate encoded output exponents lambda_t, form a_t=gamma^lambda_t. Differences a_t-a_u are units modulo N: gamma is a unit, and their distinct exponent differences have absolute value below 16m^2, strictly below both prepared local orders. Thus a Vandermonde matrix at the a_t is invertible over Z/NZ, with every scalar denominator arising from its node differences a unit.

Evaluate each encoded sparse input at gamma^i for i=0,...,S-1, where S is the number of candidate output slots. These values are the moments sum c_t*a_t^i. Fast transposed monic multipoint evaluation computes them from the O(p) input coefficient/node lists in soft O(p) ring operations. Multiply values pointwise. Recover the output coefficients by the inverse TRANSPOSED Vandermonde at the candidate output nodes. Fast inverse-transpose multipoint routines use product trees and the unit derivatives of their monic node polynomial; they do not require a root of unity modulo N or division by p. Candidate supersets are legitimate: unused slots recover coefficient zero.

Equivalently this is known-support sparse multiplication with deterministic geometric evaluation. All node powers require O(log m) modular multiplications each because the encoded span is O(m^2). Consequently each norm-doubling multiplication and filtering step costs soft O(p) modular operations, hence soft O(p log N) bit work with fast integer arithmetic. Summing doubling p gives soft O(m) bit work, suppressing the standard logarithmic factors. This is a genuine constructor for the fixed sparse Q_p family, assuming the usual fast monic MPE and its transposes; it is not just a compressed expression.

## Numerator boundary

The same constructor applies to a numerator update only if its FULL pre-filter product support has O(p) explicitly known slots with encoded span below the prepared separation bound. A translated strip of bounded width, including a known monomial prefactor, qualifies. Width w contributes O(wp) slots, and the encoding span/constants must be rechecked. A family of q separately updated numerator strips costs soft O(qp) unless a further shared operation is proved. Sparse norm acquisition by itself does not pay q such updates.

Thus the positive audited result is the deterministic near-linear denominator/norm construction, with the shear-sign and post-shear parity conventions above. Closing the all-numerator affine-tag contraction remains a separate necessary theorem; I have not derived it here. No factoring-rate claim follows from the norm constructor alone.
