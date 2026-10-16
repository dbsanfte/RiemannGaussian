# Compressed block aggregation: a positive special case and two representation barriers

The desired actual q-factorial aggregation algorithm was not obtained. There is a genuine nearlinear scalar-product algorithm for a restricted block family, and precise reasons that two natural resultant representations do not yet provide the missing primitive. None is a universal lower bound.

## 1. Contract and exact regrouping

Let R be a commutative ring, q,z_1,...,z_J units, L=bT, Q=q^b, and B(X)=P_b(X;q)=product_(0<=r<b)(1-q^r X). Then

S=product_j P_L(z_j;q)=product_(0<=t<T) C(Q^t),
C(X)=product_j B(z_j X), deg C=Jb.

These are polynomial identities, including at collisions and over Z/N. No cancellation or division is used. A final short block handles nondivisible L. With b about sqrt L and J about sqrt L, explicitly evaluating the J by T grid costs at least JT outputs; this report asks only for S, so that output floor alone is not an obstruction.

Constructing the explicit coefficient array C by a product tree costs soft O(Jb), followed by the existing ring-safe geometric-product primitive of cost soft O(Jb+sqrt(JbT)). Thus this regrouping costs soft O(Jb+sqrt(JL)); at J=b=T=m the first term is m^2. Faster modular composition applied after C has been acquired does not pay for its acquisition. The output-array charge is specific to this representation, not to implicit C or scalar S.

For monic A(Z)=product_j(Z-z_j) and G(Y)=product_t(Y-Q^t), the exact orientation is

S=Res_Z(A(Z), Res_Y(G(Y), B(ZY))).

Both resultants are evaluated with the monic root polynomial as their first argument. The standard explicit quotient R[Z,Y]/(A,G) is free of rank JT; its multiplication-norm interpretation is exact but is not an O(J+T)-size algebra. This rank statement does not forbid another carrier or compressed determinant.

## 2. A genuine cheap aggregation family

Suppose the given block polynomial has the form B(X)=D(X^rho), with deg D=s. Set eta_j=z_j^rho and

F(X)=product_j D(eta_j X), deg F<=Js.

Then S=product_(t<T) F((Q^rho)^t). A product tree constructs F in soft O(Js), exponentiation costs O(J log(rho+1)), and the existing division-free geometric-product algorithm gives total

soft O(Js+sqrt(JsT)+J log(rho+1)) ring operations.

If the degree-b input is supplied as an explicit array, add O(b) to read/verify the support pattern. For fixed s and J=T=m this is soft O(b+m), hence the requested scale when b=Theta(m). No root extraction or discrete logarithm is needed. The scalar S preserves every collision exactly. The algorithm supports row subsets by rebuilding F, and contiguous BLOCK-time restrictions by replacing z_j with z_j Q^start and shortening T. Applying a factoring controller still requires its leaf/global-saturation recovery theorem and any restrictions inside an original block separately: an arbitrary zero of D((z_j Q^t)^rho) does not inherit the original gamma-linear leaf factor-sum theorem, and partial original q-blocks need not retain the support pattern. Ring operations cost soft O(log N) bits each modulo N, giving the corresponding bit bound; modular exponent lengths are charged above. All steps are ring safe because the inherited product primitive uses no division by node differences.

This includes binomials a+cX^rho; it does not include arbitrary polynomials with a bounded number of terms at unrelated exponents.

The actual block does not admit this direct support-stride compression. In each retained hidden field its q-order R_local exceeds b. Its coefficient c_k is

c_k=(-1)^k q^(k(k-1)/2) product_(r=1..k)(1-q^(b-k+r))/(1-q^r), 0<=k<=b.

Every numerator and denominator factor has exponent in [1,b], and is nonzero. Consequently every c_k is nonzero in both hidden fields, hence a unit modulo N. In particular c_1 is a unit, so B(X)=D(X^rho) with rho>1 is impossible as a polynomial identity over Z/N. With rho=1, s=b and the displayed algorithm loses the compression. This excludes only this exact support-stride representation in the original variable; affine changes, other bases, nonlinear compressed representations, and input-dependent algorithms remain open. The coefficient identity is used to prove support, not as an instruction to invert unchecked ring elements.

## 3. A bounded-entry-degree determinant obstruction

Over any field, fix nonzero starts z_j and ratio Q, and treat beta_0,...,beta_b as algebraically independent. For B_beta(X)=sum_r beta_r X^r, the polynomial

S_beta=product_(j,t) B_beta(z_j Q^t)

is nonzero and homogeneous of total beta-degree JT (its beta_0^(JT) coefficient is 1). If S_beta=det M for an r by r matrix whose entries are polynomials in beta of total degree at most c, determinant expansion gives JT<=rc. Thus an affine-entry determinant requires r>=JT. At J=T=m it cannot have dimension O(m).

The same conclusion applies to a quotient det M/det N of polynomial-entry determinants with det N nonzero: the polynomial identity det M=S_beta det N gives deg det M=JT+deg det N, so the numerator still has dimension at least JT/c. It does not apply to arbitrary rational entries with uncharged denominator manipulations, or to entries allowed large beta-degree and succinct powering circuits.

This is a representation theorem, not an operation lower bound: a polynomial can have huge degree and a tiny repeated-squaring circuit. Moreover the actual q-binomial coefficients lie on a special parameterized family rather than being independent beta variables. No reduction from a fast actual-family algorithm to a generic-beta determinant is supplied, so the obstruction must not be promoted to an actual-family computational impossibility.

## 4. Fresh primary resultant checks

Jeronimo--Sabia, *Sparse resultants and straight-line programs* (JSC 87, 2018), explicitly uses arithmetic over Q (section 2.3). Theorem 10 is a probabilistic construction, for essential supports, of an SLP for a scalar multiple of the sparse resultant; its length is

O(D^4 (D^(Omega-2)+delta^(omega+1) log(D) Qexp^2 log(Qexp) n^10 Ncoeff)).

D is total resultant degree (sum of mixed volumes); delta is a mixed volume; Qexp bounds support exponents. Here Omega denotes their determinant exponent, not an input size. The theorem is polynomial in degree, not nearlinear in the succinct support or SLP length. In our generic aggregate the beta multidegree alone is JT, so a resultant representation carrying it as a coefficient group cannot have D<JT. This existing upper bound therefore does not give the target. This does not prove that a better specialized algorithm cannot exist. Their Q-arithmetic/random-specialization construction also cannot simply be called modulo an unknown composite: scalar constants, inversions, and normalization require a separate ring-safe specialization argument and charged bit costs.

Primary author/institutional PDF: https://ri.conicet.gov.ar/bitstream/handle/11336/89011/CONICET_Digital_Nro.9f5a9366-0db2-455c-8733-7fb11571421e_A.pdf?sequence=2 . Exact local PDF and extracted text are pinned in manifest.json.

Groh--Zach, *Computing A-resultants via direct images*, arXiv:2602.14657v1 (16 February 2026), gives an algorithm for toric direct-image/Weyman complexes and practical smaller resultant complexes. Theorem 2.1 concerns a toric variety over a field and a commutative Noetherian coefficient ring; it is not a soft O(b+J+T) scalar-resultant complexity theorem. Section 2.2 Gaussian simplification expressly assumes an invertible pivot submatrix. Such simplification over Z/N needs unit/factor-aware pivots. Neither the abstract nor that theorem provides a bound eliminating the mixed-volume/coefficient-degree cost for our grid product. Section 3 examples are not asymptotic theorems for this family. Applying a determinant construction with bounded-degree beta entries remains subject to section 3 above; allowing higher-degree entries moves work into their acquisition rather than proving it cheap.

Primary: https://arxiv.org/html/2602.14657 ; PDF https://arxiv.org/pdf/2602.14657 . Both papers were freshly inspected; local PDFs/text are saved. These checks are targeted, not an exhaustive negative literature result.

## 5. Remaining positive target

A useful theorem would aggregate a dense but q-hypergeometrically specified B=P_b across J geometric ranges without explicitly acquiring C's Jb coefficients, the JT values, or a JT-dimensional bounded-entry-degree determinant. The bounded-support-stride case proves that compressed scalar aggregation can beat the grid floor; the actual block's full unit support explains exactly why that simple construction does not transfer. No soft O(J+sqrt L) actual-source algorithm, or general impossibility theorem for one, is claimed.
