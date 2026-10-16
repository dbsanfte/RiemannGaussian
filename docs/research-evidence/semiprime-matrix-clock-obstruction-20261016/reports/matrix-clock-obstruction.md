# Small rational matrix state in one geometric clock is excluded for the certified chirped stream

2026-10-16. A classical representation theorem. Standard polynomial-minor scalarization and finite-node interpolation are combined with the preceding arbitrary-clock scalar obstruction. The finite-orbit nonvacuity repair is explicit. No long-query evaluator, general operation lower bound, or new Lean theorem is obtained.

## 1. Generic finite realization-to-recurrence lemma

Let K be a field, h a nonzero element, s>=1 and L>=s integers, and delta>=0. Suppose a state v_k in K^s, 0<=k<=L, satisfies

 v_(k+1)=M(h^k)v_k/B(h^k),       0<=k<L,                           (1)

where M is an s-by-s polynomial matrix and B a polynomial, all of degree at most delta. Assume B(h^k)!=0 for exactly the needed times0<=k<L. Let u in K^s be a constant output vector and a_k=u^T v_k. No invertibility of M, genericity of the state, known order of h, or independence of h from other parameters is required. The entire realization may be privately advised.

Then there exist polynomials P_0,...,P_s of degree at most

 D=s² delta                                                       (2)

such that

 sum_(t=0)^s P_t(h^k)a_(k+t)=0,       0<=k<=L-s,                    (3)

and at least one coefficient FUNCTION k->P_t(h^k) is not identically zero on the entire h-orbit. This is the same nominal order s and the same finite equation range, even if the effective highest nonzero coefficient function occurs earlier. The conclusion is a proof-side existence lemma, not an algorithmic order-finding or cheap scalarization theorem.

## 2. Clear the state denominators uniformly

Set

 b_s(X)=product_(i=0)^(s-1) B(h^i X),
 Z_t(X)=[product_(i=t)^(s-1)B(h^i X)]
          u^T M(h^(t-1)X)...M(X),       0<=t<=s.                    (4)

The matrix product is empty for t=0 and the scalar product is empty for t=s. Each Z_t is a polynomial ROW of length s and degree at most s delta: there are t matrix factors and s-t scalar factors. On every available starting index0<=k<=L-s, iterating (1) gives

 Z_t(h^k)v_k=b_s(h^k)a_(k+t),       b_s(h^k)!=0.                    (5)

All denominator exponents k+i lie in[0,L-1]. Therefore a polynomial row dependency on the Z_t, or a row dependency at each h-orbit point, yields (3) after division by this nonzero scalar at available times.

Crucially the CLEARED polynomial rows Z_t exist at every orbit point, including points outside the available time range at which B might vanish. We will never divide by b_s there. No nonzero-denominator hypothesis on the full orbit is silently added.

## 3. A bounded-degree polynomial dependency

Let rho be the rank over K(X) of the (s+1)-by-s matrix of rows Z_t. If rho=0 every Z_t is zero; take P_0=1 and all other P_t=0, obtaining a nonvacuous dependency of degree zero.

Otherwise choose rho independent rows and rho columns whose square minor has nonzero determinant Delta. Choose any further row Z_j. The selected rows span the full row space. Solving for Z_j on these columns by adjugate/Cramer's rule, and multiplying by Delta, gives a dependency between Z_j and the selected rows whose coefficient on Z_j is Delta. It holds on ALL columns: the row is in their span over K(X), and the selected-column solution is unique. Thus it is a genuine polynomial row dependency, not only a relation on a chosen minor.

Every coefficient is a rho-by-rho determinant of entries of degree<=s delta, so its degree is at most rho*s delta<=s² delta=D. At least one coefficient polynomial is nonzero. The rank-rho row set has an additional row because rho<=s<s+1. Zero coefficients, singular M, and a lower actual rank cause no gap.

If ord(h)>D, including infinite order, a nonzero polynomial of degree<=D cannot vanish on the whole orbit: its first D+1 nodes are distinct. Hence this dependency already has a nonvacuous coefficient function and proves the lemma in this case. When delta=0, D=0 and ord(h)>=1>D, so this case automatically includes constant systems and h=1.

## 4. Repair nonvacuity on a short finite orbit

The remaining case is finite ord(h)=R<=D. At each of the R distinct orbit points x choose a nonzero vector p(x) in the kernel of the transpose row matrix: there are s+1 coefficient unknowns and only s row coordinates, so such a vector always exists, regardless of rank. Equivalently sum_t p_t(x)Z_t(x)=0.

Interpolate each coordinate p_t(x) on these R distinct field points to a polynomial P_t of degree<=R-1<=D. At every orbit point the interpolated row relation holds. At least one coefficient function is not identically zero, since the chosen vectors are nonzero; in fact at each orbit point at least one coordinate is nonzero. Thus (5) gives (3) at all available starting times.

This interpolation is only a mathematical existence argument. No order of h, enumeration oracle, or computed interpolation output is being supplied to an algorithm. Field differences between the distinct orbit points are invertible. The cleared rows are defined even at points where B vanishes; only available-time b_s values are divided. Hence the argument neither assumes denominators are nonzero on the full orbit nor manufactures extra state transitions beyond k=L-1. It also works when the available sample range is shorter than the orbit.

Sections2–4 prove the generic lemma. Nonvacuity means a coefficient function is nonzero somewhere on the orbit, not that a formally nonzero polynomial was merely written down. This distinction is necessary for finite-order clocks.

## 5. Application to the actual certified coefficient stream

Let N=P Q with distinct odd primes, m at the public sixth-root scale, N<=m^6. The paid all-semiprime setup and square-alias screen either factor N or provide g=beta,q=beta^(m²) with both local q/g orders>16m² and the simultaneous relation exclusion

 g^a q^b!=1 for (a,b)!=(0,0), |a|,|b|<=m                           (6)

in each hidden field. The mixed relations are excluded by the screen's unit differences; axes follow from the order bounds. Numerical local orders need not be known, prime, or equal. This costs soft O(m) bits and needs no balance premise or new source-family deletion.

Put L=2m²+2 and define

 product_(i=0)^(L-1)(1-q^i T)=sum_(k=0)^L c_k T^k,
 A_k=c_k g^(-binom(k,2)).

These coefficients are nonzero and satisfy the exact relation

 g^k(1-q^(k+1))A_(k+1)=(q^L-q^k)A_k.

Suppose a rational SINGLE-CLOCK realization (1), with constant output u^T v_k=A_k for ALL0<=k<=L, exists over either hidden field. Its h, coefficients, state and output may be fully advised, and M may be singular. The generic lemma gives a nonvacuous scalar recurrence of nominal order r=s and coefficient degree<=D=s² delta, throughout exactly0<=k<=L-s.

The preceding arbitrary-clock scalar theorem excludes this recurrence whenever

 s<=m,       2s³ delta<=m,
 (s+1)²(s² delta+1)<=L-s-s² delta+1.                               (7)

Indeed these are exactly r<=m,2rD<=m and its finite sample-count condition. The required q-order margin ord(q)>L+s follows from ord(q)>16m² and s<=m. Its proof may shift by at most D positions to find a regular leading coefficient, but the numerical condition in (7) explicitly charges that sample loss. No shortening of the effective recurrence is used to extend the available k range.

Consequently, on the certified no-factor branch there is NO such realization satisfying (7), in BOTH hidden fields, simultaneously for every scalar clock h and arbitrary advice. In particular all fixed or polylogarithmic dimensions s and degree bounds delta satisfy (7) eventually. This is a factor-or-representation-obstruction composition; it does not force the screen to factor every input.

## 6. Rational entries and affine updates

If each rational matrix entry is supplied as a numerator/denominator of degree<=delta_entry, and every entry denominator is nonzero at all available times, multiply the at most s² denominators to obtain a common B. Every entry of its cleared numerator matrix has degree at most s² delta_entry. The previous result applies with common delta<=s² delta_entry; all dimension/degree factors must be charged. No interpolation pivot or quotient-algebra inversion is made free by this observation.

An affine recurrence can be made linear by adjoining a constant coordinate1. This increases state dimension by one, and the affine offset entries must also be included in the common denominator/degree accounting. A constant output plus a constant term is handled by the same coordinate. These are standard representation conversions, not free compressed algorithms. If dimension or degree grows beyond (7), this theorem simply gives no exclusion.

## 7. Provenance and limits

Polynomial-minor/Cramer scalarization, root counting and finite-node interpolation are standard. The new composition applies them to the certified finite chirped stream, with an explicit short-orbit repair preventing zero-on-orbit scalarizations from escaping the earlier nonvacuous theorem. A scoped search of recent recurrence/source packets found no matching actual-source matrix consequence; no absolute literature-priority claim is made. The earlier arbitrary-clock scalar result and paid setup/screen are pinned dependencies.

This result concerns exact step-by-step rational matrix state in ONE scalar geometric clock, with bounded polynomial degree, a constant output functional and agreement with the COMPLETE finite coefficient stream. It is not a bound on arbitrary vector programs or arithmetic circuits. Two-clock coefficients are deliberately outside it: the known scalar ratio already has low bidegree in g^k,q^k. Another transformed stream, sparse high-degree rational entries, selected jump/evaluation algorithms, selected convolution, nonlinear state, direct norms and factor/witness-only methods remain open. High polynomial degree by itself is not an operation lower bound.

The existing long-query acquisition clock is unchanged. No query evaluator, complete sixth-rate factoring algorithm, native code, Lean declaration, numerical example or broad build is supplied. The lemma's scalarization/interpolation is proof-side; no hidden order or interpolation data is presented as a paid input. Frozen prior reports and repository files remain unchanged.
