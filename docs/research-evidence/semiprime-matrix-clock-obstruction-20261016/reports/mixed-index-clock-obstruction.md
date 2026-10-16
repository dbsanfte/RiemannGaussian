# Small mixed index/geometric-clock scalar and matrix recurrences are excluded

2026-10-16. Classical finite-stream representation theorem. Standard confluent Vandermonde/Hermite interpolation, polynomial minors and finite-orbit interpolation are combined with the certified short-relation box. The integer-index clock is retained formally instead of being dropped. No general operation lower bound, query-acquisition algorithm or new Lean theorem is claimed.

## 1. Scalar statement

Let K be a field, g,q,h nonzero elements, and let A_0,...,A_L be the nonzero chirped coefficients satisfying

 A_0=1,
 g^k(1−q^(k+1))A_(k+1)=(q^L−q^k)A_k, 0<=k<L.

Suppose ord(q)>L+r and, for an integer m>=1,

 g^a q^b!=1 whenever(a,b)!=(0,0), |a|,|b|<=m.                       (1)

For integers r>=1,D_k,D_h>=0 put M_0=(D_k+1)(D_h+1). Assume char(K)=0 or char(K)>D_k, and

 r<=m,       2rD_h<=m,
 (r+1)² M_0<=L−r−M_0+2.                                           (2)

There is NO recurrence

 sum_(t=0)^r P_t(k,h^k)A_(k+t)=0, 0<=k<=L−r,                       (3)

where P_t(Z,X) have bidegree at most(D_k,D_h) and at least one coefficient FUNCTION k->P_t(k,h^k) is not identically zero on the nonnegative integer trajectory. The integer k is interpreted in K, including its characteristic reduction. This nonvacuity requirement is essential: a nonzero formal polynomial may vanish on the whole trajectory, for example through a small finite h-orbit.

All clocks, polynomials and coefficients may be fully advised. The sample range always uses the ORIGINAL nominal order r, even when the effective highest coefficient function occurs at a smaller shift. The characteristic condition is sufficient; no hypothesis char(K)>the total sample count is needed.

## 2. Confluent exponential-polynomial independence

For distinct nonzero lambda_1,...,lambda_v in K, the functions

 n^j lambda_i^n,       1<=i<=v, 0<=j<=D_k,

are linearly independent on the first v(D_k+1) consecutive nonnegative integer samples, provided char(K)=0 or>D_k.

Here is an algebraic proof. Let N_0=v(D_k+1). The map sending polynomials f(T) of degree<N_0 to all their Hasse jets of orders0,...,D_k at the distinct lambda_i is invertible: if every jet vanishes, each(T−lambda_i)^(D_k+1) divides f; their pairwise coprime product has degree N_0, forcing f=0. In the monomial basis its entries are

 binom(n,j) lambda_i^(n−j),       0<=n<N_0.

Transpose this invertible matrix and scale each jet-indexed column j by the nonzero scalar j! lambda_i^j (equivalently scale jet rows before transposing). This gives(n)_j lambda_i^n, where(n)_j=n(n−1)...(n−j+1). The change from falling-factorial polynomials(n)_j to n^j is triangular with diagonal1. Therefore the matrix for n^j lambda_i^n is invertible. All j! are units under the characteristic hypothesis. This remains valid when N_0 exceeds the field characteristic.

Grouping repeated numerical frequencies first, a sum of polynomial-in-n coefficients times distinct lambda^n that vanishes on at least(D_k+1) times the number of frequencies has EVERY coefficient polynomial identically zero.

## 3. Find a regular leading evaluation without extending the sample range

Drop coefficient FUNCTIONS identically zero on the trajectory and let t_*<=r be the largest remaining shift. This does not extend the given range k<=L−r. A nonvacuous function P_(t_*)(k,h^k) has some first nonzero value at j<=M_0−1. Indeed, expand it into at most D_h+1 numerical frequencies h^v with polynomial k-coefficients of degree<=D_k, grouping equal h^v. If its first M_0 samples were zero, section2 would make every grouped polynomial zero, so the function would vanish on the whole trajectory.

Shift k to j+k. The coefficient polynomial becomes

 P_t(Z+j,h^j X),

with unchanged bidegree and leading value nonzero at(Z,X)=(0,1). There remain at least L−r−M_0+2 equations, as charged in(2). If t_*=0, the equation at this selected j contradicts the nonzero A_j directly. Hence assume t_*>=1 below; retaining the original bounds r only overcounts all frequencies.

## 4. Clear the chirped ratios and group coefficient POLYNOMIALS

For the shifted equations the exact ratios are

 A_(j+k+t)/A_(j+k)
 =g^(−jt−binom(t,2))(g^k)^(−t)
  *product_(ell=0)^(t−1)(q^L−q^(j+ell)q^k)
  /product_(ell=1)^t(1−q^(j+ell)q^k).

Every needed denominator is nonzero since j+k+t<=L. Clear their common product through t_*. The resulting numerical frequencies have the form

 g^(−t)q^u h^v,       0<=t,u<=t_*<=r, 0<=v<=D_h,

each with a polynomial coefficient in k of degree<=D_k. There are at most(r+1)²(D_h+1) distinct frequencies. Section2 and(2) imply that EVERY actual numerical frequency group has zero COEFFICIENT POLYNOMIAL in a formal variable Z, not merely zero at the sampled integers. This is the critical extra conclusion needed to retain the index clock.

## 5. Coarsen aliases and use the highest-shift pole over K(Z)

A numerical alias gives g^a q^b h^c=1 with |a|,|b|<=r,|c|<=D_h. A nonzero alias cannot have c=0 by(1). Eliminating h between two aliases gives a g/q relation with both exponents bounded by2rD_h<=m. Thus(1) forces the two exponent determinants to vanish, so all actual alias vectors are rationally collinear.

If no nonzero alias exists, the grouped coefficient-polynomial conclusion already forces every product of the nonzero denominator-cleared ratio multiplier and P_t to vanish. That contradicts the selected nonzero leading value.

Otherwise choose ANY alias(a,b,c), reversing sign so c>0. Replace the formal frequency clocks by

 G=x^c,       Q=y^c,       H=x^(−a)y^(−b).

Every actual numerical frequency group maps to one Laurent monomial; possibly merged groups still have zero coefficient polynomial in Z. No primitive-direction membership or torsion-free quotient is needed. Divide by the nonzero denominator-clearing polynomial. The resulting exact identity over K(Z,x,y) is

 sum_(t=0)^(t_*) x^(−ct) R_t(y^c) P_t(Z+j,h^j x^(−a)y^(−b))=0,       (4)

where

 R_t(Y)=g^(−jt−binom(t,2))
        *product_(ell=0)^(t−1)(q^L−q^(j+ell)Y)
        /product_(ell=1)^t(1−q^(j+ell)Y).

The original g,q in these COEFFICIENTS remain field constants. The clocks G,Q represented g^k,q^k, and only those formal frequency variables are coarsened.

If a!=0, choose a nonzero algebraic y_0 with y_0^c=q^(−j−t_*). Only R_(t_*) has a pole there. Its numerator cannot vanish because that would require q^(L+t_*−ell)=1 with L+1<=L+t_*−ell<=L+r<ord(q). Its other denominator factors are nonzero. The leading P polynomial after substitution is nonzero in K(Z)[x,x^(−1)], because a!=0 and its value at Z=0,X=1 before substitution was nonzero. Consequently that top pole cannot cancel. Inseparability may increase its multiplicity but does not remove it.

If a=0, the distinct powers x^(−ct) separate terms. When b!=0 the leading P_t(Z+j,h^j y^(−b)) is nonzero. When b=0 the leading P_t(Z+j,h^j) is a nonzero polynomial in Z because its value at Z=0 was selected nonzero. Thus its coefficient cannot vanish in either case. This contradicts(4) and proves the scalar theorem.

The case D_h=0 is included: there are no h-direction aliases, so confluent independence directly suffices. In particular ordinary polynomial-in-k holonomic coefficients are covered in this parameter range, rather than being an unmentioned escape.

## 6. Mixed index/geometric MATRIX state

Let s>=1,L>=s and suppose v_k in K^s satisfies

 v_(k+1)=M(k,h^k)v_k/B(k,h^k),       0<=k<L,
 a_k=u^T v_k,

where u is constant, the entries of M and B have bidegrees at most(delta_k,delta_h), and B(k,h^k)!=0 at every actual transition. No invertibility of M, generic state, known h-order or denominator regularity outside the sample window is assumed.

There is a NONVACUOUS scalar recurrence of nominal order s, same range0<=k<=L−s, with coefficient bidegrees at most

 D_k=s²delta_k,       D_h=s²delta_h,                                (5)

provided char(K)=0 or>D_k. This is proof-side existence, not a fast scalarization algorithm.

Define cleared rows

 Z_t(Z,X)=[product_(i=t)^(s−1) B(Z+i,h^i X)]
          u^T M(Z+t−1,h^(t−1)X)...M(Z,X),       0<=t<=s.

They have bidegrees at most(s delta_k,s delta_h). At actual starts they yield the same product of B-values times a_(k+t). Every denominator used lies in0,...,L−1.

Over K(Z,X), rank-rho polynomial minors give a nonzero row dependency with coefficients of bidegrees at most(rho*s delta_k,rho*s delta_h), hence(5). Rankzero permits a constant relation. If ord(h)>D_h, a formally nonzero such coefficient has a nonvacuous integer trajectory: its expansion has distinct h^v frequencies, and section2 forces a polynomial identically zero if the entire trajectory were zero.

If ord(h)=T<=D_h, specialize the CLEARED rows at EACH distinct orbit point X=zeta, and compute a row dependency over K(Z). A nonzero rank minor yields polynomial-in-Z coefficients of degree<=D_k after Cramer clearing; rankzero again permits a constant coefficient. Choose one such nonzero vector at each orbit point and interpolate its coordinates in X to degree<T<=D_h. The resulting row relation holds as a polynomial identity in Z at every orbit point. It is nonvacuous on the integer trajectory: expansion in the T distinct h-frequencies, with coefficient polynomials in Z of degree<=D_k, and section2 exclude an identically-zero trajectory unless every interpolated coefficient polynomial is zero. At least one is nonzero by its chosen orbit value.

All these cleared rows exist even where B vanishes. Only the actual sample-window common denominator is divided; no full-orbit denominator promise or extra state transition is manufactured. Interpolation and order selection are mathematical existence arguments, not supplied hidden-order primitives.

Thus a realization of the certified chirped stream is impossible whenever, with(5) and M_0=(D_k+1)(D_h+1),

 s<=m,       2sD_h<=m,
 (s+1)² M_0<=L−s−M_0+2,
 char(K)=0 or>D_k.                                                (6)

All fixed or polylogarithmic s,delta_k,delta_h satisfy these numerical conditions eventually in the canonical scale. Singular matrices, fully advised initial states and clocks are included. Rational entries can be brought to a common denominator, charging the resulting degree increase; affine updates add a constant coordinate. These are standard conversions and do not license uncharged high-degree representations.

## 7. Actual certified fields, provenance and limits

For L=2m²+2, the all-semiprime paid strong-order setup plus the square-alias screen either factors N or supplies(1) in both hidden fields, with local q-orders>16m². Also their characteristics P,Q exceed16m²>L. Under(2) or(6), D_k<L, so the characteristic requirement is automatic. The q-order margin holds for r<=m. No balance premise, prime-order counterfamily or extra source deletion is introduced. This is a factor-or-representation-obstruction composition, not a claim the screen always factors.

Confluent Vandermonde/Hermite interpolation, falling factorials, Cramer minors and finite-node interpolation are standard. The new composition retains the ordinary index clock as coefficient polynomials and extends the prior arbitrary-geometric-clock scalar/matrix obstruction to bounded mixed dependence. The old known chirped ratio uses two retained geometric powers g^k,q^k (with q=g^d); they are not asserted multiplicatively independent. That ratio remains outside this bounded-degree one-geometric-plus-index contract; there is no contradiction.

The theorem concerns exact agreement on the COMPLETE finite coefficient stream and the explicit parameter/sample bounds. It does not exclude arbitrary multivariate geometric clocks, selected evaluation/jump algorithms, sparse high-degree entries, other transformed streams, nonlinear circuits, direct norms or factor/witness acquisition. It proves no operation lower bound, full-query evaluator, improved factoring exponent or Lean theorem. No native source, frozen report or build is changed. Exact prerequisites are recorded in mixed-source-pins.json; no new external analytic or algorithmic theorem is imported.
