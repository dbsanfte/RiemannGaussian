# Translated cyclotomic logarithmic observables: initialized tests and boundaries

24 October 2026. Read the actual globally-zero theorem in /home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-cyclotomic-row-cancellation-20261016/README.md. No repository changes or finite examples. The translated unit avoids that theorem's self-reciprocity hypothesis, but the concrete derivative/ratio selectors tested here do not give a covered fast factor query.

## Acquired algebra data

Work in A=(Z/NZ)[Z]/(Z^m-1), m odd prime and a certified unit. Let u=beta+zeta, with beta's local orders odd. The exact inverse certificate is

    (beta+Z)*sum_(r=0)^(m-1)(-1)^r beta^(m-1-r) Z^r
      =beta^m+Z^m.

Modulo Z^m-1 the right side is beta^m+1, a unit: in either hidden field an odd-order element beta^m cannot equal -1. The inverse is therefore acquired by one certified scalar inversion and soft m algebra arithmetic. Negative native ell powers are lawful.

Compute f=u^N and q=u^(m²) by binary powering. With explicit cyclic convolution this costs soft(m log N) and soft(m log m), respectively; sigma_j and sigma_j inverse are coefficient permutations, costing O(m) words when materialized. A supplied row

    T_j=u^ell_j (sigma_j u)^a_j sigma_(j^-1)(f)

is then acquired in soft(m log N) operations, or soft m suppressing logarithmic exponents. Acquiring all m-1 rows independently costs soft m², even though f is shared. No row vector or comparison list is taken as a free input.

The original own-tag proof survives at the point beta: modulo P, for j=P modulo m, Frobenius fixes the scalar beta, so T_j=q^I. This does not supply a local-order or collision guard for q. Neither augmentation beta+1 nor norm beta^m+1 inherits the prepared order of beta. The old beta decoder therefore cannot recover a factor from a global translated-algebra equality without a new proof or retaining the original scalar beta query.

## Test 1: nonselfreciprocal star ratio

Now u*=beta+zeta^-1 generally is not a monomial phase times u. Let w=u/u*, an acquired unit. Direct arithmetic gives the valid observable

    T_j/T_j*=w^ell_j (sigma_j w)^a_j sigma_(j^-1)(w^N).

Unlike the old anti-invariant, this is not forced to be one globally. However own-tag equality only implies

    T_j/T_j*=(q/q*)^I=(w^(m²))^I mod P.

Thus the long unknown exponent remains. Setting the ratio to one would require an independently proved period dividing m² for w, which is not provided. A coefficient gcd of T_j-T_j* is an initialized opportunistic factor test, but is not a covered selector. It can be computed in soft m per supplied row; its full-family cost is soft m². Being nonzero globally repairs the old degeneracy but does not eliminate I.

## Test 2: logarithmic derivative in zeta and its exact carry

The apparent extractor delta=Z*d/dZ does NOT descend to A. Indeed delta(Z^m-1)=m Z^m=m modulo the defining relation, and m is a unit. Define delta only on the degree-<m representative.

For acquired representatives p,r of degree <m, write pr=s+(Z^m-1)Q, with deg s<m. Reducing the ordinary derivative gives the exact product law

    delta(s)=(delta p)*r+p*(delta r)-m Q mod (Z^m-1).       (1)

The quotient carry Q is acquired in soft m from explicit p,r. It cannot be dropped. In particular, if

    (beta+Z)^n=R_n+(Z^m-1)A_n,

then

    delta(R_n)=n Z u^(n-1)-m A_n mod (Z^m-1).             (2)

A binary powered state can acquire R_n and the corresponding carry for a SUPPLIED n in soft(m log n); equivalently, once R_n and n are supplied, (2) acquires the reduced carry directly. For own-tag n=m²I, n and the reduced carry are not supplied. Treating delta(R_n)/R_n as n Z/u without the carry is false. Every operation in a purported coefficient logarithm extractor must retain this boundary, and the known T_j does not determine the unknown scalar n through (2) because the unknown carry changes with n.

There is no algebra derivation fixing R and moving zeta that repairs this: differentiating zeta^m=1 forces m*zeta^(m-1)*D(zeta)=0, hence D(zeta)=0. A thickened defining ideal would introduce different tangent data; it does not preserve the own-tag equality for free.

This is an exact failure of this proposed differential algorithm, not an arithmetic lower bound on other observables.

## Test 3: scalar-beta tangent is lawful but loses own-tag coverage

Introduce a formal scalar B and differentiate the explicit expression defining T_j(B), then specialize B=beta. This is a legitimate algebra operation. Since N=0 in R, the derivative of (B+zeta)^N vanishes, and the acquired logarithmic derivative is

    T_j'(beta)/T_j(beta)
      =ell_j/u+a_j/(beta+zeta^j).                         (3)

It is acquired in soft m for a supplied row. However the own-tag point equality T_j(beta)=u^(m²I) modulo P is NOT an equality of B-functions near beta. Frobenius gives

    (B+zeta)^P=B^P+zeta^j,

whereas sigma_j(B+zeta)=B+zeta^j. These agree at B=beta but their derivatives differ. More explicitly, modulo P the own-tag row as a B-function is

    (B+zeta)^ell * (B+zeta^j)^a * (B^P+zeta)^Q.

Its derivative is exactly (3). The comparison power has logarithmic derivative (aP+Q+ell)/u=(Q+ell)/u modulo P. Requiring tangent equality would additionally require

    a*u/(beta+zeta^j)=Q

as an algebra identity; this is not an own-tag consequence and is generally nonconstant when j differs from 1. Thus extending the point comparison to dual numbers is an invalid coverage step. It cannot recover I from (3).

## Explicit long-comparison fallback and its limits

One can acquire baby powers q^r for r<b and giant row values T_j*q^(-bt) for t<h/b by explicit algebra multiplication. This uses soft(m*(b+h/b)) ring work for ONE supplied row and stores Theta(mb) coefficients if all baby vectors are kept. At h~m²,b~m this is already soft m² per row, exceeding the desired whole-query soft m. Materializing all rows incurs at least soft m² before comparisons.

More seriously, exact tuple sorting modulo N only finds global equalities; an own-tag equality modulo P alone does not imply equal coefficient tuples modulo N. Coefficient projections and monic MPE can test scalar projected collisions without inverses, but extra globally coincident projected values can saturate gcds. No argument here guarantees a proper factor witness from such saturation. Even a true global algebra equality is not covered by the original beta order decoder: q has no inherited separation guarantee. Hence this is not presented as an initialized complete factoring fallback. The original scalar beta query remains necessary unless translated comparison recovery is separately proved.

## Ledger and focused result

| Operation | Paid cost | Delivered information |
|---|---:|---|
| u inverse, f=u^N, q=u^(m²) | soft(m log N) | explicit algebra units |
| One T_j | soft m | explicit m coefficients |
| All T_j by present construction | soft m² | exceeds desired whole-query clock |
| One star ratio or derivative test | soft m after row | initialized, but no covered I elimination |
| Delta carry for supplied exponent | soft(m log n) | carry paid only for supplied n |
| Unknown-I delta extractor | uninitialized carry | no exponent/factor oracle |
| Beta tangent selector | soft m after row | rejects valid own-tag point relations in general |
| One-row algebra BSGS data | soft(m sqrt h) | comparison/recovery still not guaranteed |

The translated choice supplies a genuine escape from the old globally-zero anti-invariant theorem, but nonselfreciprocity alone is not factor-producing. The concrete star ratio retains I; zeta differentiation has an exact quotient-carry boundary; scalar differentiation fails to preserve own-tag Frobenius. A successful observable must both eliminate the long exponent and prove proper-factor recovery under translated collisions, while acquiring its selected rows below the all-row m² cost. No new query or factoring exponent is obtained.
