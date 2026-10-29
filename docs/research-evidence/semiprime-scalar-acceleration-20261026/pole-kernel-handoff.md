# A one dimensional kernel target for the long query

26 October 2026. Paper derivation under the existing prepared-ring and unique-cover contracts. This is a sufficient replacement output for the original packed residue, not an identity equating the two numerically. It supplies no faster acquisition algorithm.

## The original query and the changed output

The original six-domain query is the packed additive residue

    C_original = Res_delta sum_(j,t) (K/2+[j²]_n)/(delta+1-T_j*q^(-t)).

Its original one-row-per-colour multiplicity bound belongs to that original bank. The subsequently proved, publicly selected support partition instead has exactly one good row-clock collision in a correct bin. On this selected bank let D(X)=product_j(X-T_j), n_clock=h-1, and theta=q^I be that unique collision. Do not transfer the original bank's count formula to an arbitrary completed catalogue.

The new regularizer is D_delta(X)=D(X)+delta. Set

    F_m(delta)=[1,q,...,q^m](1/D_delta),
    R_m=Res_delta F_m.

The finite divided-difference formula proves simple delta poles in every component. At the unique good collision,

    R_(h-2)=(theta-q^(h-1))*R_(h-1),
    theta=q^(h-1)+R_(h-2)/R_(h-1).

The final denominator is nonzero in the good nonsplit field, including a hit at the final clock point. An actual norm gate therefore factors or permits division on the correct attempt. From theta, the short polynomial H_u(X)=sum_j u_j*product_(k!=j)(X-T_k) gives u=H_u(theta)/D'(theta), with its own norm gate. Both D and H_u are acquired by product-tree operations in soft J without dividing by row differences. The existing bounded tag validator and recovery consumer finish the attempt. Wrong bins do not acquire the good-field promise and must remain bounded attempts.

This removes the long tau product from the requested numerical output. It does not by itself eliminate the work of every algorithm that might compute the output.

## The pole is a single kernel mode

Work modulo z^h. Write

    B(z)=sum_(m<h) q^(m(m-1)/2)*z^m/(q;q)_m,
    (q;q)_m=product_(r=1)^m(1-q^r),
    S f(z)=f(qz),  L=(1+z)S.

Every denominator used here is a certified unit. B has constant coefficient one. The finite Euler identity gives L=B*S*B^(-1). The Newton-converted series C_delta satisfies

    (D(L)+delta) C_delta=1 mod z^h.

Consequently c(z)=Res_delta C_delta satisfies D(L)c=0. Conjugating this equation by B gives the diagonal equation D(S)(B^(-1)c)=0. In the good field, D(q^i) vanishes at exactly one index I. Hence the kernel has dimension exactly one, and direct residue extraction fixes its representative as

    c(z)=(-1)^I*z^I*B(z)/(q;q)_I mod z^h.

In particular every coefficient c_m for I<=m<h is nonzero, while the earlier coefficients vanish. Two final coefficients of ANY nonzero vector in this good-field kernel recover the same theta:

    theta=q^(h-1)+q^(h-2)*c_(h-2)/c_(h-1).

The matrix of L, if written in the monomial basis, has diagonal q^m and one lower diagonal q^(m-1). It need not be materialized: D and the formula L=(1+z)S give a compact input of size O(J). The target asks only for the projective final pair of a kernel vector that is nonzero in the good component; arbitrary zero output is not sufficient. The actual resolvent residue provides that promise.

This is a substantial difference in output structure from computing a full resolvent, whose rank and degree can be large. It does not establish low acquisition cost. Finding the unknown singular diagonal D(q^I), solving for the kernel, or acquiring its final pair is still unpaid. In particular, when I exceeds the paid short prefix, that prefix of c is identically zero; it cannot initialize a nonzero homogeneous solution merely by retaining pole coefficients. The regularized problem carries the necessary singular choice. This observation is not an information-theoretic lower bound on algorithms using all the supplied D coefficients.

## Retained constructive directions

The two-section generator in sectioned-newton.md is compact and exact. Repeated sectioning must preserve only enough of this one-dimensional kernel to obtain its final projective pair; a general full inverse is unnecessary. A useful next algorithm would keep that state and its singular selection within soft J work over all halving steps. The first two scalar Graeffe products do not have the needed parity closure, and the coupled route is audited separately.

The laminar partition algorithm in native-thinning.md can first minimize the available row/window work in soft K, with all cheap bins attempted before expensive fallback. Its scoped balanced-bin price prevents that specific full-window approach from supplying the uniform target. It does not apply to the compact kernel computation above.

The retained complete bound is soft(J+sqrt(Jh))=soft K^(5/4), for J=O(K), h=O(K^(3/2)). A whole-family soft-K kernel-pair supplier, with the actual composite-ring gates and bit costs, remains the missing positive result.
