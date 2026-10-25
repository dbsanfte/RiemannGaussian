# Exact conductor-m^3 colour and its remaining query

This is a symbolic derivation, not an evaluator or an improved factoring bound. All algebras containing zeta_(m^3) below are proof-only; the resulting targets and seed lie in the much smaller zeta_m algebra. No large cyclotomic carrier is charged as if it were free.

Let m be an odd prime, m coprime to N. Every unit modulo m^3 uniquely has the form v(1+mt), where v is a Teichmueller unit and t is modulo m^2. Define the primitive character of order m^2

    chi(v(1+mt))=zeta_(m^2)^(t-m*t^2/2).

Here division by 2 is modular. The truncated logarithm verifies multiplicativity exactly modulo m^2. Write t=t0+m*s in its Gauss sum. Summation over s vanishes unless v=-1 modulo m. The unique Teichmueller lift is literally v=-1, so

    u=tau(chi)=m*zeta_(m^3)^(-1)*G,
    G=sum_(t mod m) zeta_m^(-t^2/2),
    G^2=epsilon*m, epsilon=Legendre(-1,m).

Thus the primitive conductor-m^3/order-m^2 Gauss sum has a scalar/quadratic amplitude A=mG, A^2=epsilon*m^3, times one primitive additive phase. This formula can be proved and used without materializing the conductor-m^3 algebra.

For the native row put a=a_j, b=b_j, c=c_j, ell=m*b-2*a*j, E=N+a+ell and d=m^2, with

    m^2*c-j*m*b+j^2*a=N.

At a prime P dividing N with P=j+m*h, define the true integer I=(aP+N/P+ell)/d. Direct expansion gives the exact integer identity

    I*P=a*h^2+b*h+c.

In particular

    I=f_j(h)=(a*h^2+b*h+c)/j mod m,
    (b+2*a*h)^2=Delta+4*a*j*I mod m,
    Delta=b^2-4*a*c.

The sign of Delta and the coefficient 4*a*j are as displayed.

Let phi be full P-Frobenius, including all nested roots. On G it acts by Legendre(j,m), and on zeta_(m^3) by exponent P. Therefore the literal native source is

    T=A^E*Legendre(j,m)^(a+N)
        *zeta_(m^3)^[-ell-aP-N/P],

where N/P in the exponent means N times the inverse of P modulo m^3. Since the native row vanishes to order m^2 for every lift P=j+m*h, its phase is exactly zeta_m^[-f_j(h)]; P's third digit cancels. Also

    q=u^d=A^d*zeta_m^(-1).

This retains a genuine index colour, but that colour is the quadratic function f_j of the unknown second digit h. It is not public index recovery.

The image R_j={f_j(h):h mod m} is explicit. Since a,j are units modulo m,

    R_j={r: Legendre(Delta+4*a*j*r,m) is 0 or 1},
    |R_j|=(m+1)/2.

The equality is exact: completing a square is a bijection on h before squaring. One can acquire each row's admissibility function by this formula; no hidden h is used. A whole family of these predicates is described in soft O(m) words by a,b,c,j, without expanding an m-by-m table. Such a compressed description is not evaluation of the associated query.

The same retained phase, with fewer auxiliary ingredients, follows from the proof-only source u0=gamma*zeta_(m^3)^(-1) for any prepared scalar gamma. Then

    T_(j,h)=gamma^E_j*zeta_m^[-f_j(h)],
    q0=gamma^d*zeta_m^(-1).

Thus the extra wild Gauss amplitude is unnecessary for this particular colour mechanism. This source exactly preserves the original own-tag collision. Potential additional extension-ring collisions can be raised to the mth power to recover a scalar annihilator; the exponent multiplier has O(log m) bits. It does not require interpreting the proof-only high-conductor algebra as an acquired object.

The precise remaining scalar observable is the native query restricted to I mod m in R_j, or a source-preserving extension-ring equivalent:

    product over j and native I with I mod m in R_j
       (gamma^E_j-gamma^(d I)).

True own-tag coverage is retained, but the restriction has about one-half of the native index classes in every row. Writing each row in O(log N) parameters or expressing its mask as a quadratic character does not acquire this long product. No soft O(m) simultaneous evaluator or locator for that character-masked query has been proved here. The result is exact cancellation of the third digit and an exact retained quadratic colour, not recovery of the second digit or a universal rate gain.

## What further precision at the same prime adds

The exact identity also gives

    a*h^2+(b-mI)*h+(c-jI)=0,
    D(I)=(b-mI)^2-4*a*(c-jI).

At every modulus m^t, existence of h is equivalent to D(I) being a square, since 2a is a unit. Modulo m, D(I)=Delta+4ajI is a nonconstant affine function. Exactly (m-1)/2 residue classes I0 make it a nonzero square. For EACH such class, every lift I=I0 mod m has square D(I) modulo every m^t, by Hensel lifting the nonzero square root. Hence even arbitrarily high same-prime digit precision leaves at least (m-1)/(2m) of all index classes. Only the one I0 with D(I0)=0 mod m can be further thinned by higher digits. This is an exact fact about this retained residue predicate; it does not rule out a new evaluator using its weights or other arithmetic.
