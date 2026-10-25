# Execute a compressed coefficient-system solver for the geometric grid

24 October 2026. Scratch only. The concrete candidate is a banded q-difference linear system with a sparse right-hand side, followed by a short remainder projection. All its diagonal pivots are units. A complete nearlinear-in-LENGTH solver exists and is initialized below; it costs soft-O(k²), not the desired soft-O(k). An exact inverse factorization identifies the missing generators in a proposed short Schur-complement solver. This is a scoped acquisition result, not a lower bound for scalar or implicit methods.

## 1. Actual input, exact length and units

Use `../semiprime-quadratic-batch-20261024/reciprocal-recurrence.md`, final SHA256 `4642b776f4c72a42a5a2c20beac07b25dbff0a21ba9f3569cd495108d4801f1b`. In particular the balanced main length is ell=2H with H=k², m=k, G=2k; the full original horizon is ell+2. Reciprocal augmentation MUST use a0=q^(1-ell), not the full-horizon reciprocal parameter. The two actual tail factors are already acquired at original indices ell,ell+1. Optional repaired horizon3H+2 uses main3H and G=3k. These choices avoid an assumed balanced factorization of2H+2.

Let Q=q^k and let

    R(T)=product_(j,g<G)(T-Q^g y_j), D0=JG,
    F(T)=product_j(T-y_j),
    A(T)=F(Q^(-(G-1))T), B(T)=A(Q^G T).

The letter B(T) denotes a polynomial; the coefficient algebra is denoted mathcalB below. A need not be monic, but A(0)=B(0) is a known unit. All degree-J arrays are acquired in soft-O(J), including their scales. The native degree J is <=k; after reciprocal augmentation it is <=2k, so D0<=4H<16H and D0<P,Q. The corresponding monic short polynomial is Phi_m(T)=product_(i<m)(T-q^(-i)); its coefficients and root labels cost soft-O(m). Its nonmonic unit multiple is P_m(T)=product_(i<m)(1-q^i T).

The rough-component hypothesis matters. Every local component order of q is k-rough and exceeds16H. Since gcd(k,ord(q))=1, Q has the SAME component order. Thus Q^n-1 is a unit for1<=n<=D0 even though the written exponent kn may exceed16H. This follows from actual roughness and the actual q screen; the exponent guard alone would not justify it. Integers1,...,D0 are units because D0<P,Q. No local field, logarithm or primitive-root oracle is used.

The constant coefficient is actual acquired data:

    R0=(-1)^D0 (product_j y_j)^G Q^[J G(G-1)/2].

Both end prefixes of length m in the reciprocal augmentation are paid input from the pinned report. The algorithm below does not reinterpret them as a middle vector.

## 2. The explicit system: small input and sparse right-hand side

The exact operator is

    L(h)=A(T) h(QT)-B(T) h(T),    L(R)=0.          (1)

Write A=sum a_i T^i, B=sum b_i T^i with b_i=a_i Q^(Gi), and R=sum r_n T^n. For1<=n<=D0,

    a0(Q^n-1) r_n
       + sum_(1<=i<=min(J,n-1))
            (a_i Q^(n-i)-b_i) r_(n-i)
       =(b_n-a_n) R0.                            (2)

Coefficients beyond degree J are zero. Thus (2) is an ACTUAL lower triangular band-J system of dimension D0. Its diagonal entries a0(Q^n-1) are certified units, and its right-hand side has only J possibly nonzero coordinates. The input metadata, diagonal rule, bands and sparse right-hand side cost soft-O(J); an explicit D0-vector is not claimed as input. Direct band substitution costs O(J D0), with only these certified inverses. The supplied bottom coefficients are consistent additional boundary data, not a missing singular-pivot repair: (2) already uniquely determines the whole vector from R0.

This is an attractive compressed linear-system candidate. Nevertheless dimension D0 and bandwidth J are separate parameters. Calling a solver merely because the number of supplied polynomial coefficients is O(J) does not eliminate its precision/dimension parameter.

## 3. Execute a faster complete solver over the actual ring

Set U=R/R0 so U(0)=1, and let

    log(A(T)/a0)=sum_(n>=1) l_n T^n.

Taking formal logarithms of (1) in the T-adic ring gives

    log U(T)=sum_(n=1)^D0
        l_n * (Q^(Gn)-1)/(Q^n-1) * T^n mod T^(D0+1). (3)

Algorithm: acquire the first D0 coefficients of log(A/a0) using monic/formal series inverse and differentiation/integration; acquire Q^n,Q^(Gn) and the certified inverses Q^n-1 for1<=n<=D0; multiply coefficientwise in (3); exponentiate to precision D0+1; multiply by R0. All integer divisions and q-divisions are justified in Section1, and every formal inverse has known unit constant term. This reconstructs the actual full polynomial R in soft-O(J+D0) work and O(D0) coefficient storage. No logarithm of an actual nonunit native value is taken: these are formal series with constant1.

Once R is acquired, monic division computes R mod Phi_m in soft-O(D0+m). The scalar resultant is then obtained by short monic evaluation or guarded gcd/resultant arithmetic. The phase is explicit: if alpha=(-1)^m q^[m(m-1)/2] is the leading coefficient of P_m, then

    Res(R,P_m)=Delta_main,
    Res(P_m,R)=(-1)^(m D0) Delta_main
             =alpha^D0 product_(i<m) R(q^(-i)).   (4)

For reciprocal augmentation the corresponding main scalar is a known unit times Delta_main², as in the pinned report; combine the ACTUAL tail squared. Nonunits are not inverted. Original block/localization fallback costs soft-O(J+sqrt(J ell)), below this dense solver's cost, and retains the original row/index labels. A reciprocal main hit maps to ell-1-i, never to the two tail indices. This gives a complete factor-or-original-witness interface within soft-O(D0), even if an auxiliary resultant is saturated.

At J~k,G~k this executed solver costs soft-O(k²), and is worse than the retained soft-O(k^(3/2)) query. Its useful positive fact is that even this compressed system's entire vector can be acquired in nearlinear D0 time with every pivot safe; field linear algebra is unnecessary for this scalar case.

## 4. Try a compressed inverse / short Schur complement

There is an exact factorization of the inverse on zero-constant inhomogeneities. Write h=R v. Since A R(QT)=B R(T),

    L(Rv)=A R(QT) [v(QT)-v(T)].                   (5)

For an input f with f(0)=0 and prescribed h(0)=0, (5) gives

    h = R * I_Q( f / [A R(QT)] ),
    I_Q(sum_(n>=1) f_n T^n)
                  =sum_(n>=1) f_n/(Q^n-1) T^n.  (6)

All operations here can be performed formally at finite precision. Because A R(QT)=B R and all their constants are units, the inverse map is precisely

    Toeplitz(R) diag_(n>=1)(1/(Q^n-1))
                                      Toeplitz(1/[B R]). (7)

This is the strongest tested generator shortcut: replace elimination of D0 variables by two Toeplitz actions and a diagonal scaling, and ask only for the m-dimensional remainder of the output. But its generators are the ACTUAL prefixes of R and 1/(B R) through precision D0. The acquired top/bottom length-m vectors do not instantiate those middle coefficients. The first m inverse-series coefficients cost soft-O(J+m), as expected; using (7) for arbitrary long input/output contractions would still need a new implicit Toeplitz/gauge action. Formula(7) is not charged as an initialized nearlinear-in-m inverse.

One can express the precise requested Schur output without writing a free right-hand side. Let M denote (2) on variables r1,...,r_D0, and let b be its J-supported right-hand side. For h=0,...,m-1 define

    H[h,n]=[T^h](T^n mod Phi_m).

Then the desired remainder is the known R0 contribution plus H M^(-1)b. H has an acquired order-m recurrence given by Phi_m, or a known-root description using q^(-i); its D0*m array is not supplied. A structured solver for this single matrix sandwich at soft-O(J+m+G) would meet the target. The initialized (7) still contains the unacquired long gauge factors. This is a specified short-output problem with an actual sparse b, not a claim that the output requires all R coefficients.

A literal displacement calculation also prevents an incorrect application of a rank-two Sylvester solver. Let Z be the lower shift on the D0 unknown coordinates, Lambda=diag(Q^1,...,Q^D0), and T_A,T_B the lower triangular Toeplitz matrices of A,B. Then M=T_A Lambda-T_B and

    M Z-Q Z M=(Q-1) Z T_B.                       (8)

Since b0 is a unit, T_B is invertible; Z has rank D0-1. Thus the right side has local-field rank D0-1, not constant. Ordinary unweighted shift displacement similarly has rank D0-1. This only excludes assigning low rank to THESE literal operators; it is not a classification of all displacement representations. Higher-order displacement or a different generator calculus could still exploit the compact operator. The explicit nearlinear-D0 solver already exploits more structure than a generic dense solver.

## 5. Primary theorem contracts on this exact instance

Alin Bostan, Muhammad F. I. Chowdhury, Romain Lebreton, Bruno Salvy, Eric Schost, *Power Series Solutions of Singular (q)-Differential Equations* (2012), [primary author PDF](https://mathexp.eu/bostan/publications/BoChLeSaSc12.pdf), Definition1 and Theorems1--2. The base coefficient object in the theorem is a FIELD K. The unknown is a dimension-n vector series at PRECISION N, with supplied coefficient series truncated through N. For a good constant spectrum, divide-and-conquer costs O(n^omega M(N) log N); the Newton variant costs O(n^omega M(N)+n^omega log(n)N). The good-spectrum definition explicitly excludes the relevant small q-resonances; it is not an unconditional promise for finite-order q.

Here normalize (1) as

    T delta_Q R = C(T) R(QT),
    C(T)=[B(T)-A(T)]/[(Q-1)B(T)],
    delta_Q f=[f(QT)-f(T)]/[T(Q-1)].              (9)

This has dimension n=1, singular exponent1, C(0)=0 and initial coefficient R0. Its only resonance through precision D0+1 is the freely supplied constant: for positive index i the indicial value is a unit multiple of (Q^i-1)/(Q-1). Thus the local field hypotheses really hold. The theorem specializes to soft-O(D0), not soft-O(J), because N=D0+1. Input C(T) to that precision can be acquired from the rational degree-J data in soft-O(D0); it is not a length-m input to a degree-D0 solver. Formula(3) independently proves the requisite extension to our composite ring using only the certified units, rather than invoking all field linear-system steps over mathcalB without proof.

Vincent Neiger, *Fast Computation of Shifted Popov Forms of Polynomial Matrices via Systems of Modular Polynomial Equations*, ISSAC2016, [primary HAL PDF](https://inria.hal.science/hal-01266014/preview/fast_popov_form.pdf), Problem2 and Theorem1.4. Given explicit polynomial equation columns over a FIELD, arbitrary moduli of total degree sigma, and shift, its deterministic minimal-solution-basis theorem costs soft-O(w^(omega-1) sigma) for module rank w when the number of columns is O(w). A rank-two ordinary Padé encoding at modulus T^(D0+1) therefore still has precision/total modulus degree Theta(D0), even with degree-J equation entries. The theorem computes a solution basis, not H M^(-1)b from implicit middle data.

More fundamentally, the obvious ordinary syzygy equation

    -B h+A k=0 mod T^(D0+1)

does not enforce k=h(QT). Its solution module contains the trivial polynomial pair (A,B); returning an ordinary modular basis has not recovered R. The compatible pairs (h,h(QT)) are not a mathcalB[T]-submodule: multiplying both coordinates by T breaks compatibility by the factor Q, since Q-1 is a unit. The q-compatibility must be encoded with its actual diagonal/semilinear constraint, giving (2), or handled by an appropriate proved skew solver. Reducing the ordinary modulus to length m computes a prefix constraint, not the desired remainder modulo Phi_m. This is the concrete missing hypothesis in this attempted approximant-basis application, not a blanket objection to approximant methods.

## Outcome and retained consumer

The new fully initialized object is a band-J, dimension-D0 triangular system with sparse right-hand side, all diagonal units, and the actual two acquired end vectors. Its dense q-logarithmic solve and its gauge inverse factorization are exact. The target is the short sandwich H M^(-1)b or its consumable norm, without acquiring long gauge coefficients. No such short-boundary solver is obtained here. The complete covered query remains the original soft-O(J+sqrt(J ell)) blocked algorithm, with original row, main-block, reciprocal and tail maps; no unproved recurrence endpoint or auxiliary coefficient is passed to the beta consumer. No whole-query or factoring exponent gain, generic lower bound, or numerical campaign is claimed.

## Cached primary pins

`./sources/bostan-chowdhury-lebreton-salvy-schost-2012.pdf`: SHA256 `271c7cec2b2e11772baf9a3ea687678949438f43b1633b088e441a469623440e`.

`./sources/neiger-popov-2016.pdf`: SHA256 `805a10be32f44581faad4e1f6b262e1eea91e18ae4c369af7127bc164a56735f`.

Extracted text is retained beside each cached PDF.
