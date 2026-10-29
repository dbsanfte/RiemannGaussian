# Section the actual Newton coefficient: a pole-only reduction and an Ore parity test

26 October 2026. Scratch paper execution, no repository edits, tests or emitted h-coefficient arrays. **Positive reduction:** the final E pair can be replaced by TWO simple-pole q-Newton coefficients of 1/(D+delta), with no tau product or unknown cofactor amplitude. An explicit q-Euler conjugation initializes a compact coefficient equation. Two concrete Bostan–Mori-style Graeffe steps have paid short right sides but fail scalar parity closure by a CERTIFIED odd operator coefficient on the actual monic input. This is a scoped executed failure; no general scalar-algorithm lower bound or improved query exponent is claimed.

## 1. Normalize the actual E definition without keeping its long product

Use the authoritative selected-subresultant.md §6: D monic of degree J, a_i=q^i, n=h-1, and exactly one common leaf theta=q^I at the good field in a correct bin. The scalar E_m is tau_(m+1) times the divided difference `[a_0,...,a_m](1/D)`.

Introduce a DIFFERENT formal regularizer on the acquired short polynomial:

    D_delta(X)=D(X)+delta,
    F_m(delta)=[a_0,...,a_m](1/D_delta).

It is not the physical individual-row additive deformation. This distinction is harmless for the following weak locator, proved directly. The universal divided-difference formula is

    F_m(delta)=sum_(i=0)^m 1/[ (D(a_i)+delta)*prod_(0<=l<=m,l!=i)(a_i-a_l) ]. (1)

Every clock difference is a supplied unit. Each term has at most a SIMPLE delta pole at every component, even if D has repeated row roots or several different clock points hit there. Thus every F_m has at most simple poles globally; no good-field-only precision assertion is used.

At the unique good hit let R_m=Res_delta F_m. For m>=I,

    R_m=1/prod_(l<=m,l!=I)(theta-a_l),

and for m<I it is zero. In particular R_n is nonzero, and

    R_(n-1)=(theta-a_n)*R_n,
    theta=a_n+R_(n-1)/R_n.                              (2)

This includes I=n: the numerator is zero and the known final clock node is returned. No final-endpoint inverse or tau norm is needed. Norm-test the ACTUALLY acquired R_n before division; on the good attempt it is proper-factor-or-unit. The short H_u(theta)/D'(theta) tag evaluation has its separate good-unit gate. Wrong bins are bounded attempts and cannot suppress later ones.

Equation (2) is projectively compatible with the final E locator but asks for different numeric quantities. It does not claim equality of R_m to E_m in B. It eliminates their long tau normalization from the requested OUTPUT, not from all possible algorithms' work.

## 2. Execute geometric Newton-to-coefficient conversion

Write (q;q)_m=prod_(r=1)^m(1-q^r). Exact expansion of the divided-difference denominators gives

    F_m=q^(-m(m-1)/2)*[z^m]( A(z)*B(z) ),               (3)
    A(z)=sum_(i<h) (-1)^i*z^i/[(D_delta(q^i))*(q;q)_i],
    B(z)=sum_(i<h) q^(i(i-1)/2)*z^i/(q;q)_i.

All series are truncated modulo z^h. We do NOT assume the infinitely many q-factorials are invertible at a finite-order native q. The finite coefficients used here have indices<h<16H, so their denominators really are units.

Let C=A*B mod z^h. Then C_m=q^(m(m-1)/2)F_m, and the desired weak locator is

    theta=q^n+q^(n-1)*Res C_(n-1)/Res C_n.              (4)

The power q^(n-1) is essential. The denominator residue is nonzero at the good field. Coefficient sectioning now targets two ordinary coefficients of C, not an unexplained generating function for E.

### Actual initialized operator input

Let S act by f(z)->f(qz). The truncated q-Euler identities are B(qz)=B(z)/(1+z) and

    D_delta(S)A=B^-1 mod z^h.

Since B has constant term one, its inverse is legal as a truncated power series. Conjugating gives the compact exact equation

    D_delta(L) C=1 mod z^h,
    L=(1+z)S,   S*z=q*z*S.                             (5)

This needs only the supplied O(J) coefficients of D_delta and the fixed generator L. Its expanded normal form could have quadratically many coefficients; none is silently declared acquired.

Acquire the actual first O(J) values D(q^i) by geometric MPE. A nonunit point value can be localized to an ORIGINAL row difference T_j-q^i and sent to the paid native mixed-relation decoder, or the known factor/tag branch. Otherwise these values are global units; their fixed-precision D_delta inverses and (q;q)_i factors give a genuine O(J)-coefficient prefix of A and C by one convolution, in soft J. No arbitrary initial-condition oracle is used. If h=O(J), the old shared query already fits soft J, so focus on the long-clock case.

The supplied scalar E recurrence clears such denominator inverses polynomially. Equation (5) instead lives first as a rational-parameter identity before componentwise Laurent specialization. A proposed execution must handle its singular D(q^I)+delta honestly; constant precision through every unclassified division is NOT assumed.

## 3. First executed Graeffe candidate: reflect the operator variable

Normalize ordinary polynomial Graeffe by (-1)^J*D_delta(X)D_delta(-X)=R_delta(X²), with R_delta monic of degree J. R_delta is acquired by one polynomial multiplication in soft J. Left-multiply (5):

    R_delta(L²) C=(-1)^J*D_delta(-L)1.                         (6)

The right side is the acquired degree-J polynomial

    sum_(r=0)^J d_r(delta)*(-1)^(J+r)*prod_(t=0)^(r-1)(1+q^t z).

Fast geometric Newton conversion acquires its coefficients in soft J; all needed node differences have gaps<=J and are screened. Thus this attempt does not fail merely because its transformed input is unavailable.

However

    L²=(1+z)(1+qz)*S²

does NOT preserve even and odd z powers. The highest q-shift term of R_delta(L²) is L^(2J), since R_delta is monic. Its coefficient of z*S^(2J) is

    sum_(t=0)^(2J-1)q^t=(1-q^(2J))/(1-q),               (7)

a GLOBAL UNIT on the actual supplied q. Lower powers of L cannot cancel that highest-shift coefficient. Thus the ordinary scalar even-denominator invariant needed by Bostan–Mori does not arise in this Newton-conjugated Graeffe step.

This is an actual-input operator calculation, independent of lower D coefficients or a genericity assumption. It is not a claim that every structured section algorithm must expand that operator or has large complexity.

## 4. Second executed candidate: reflect z as in Bostan–Mori

Parity reflection conjugates L_+=(1+z)S to L_-=(1-z)S. Left multiplication yields

    D_delta(L_-)*D_delta(L_+) C=D_delta(L_-)1.           (8)

Again the right side is a paid degree-J q-Newton polynomial. But the two operator factors do not commute. At q-shift order 2J, their coefficient is

    prod_(t=0)^(J-1)(1-q^t z)
    *prod_(t=J)^(2J-1)(1+q^t z).

Its linear z coefficient is

    -(1-q^J)²/(1-q),                                  (9)

also a GLOBAL UNIT. Thus this second concrete denominator product is not parity-even either. For J=1 this is the explicit commutator effect L_+L_- - L_-L_+=2(1-q)z*S², but (9) proves the mismatch for the ACTUAL growing monic J as well; it is not based only on a small toy degree.

For h>4J+1 the odd normal-form coefficient also represents a genuine cross-parity action on the truncated coefficient space: its polynomial in S has degree 2J and unit leading coefficient. It cannot vanish at every one of q^0,q²,...,q^(4J), whose Vandermonde differences are certified units. If h<=4J+1 the old bound soft(J+sqrt(Jh)) is already soft J, so this long-clock restriction costs no unresolved case.

The exact coupled section state remains small at the generator level. With u=z² and C=C_even(u)+z*C_odd(u),

    L = [[1,q*u],[1,q]] * S_(q²).                     (10)

Both off-diagonal entries are actual nonzero operators. Equation D_delta(L)C=1 becomes a two-component q²-system with the same short polynomial D. This is a valid retained compact input. An algorithm exploiting repeated sections of (10) without emitting growing coefficients could still work; none is ruled out by (7)–(9).

Whole-bin uniqueness does not make one coefficient section identically regular. At the good unique hit, Res F_m is nonzero for EVERY m>=I, by (1), and multiplication by q^(m(m-1)/2) preserves this. Thus both parities carry the pole once the index passes I, except the trivial last-endpoint case already included in (2). This is a source-specific statement about the actual Newton coefficients, not a general 'two branches imply a lower bound' argument.

## 5. Completed cost and exact next handoff

The original final E scalar pair was initialized in soft J but its direct recurrence costs soft Jh. The new reciprocal-Newton pole pair (4) removes tau amplitudes from the desired output and initializes (5) in soft J. Each first Graeffe/reflection transformation above has a paid short right side and degree-J compact denominator data. They do not produce a scalar constant-degree parity iteration to which the ordinary O(M(J)log h) Bostan–Mori theorem can be applied.

A completed exact fallback remains the inherited shared q-factorial/first-variation engine at soft(J+sqrt(Jh)). With the optional paid global row-separation gate, clock-pole residues in (1) can be assembled from the acquired row flags and W_h'(T_j)^{-1}; the coefficient at n-1 is (T_j-q^n) times the coefficient at n. No clock index I is needed. All relevant clock derivatives are units on flagged rows, and the gate either factors or licenses them. Without demanding exact equality at other components, the same sums are already admissible weak projective outputs from the unique good hit; exact repeated-clock counting must not be silently identified with that weaker interface.

No h coefficients were materialized in this investigation. Emitting the full A prefix or all D(q^i) values would itself cost soft h=K^(3/2) in that straightforward implementation, worse than the retained K^(5/4) route. Neither form is counted as a shortcut.

The precise new coefficient-algorithm opportunity is to section the compact matrix generator (10), or another conjugation of (5), while acquiring ONLY the last two negative Laurent coefficients and retaining the singular row at its unknown clock position. The failed scalar invariants (7) and (9) do not prove that such a coupled algorithm is impossible.

## Primary source contracts and old credit

Bostan–Mori, *A Simple and Fast Algorithm for Computing the N-th Term of a Linearly Recurrent Sequence*, primary SIAM paper PDF https://mathexp.eu/bostan/publications/BoMo21.pdf , supplies the commutative rational-series even/odd algorithm and its arithmetic bound; it does not supply (6) or (8) as a q-Ore extension. Bostan–Schost, *Polynomial evaluation and interpolation on special sets of points*, primary PDF https://cs.uwaterloo.ca/~eschost/publications/BostanSchost.pdf , supplies fast geometric Newton conversion. Native application uses certified unit differences rather than assuming a field equality oracle. Equations (1)–(10) above are derived finite identities, not claimed theorems imported from those papers.

The frozen sectioned-q-binomial/Cauchy action and raw norm parity audits retain their credit. This calculation starts instead from the actual E divided difference, isolates a pole-only two-coefficient output, and tests the SPECIFIC Newton-conjugated operator's parity invariants. It establishes no new sixth-rate factoring theorem or general complexity lower bound.
