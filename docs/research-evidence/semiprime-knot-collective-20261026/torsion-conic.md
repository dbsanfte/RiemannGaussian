# Native conic rows: explicit Schur/torsion and character-kernel tests

26 October 2026. Bounded constructive pass; scratch only, no numerical campaign or repository edits. **No faster complete query obtained.** Two exact candidate calculations identify the additional collective identity needed, rather than asserting a general topological obstruction.

## 1. Ring and integer-lift distinction

Put H=k², S=H/4, c=lambda/2. The actual congruence forces lambda even, so c is integral, 0<=c<2S, and

    abN-c² is divisible by S,
    E=a+bN+2c.

All statements retain the uncentered lambda. On the prepared branch the local q-orders exceed 16H, so both semiprime factors exceed 16H. For nonaxis rows 0<lambda<H and 0<|a|,|b|<=k; hence a,c,S,2 and beta are units in R=Z/NZ. Axes remain their separately paid part of the original query.

The proposed binary form B=[[a,c],[c,bN]] is rank-deficient modulo the AUXILIARY integer S. It is **not** rank-deficient over R: bN=0 in R and det B=-c² is a unit. Its Schur complement at a is bN-c²/a=-c²/a, also a unit. This does not refute an exponential-weight construction. It shows that plugging B directly into a coefficient-ring surgery determinant cannot identify its auxiliary congruence with the native CRT collision. In particular bN=0 in R does not permit beta^(bN)=1: exponents live modulo the unknown multiplicative orders, not modulo N.

## 2. Execute a unit-pivot two-by-two collision presentation

There IS an exact exponential Schur presentation. For each actual row and original signed clock index i define

    M_(E,i) = [[ beta^(a-Hi), beta^(-c) ],
               [ beta^(-c),   beta^(bN) ]].

Every displayed entry is a unit and is acquired by short-bit powering. Its determinant is

    det M_(E,i)=beta^(-lambda)*(beta^(E-Hi)-1).       (1)

Thus it has exactly the actual leaf's CRT zero predicate. Eliminating the bottom pivot beta^(bN) is always legal and leaves

    beta^(a-Hi)-beta^(-lambda-bN),

which is a unit times the same leaf. This equality is a finite-ring polynomial/determinant identity, not a torsion assertion needing acyclicity at collisions. It never divides by the desired factor. A fixed i with all rows uses block diagonal versions of (1); its determinant retains their product.

The proposed collective surgery compression would identify repeated a- or b-vertices instead of keeping independent row blocks. That is not a determinant-preserving operation supplied by (1). Weighted tree contraction provides a concrete check: independent bridge edges of weights d1,d2 give d1*d2, whereas merging them into parallel alternatives gives d1+d2. At d1=0,d2 a unit the second value is a unit, losing the desired leaf zero. This is an identity-level comparison, not an asserted attained native counterexample. A special native coupling could still work, but must prove the missing correction rather than equate the two graph operations.

Acquiring all matrices (1) over every row and clock costs soft O(Jm). Keeping the existing block polynomial gives the previously paid soft O(J+sqrt(Jm)) scalar algorithm. A dense k-by-k surgery matrix would itself have k² acquired entries and generic determinant cost O(k^omega), both above soft k; a binary twist descriptor or a sparse graph does not by itself pay the determinant. No rank-k determinant is counted as an answer here.

## 3. Keep the rank-one parametrization's actual carry

For the stratum gcd(a,S)=1, let u in [0,S) satisfy c=a*u mod S. Write exact integers

    c=a*u+S*v,    bN=a*u²+S*w.

The second divisibility follows from c²=abN mod S and invertibility of a. Then

    E=a*(1+u)²+S*(w+2v).                            (2)

Writing w+2v=4h+rho with 0<=rho<4 gives

    beta^E=beta^[a*(1+u)²] * beta^(S*rho) * q^h.   (3)

This executes the rank-one-mod-S proposal without dropping its lift. The phase rho and integer h are acquired from the actual row in O(log N)-bit arithmetic, but they vary by row. Replacing the right side with its first term changes the comparison index by h and drops a phase; no common short physical interval follows. Other 2/3-adic strata of a need separate parametrizations; (2) is not claimed to cover them for free. Even on this favorable unit stratum it does not collapse the clock.

## 4. Execute a collective character kernel, and charge its acquisition

One possible way to combine all congruent rows is the exact auxiliary selector

    1_(c²=abN mod S)=(1/S)*sum_(u=0)^(S-1)
                         zeta^[u*(c²-abN)],        (4)

in a finite etale algebra containing a primitive S-th root zeta. This is legal because gcd(S,N)=1; the cyclotomic algebra already has degree phi(S)=Theta(S)=Theta(k²). Formula (4) is additive selection, not an identity for the required PRODUCT of selected comparisons. It must not be mistaken for a zero-preserving product contraction.

The complete a,b kernel at a unit u is Fourier-like: K_(a,b)=zeta^(-u*N*a*b), 0<=a,b<S. Since u*N is invertible modulo S its columns permute a discrete Fourier matrix, so K is invertible over that etale algebra. This does NOT assert full rank for the actual masked hyperbolic catalogue |ab|<k. It says that invoking the complete character kernel supplies S modes, not a free low-rank decomposition of the masked problem. Dense expansion is already too expensive.

The uncentered exponential c-weight also has a fully explicit boundary correction. For 0<=c<S,

    sum_c beta^(2c)*zeta^(-r*c)
       =(1-beta^(2S))/(1-beta²*zeta^(-r)).          (5)

Both numerator and denominator are units in this etale algebra. For the denominator, equality beta²=zeta^r at a residue component would force the order of beta² to divide S, contradicting the native large odd order. The numerator is a nonzero short clock difference, since beta^(2S)=eta. Thus all S Fourier coefficients in (5) survive. Extending c to [0,2S) multiplies by 1+eta, another unit because eta has odd local order. It does not create a sparse Fourier boundary state. No numerical values of these unit products need be acquired for a predicate, but their nonvanishing does not license deleting the weighted selector's modes.

This finite calculation isolates the relevant carry/phase mismatch: the conic condition is periodic modulo S, while beta^(2c) is not. It leaves open a direct fast algorithm on the actual sparse |ab|<k mask, with no full character-cycle expansion.

## 5. Primary splice/Seifert formulas and normalization scope

Cimasoni, [The Conway function of a splice](https://www.unige.ch/math/folks/cimasoni/splice.pdf), Theorem 3.1, printed p.5, gives an exact product of the two component Conway functions after substituting linking-number monomials into their splice variables. It has the stated exceptional case m=0 with all opposite linking numbers zero. Its proof, Lemma 4.2, is torsion gluing over a rational-function field. It does not substitute an auxiliary congruence for exact integer linking data.

Cimasoni, [A geometric construction of the Conway potential function](https://ems.press/content/serial-article-files/43000), printed p.128, expresses the invariant by generalized Seifert determinants with explicit powers of t_i-t_i^-1. Those factors must be retained or shown units after specialization; field torsion does not automatically specialize as a nonzero invariant at target collisions. Conway-to-Alexander conversion also squares variables. No such extra topological realization is assumed in (1)–(5), which are independently cleared algebraic identities.

These results supply exact products and determinants once their full data are given; they give no rule identifying the auxiliary rank-one congruence with a smaller acquired determinant. A graph-link splice product whose factors were the actual beta^(E-Hi)-1 leaves would retain their scalar product; canceling a vanishing factor through a rational presentation would need its own zero-preserving proof.

## Outcome and narrower next constructive interface

The explicit 2-by-2 presentation (1) is collision-safe with unit pivots, but its collective vertex identification needs a new finite identity. The exact rank-one lift (2),(3) retains row-dependent phase/index carries. The complete Fourier realization (4),(5) pays Theta(k²) auxiliary modes and does not establish an identity for the masked product.

A useful next theorem would therefore directly contract the ACTUAL sparse conic incidence mask, together with its integer lifts (3), into a paid soft-k determinant/norm or a smaller coverage family, while retaining the product's CRT zero predicate. It cannot merely give the rank-one factorization modulo S, a dense k-matrix descriptor, or a rational torsion equality with uncensored boundary factors. None of the inspected primary splice/Seifert formulas supplies that theorem. The original signed query and old complete bound are retained; no new preparation or representation is counted as full-query progress.
