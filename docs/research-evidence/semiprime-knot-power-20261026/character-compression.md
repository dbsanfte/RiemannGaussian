# Exact character compression trial: CRT carry survives

26 October 2026. Read the latest full-family-wheel.md and its independent review. This pass tests one concrete proposed compression: replace the expanded CRT residue alphabet by Gaussian-period/character data and then take its q-product. The one-prime Fourier formula is valid with an explicit boundary. The multi-prime norm shortcut fails at a specific substitution: reduction of exponent representatives modulo the auxiliary sieve modulus is not valid after evaluating at arithmetic q. Retaining that carry returns an unacquired truncated-knapsack/product contraction. No broad impossibility claim or numerical campaign is made.

## 1. The power-level parameter target

The nonaxis complete catalogue has original mass about kM, M~k^(3/2). To bring its retained mass down to soft(k²), the half-density sieve would need t at least about (log k)/(2 log 2), rather than Theta(log k/loglog k). The first t primes have size Theta(log k loglog k) and their product B has

    log B=Theta(log k loglog k).

Thus B is superpolynomial in k. Even the ideal density 2^-t leaves B/2^t residue classes superpolynomial. The earlier explicit CRT expansion cannot be counted as paid here. Axes retain the separate familiar wheel density, not 2^-t; a successful nonaxis compression would still need its full-family integration checked.

## 2. A lawful single-prime Gaussian formula, including the boundary

For an odd auxiliary prime ell coprime to N, adjoining a formal primitive ell-th root zeta gives an etale cyclotomic algebra of rank ell-1 over R. Let chi be the quadratic character modulo ell, chi(0)=0, and

    G=sum_(s=1)^(ell-1) chi(s) zeta^s,
    S_ell(z)=sum_(r=0)^(ell-1) chi(r) z^r.

The Gauss identity G²=chi(-1)*ell makes G a unit. Exact finite geometric summation gives

    S_ell(z)=(1-z^ell)/G
                *sum_(s=1)^(ell-1) chi(s)/(1-z zeta^s). (1)

For the simple residue-or-zero mask, the allowed-index polynomial is

    A_ell(z)=1/2[(1-z^ell)/(1-z)+S_ell(z)+1].            (2)

Equations (1),(2) are finite rational identities; their removable singularities can instead be kept as the original finite polynomials. At z=q^n with n>0 and 1<=n*ell<min(ord_P(q),ord_Q(q)), all the displayed 1-q^n zeta^s denominators are units because their total norm is a divisor of 1-q^(n*ell), a certified unit. In this restricted range the formula is genuinely legal over the extension. It requires ell summands, however; the quadratic Gauss constant does not supply their weighted rational sum for free.

For the actual mask chi(f_j(r)), additive Fourier coefficients are the corresponding finite quadratic-character sums, rather than the special single Gauss constant. They too can be acquired by enumerating ell residues, as in the existing sieve. This is cheap per prime, but it is not yet a product over the intersection of t masks.

## 3. The explicit CRT product and its nonconstant carry

Let R_ell be one row's acquired allowed set modulo each ell|B. Put

    u_ell=(B/ell)*[(B/ell)^-1 mod ell].

For a residue tuple r=(r_ell), let

    E(r)=sum_(ell|B)u_ell*r_ell,
    R(r)=E(r) mod B in [0,B),
    c(r)=floor(E(r)/B).

The CRT representation is unique and the exact allowed-residue polynomial is

    A_B(z)=sum_r z^R(r).

The inexpensive factorized expression is instead

    product_(ell|B) [sum_(r_ell in R_ell) z^(u_ell*r_ell)]
       =sum_r z^R(r)*(z^B)^c(r).                       (3)

Modulo z^B-1 it equals A_B(z). At z=q^n it contains the row/tuple-dependent factors (q^(nB))^c(r). Arithmetic q is not the auxiliary root zeta_B, so they cannot be replaced by 1. At sufficiently large B no local-order promise even certifies 1-q^(nB) as a unit.

The carry c has a polynomial-size range, at most sum ell, but that does not make (3) a small carry-state computation: selecting its value requires knowing on which interval [cB,(c+1)B) the weighted sum E(r) falls. The fractional part is on the B-point CRT grid. No bounded-state transition for these comparisons is acquired by retaining the integer carry alone.

For a selected cutoff m<B, as occurs at this power-level modulus, the needed alphabet is further truncated to R(r)<=m. Thus the exact missing operation is the finite weighted knapsack contraction

    sum_(r: R(r)<=m) q^(nR(r)),

or its multiplicative q-product analogue. The factorized tuple sums in (3) do not implement that cutoff or remove its carries. This locates the failure in an explicit formula rather than asserting that every compressed sieve is impossible.

## 4. Why the Gaussian-period norm is not the arithmetic product

Cyclotomic period norms compactly organize products such as

    product_(r in R) (X-zeta_B^r).

The desired row factor is instead

    product_(r in R, r<=m) (x-q^r),                     (4)

possibly followed by additional full B-clock blocks. Substituting zeta_B->q is not an algebra map unless q^B=1. Introducing a Bloch algebra T^B=q^B does not repair the alphabet: its spectral roots are q*zeta_B^r, rather than q^r. The resulting norm is a product at the wrong points.

Equivalently, a cyclotomic automorphism r->a*r mod B moves the actual arithmetic point to

    q^([ar]_B)=q^(ar)*(q^B)^(-floor(ar/B)).              (5)

Those same nonconstant carries prevent the quadratic-residue subgroup from acting as the claimed arithmetic Galois symmetry. No rejected leaf has been shown to be a unit, so a quotient of full and rejected products cannot be used to erase them either.

Passing to the multiquadratic fixed field of the auxiliary residue subgroups lowers the *output algebra degree* to at most 2^t. It does not acquire the large cyclotomic relative norm or the cutoff (4). At the target t~(log k)/(2 log 2), even 2^t~sqrt(k) auxiliary coordinates per each of soft(k) rows would need a separately proved shared contraction to fit soft(k). No such contraction is supplied by (1)–(5).

## 5. Finite-product boundary and recovery ledger

If the entire CRT residue list were acquired, its repeated q-clock product could be blocked at B, with all starts and tails as in full-family-wheel.md. Here B>>M, so there is no full B-block at all: the whole original clock interval is a cutoff tail. Treating that tail as zero, or applying a full-period cyclotomic norm and omitting its correction, loses the desired original leaves.

Keeping (3) and (5) formally is safe, but no cost reduction follows until their cutoff/carry contraction is paid. Expanding it returns up to B/2^t states; scanning only the original interval returns the old O(JM) factor support. The initialized old product evaluator is still available at soft(J+sqrt(JM)); the attempted Gaussian-period formula has not improved that bound.

Throughout, an actually retained tuple/index would map to its original row and physical clock index, so the inherited nonzero-annihilator consumer remains usable. The problem is acquiring the retained product, not a missing labeling rule. Rejected indices cannot be inverted as certified units, even when rejection correctly rules out a physical factor witness.

Outcome: the one-prime Fourier step is exact and cheaply initialized. The particular proposed power-level Gaussian/period compression fails at the explicit CRT carry and finite-cutoff operations (3)–(5). This trial supplies no power-level mask contraction, no full-family exponent gain, and no claim against a different compressed-mask algorithm.
