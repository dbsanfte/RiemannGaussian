# Polylogarithmic nonresidue menus remove the long-annihilator scan penalty

2026-10-16. This is a constructive extension conditional on accepting the cited primary zero-free theorem as an imported theorem. No new proof audit of that theorem, Lean declaration, or annihilator acquisition is claimed.

## Result

Assume N=P Q, distinct odd primes, N<=m^6, m=Theta(N^(1/6)), B=16m^2. A given unit gamma has odd local orders greater than B, and a supplied nonzero integer K satisfies gamma^K=1 mod N. Let L be its explicit binary length, now allowed to grow beyond polylog N.

Using the existing universal monic separator, a uniform polylogarithmic quadratic-nonresidue theorem gives deterministic factoring cost

  soft O(L + N^(1/12)).

Thus L=soft O(m) is sufficient for soft O(m) recovery. No multiplication of L by a positive power of N remains. This does not acquire K.

## Primary analytic statement

OpenAI/math primitive-roots paper, Theorem 1.2, states that every finite-order Hecke L-function of every cyclotomic F containing mu_12 has no zeros in Re s>1-10^-6, with no conductor/height cutoff. Constants in its moment proof may depend on the fixed field and character, but the final excluded region is uniform. Its Section 9 gives a smooth explicit-formula argument with uniform error x^(1-delta)(log D+n).

For fixed F=Q(zeta_12), pullback of a Dirichlet character chi along norm has L-function equal, up to Euler factors having zeros only on Re s=0, to the product of L(s,chi psi) over the four characters psi of Gal(F/Q). Thus the theorem implies the same zero-free strip for all Dirichlet L-functions. There are no cancelling poles away from s=1; at s=1 nonprincipal Dirichlet nonvanishing handles the possible principal-factor pole separately.

For a primitive nonprincipal quadratic character of conductor q, the usual smoothed explicit formula then gives a prime with chi(ell)=-1 below C(log(2q))^(2,000,000), with an absolute effectively obtainable constant C. The deliberately loose exponent 2/delta follows by comparing the x main term with O(x^(1-delta)log(2q)), prime-power errors, and ramified-prime contributions. One can sharpen it, but no GRH-strength log-squared claim follows.

The stronger pinned primary QRH paper states in Theorem 1.1 that all Dirichlet L-functions are zero-free in Re s>7/8. Corollary 1.2 explicitly supplies n(p)<=C(log p)^32 for prime p, and deterministic polynomial-log square roots over a KNOWN prime field. The same exponent 32 suffices for every primitive nonprincipal quadratic character, including Jacobi chi_N: use a nonnegative smooth weight supported on [1,2], contour at 15/16, and the uniform zero count. The weighted prime sum for chi has error O(x^(15/16)log(2q)); compare to the principal main term. Taking x=(C log(2q))^32 makes the error smaller than the main term for an absolute C, with prime powers and ramified primes also absorbed. This is a short additional Dirichlet explicit-formula corollary, not literally the prime-only statement of Corollary 1.2.

Primary pinned QRH URL:
https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf
Primitive-roots source:
https://github.com/openai/math/blob/main/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf

## Algorithm without knowledge of analytic constants

Strip K to positive odd part K0. Enumerate the same public dyadic X bins B/2<=X<=sqrt N as in the existing unbalanced extractor, cap M_X=ceil(2X/B). For a=1,2,3,..., do the following round for ALL bins:

1. Compute gcd(a,N), returning a proper factor if found; skip nonunits.
2. Compute b=a^K0 mod N ONCE for this a, shared by every bin.
3. Run the universal separator on b in every bin, returning any proper factor. Continue after NoHit or exact-common-order outputs.

All stopping tests are algebraic, so neither the unknown constant C nor hidden-prime Legendre tests are algorithm inputs. No auxiliary primes need to be acquired: the menu consists of successive integer bases.

## Coverage

For the correct bin X<=P<2X with P<Q, ord_P(b) divides (P-1)/ord_P(gamma)<2X/B<=M_X for every a. Thus its separator cannot return NoHit. It returns a proper factor whenever b has unequal local orders.

Let s_P=v2(P-1), s_Q=v2(Q-1). Odd powering preserves local 2-primary order.

If s_P=s_Q, a Jacobi-minus-one base has opposite Legendre signs and hence unequal local 2-primary orders. The uniform quadratic-character bound for conductor N supplies one among a<=C(log(2N))^32.

If the valuations differ, take the prime ell_* with larger valuation. A Legendre nonresidue at ell_* has local 2-primary order 2^s_ell*, strictly exceeding the other prime's maximum. The prime-field bound supplies such an integer a<=C(log(2ell_*))^32<=C(log(2N))^32. It need not be identified as a nonresidue by the algorithm: the separator detects the resulting unequal local orders.

Consequently the round-robin algorithm always stops by a polylogarithmic base index, with all wrong-bin outputs harmless. This avoids any unknown-threshold finite trial-division fallback.

## Charge

Each round reads/powers the L-bit exponent once, in soft O(L+1) bit work since modular multiplications cost polylog N. There are O(log N) bins. Their maximum separator cost is

 soft O(sqrt(sqrt(N)/B)+1)=soft O(N^(1/12)).

Polylogarithmically many rounds give soft O(L+N^(1/12)). Computing K0 and all cutoffs, gcds, metadata, and base enumeration fit this bound. This is asymptotic polylogarithmic overhead, not a practical recommendation to scan log^32 N bases.

## Exact limit

The supplied K annihilates gamma's high odd local subgroups, not necessarily the full groups F_P^*,F_Q^*. Therefore one cannot simply use K as a Miller exponent for arbitrary bases and claim soft O(L+polylog N). The small-index separator still costs N^(1/12) in the present proof. When L=soft O(m), both terms fit the target budget and this distinction does not weaken the intended long-K application.

Over a known auxiliary prime r~N^(1/18), quadratic root extraction is already affordable by an O(r) scan; the new theorem is not needed there. General deterministic polynomial factoring does not follow merely from having quadratic nonresidues, and its algorithms require a known prime modulus. No such routine supplies P, Q, or the missing catalog.

## Explicit proof of the composite Jacobi menu (no extra hypothesis)

Here is a direct derivation from QRH Theorem 1.1, rather than an appeal to its prime-only Corollary 1.2. Let chi be any primitive nonprincipal real quadratic character of conductor q>=3. The functional equation and the uniform zero-free half-plane put every nontrivial zero in 1/8<=Re rho<=7/8. Define

  W_chi(x)=sum_{n<=x} Lambda(n) chi(n) (1-n/x)^2.

The Mellin transform of (1-t)^2 on 0<t<1 is 2/[s(s+1)(s+2)]. Perron/Mellin inversion and a contour shift give

  W_chi(x)=-sum_rho 2 x^rho/[rho(rho+1)(rho+2)] + O(log(2q) log(2x)).

The analogous formula for the zeta character has main term x/3. The constants are absolute and effective. To see their uniformity, use the functional equation on the fixed left line, the standard zero count in unit height intervals O(log(q(2+|T|))), and the fact that the zero denominators stay a fixed distance from 0,-1,-2. The trivial-zero/zero-at-zero residues and fixed-line integral contribute the displayed logarithmic error; allowing log(2q)log(2x) is conservative. Absolute convergence of the zero sum follows from its cubic height denominator. Therefore

  W_chi(x)=O(x^(7/8) log(2q)+log(2q)log(2x)),
  W_zeta(x)=x/3+O(x^(7/8)+log(2x)).

Suppose no prime ell<=x has chi(ell)=-1. At every unramified prime chi(ell)=1, hence every prime-power term agrees between W_zeta and W_chi. The only difference comes from ell|q, and

  0<=W_zeta(x)-W_chi(x)
    <=sum_{ell|q} sum_{k:ell^k<=x} log ell
    <=omega(q) log x
    <=log(q)log(x)/log 2.

On the other hand the explicit formulas make this difference

  x/3 + O(x^(7/8)log(2q)+log(2q)log(2x)).

Take x=C(log(2q))^16. The ratio of the power-error to x is O(C^(-1/8)/log(2q)); the logarithmic errors are smaller. Choosing one sufficiently large absolute effective C makes the difference exceed x/6 while its ramified upper bound is below x/6, a contradiction. Thus a nonresidue PRIME exists below C(log(2q))^16. In particular the common exponent 32 used by the algorithm is valid after increasing C.

This proves the required menu for chi_N as well as prime Legendre characters. For distinct odd P,Q, chi_N=(./P)(./Q) is primitive of conductor N and nonprincipal (CRT supplies a residue with either prescribed sign), irrespective of N mod 4. The algorithm scans integers, so it does not need primality tests or to identify which hidden Legendre character witnesses coverage.

For the weaker primitive-roots strip delta=10^-6, reflection puts beta>=delta; the same convergent zero-sum proof has constants depending only on this fixed delta. Replacing exponent 16 by 2/delta=2,000,000 gives the stated common polylogarithmic menu.

## Frozen evidence

Both primary PDFs and pdftotext outputs are copied beside this report. primary-source-pins.json records source commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, file byte counts and SHA256 values. The primitive-roots main-branch PDF was checked against the GitHub path-history endpoint, whose latest modifying commit is that same SHA. QRH was downloaded directly from the pinned raw URL. No repository files were modified.
