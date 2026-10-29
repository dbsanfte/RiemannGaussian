# Native conic finite-product contraction: quadratic-phase and Fourier execution

26 October 2026. Read the final AGENTS sections, current Adams packet and prior finite-descendant/root-system audits. Primary search focused on finite q-binomial/quadratic transformations rather than repeating generic q-holonomicity. Scratch only; no numerical/coverage campaign or repository edits.

**Outcome.** No improved whole-query bound is established. This pass executes the concrete proposal to use the ACTUAL conic catalogue as a finite quadratic/Gaussian index set for a Habiro/q-hypergeometric contraction. It gives an exact sparse quadratic-phase/carry normal form, pays its initialization, performs its legitimate finite interlacing, and tests the proposed small Fourier-state explanation on an actual native primitive pair. That pair has all auxiliary Fourier modes nonzero and indeed unit, so the straightforward full spectral transform costs rank Theta(k²), above the budget. This excludes that particular expansion strategy, not compressed conic algorithms in general. The precise remaining arithmetic target is stated in Section 6.

## 1. What is already available, and what a new identity must change

Use the scalar native setup k=2*3^e, H=k², q=beta^H, eta=beta^(H/2), large odd local beta orders and local q orders>16H. The acquired labels are

    E=a+bN+lambda, 0<|ab|<k,
    0<=lambda<H, lambda²=4abN modH,

plus the four axes, with original whole-row deletion and signed recovery metadata. Complete-swap bookkeeping permits representatives |b|<=|a|, hence |b|<sqrt k for nonaxis pairs. It must retain the original labels for the other orientation and decoder. Nonaxis lambda cosets are not broken by the public integer-zero deletion, as proved in the prior native-family-sharing report.

For the negative-only query it suffices to acquire the zero/nonunit bit of

    product_(rows j) product_(i=1)^m (beta^E_j-q^-i),
    m=Theta(k^(3/2)), J=soft O(k).

Every selected nonunit or saturated true leaf has the old nonzero short E_j+Hi gap. Current soft(J+sqrt(Jm)) remains the paid complete evaluator. The new Frobenius/order and shared-root preparation does not shorten this rectangle; its exact common-base fallback is already archived. This report does not repackage that fallback as a new recurrence.

## 2. Exact native quadratic phase, with the correct moduli and carry

Focus first on the actual large stratum 3 not dividing b. Put

    S=H/4=3^(2e), lambda=2mu, 0<=mu<2S.

Since lambda is even, the conic is exactly

    mu² = abN mod S.                                  (1)

Let c_b be the acquired least positive inverse of bN modulo S. Define the allowed a-band

    A_b={a in Z: 0<|ab|<k, |a|>=|b|},

with the relevant original representative/pruning metadata. Because S=k²/4>2k on the hard k>16 branch, there is AT MOST ONE a in this band in a given residue class modulo S. Thus for a phase mu, either there is no row, or a_b(mu) is its unique signed lift of c_b mu² modulo S into that band. The exact set I_b of successful phases is acquired by the existing root enumeration in soft(k/|b|) output-scale work, rather than scanning all 2S phases.

The integer

    tau_b(mu)=(c_b mu²-a_b(mu))/S

is explicit for every acquired row. The native exponent is exactly

    E=bN+c_b mu²+2mu-S*tau_b(mu).                    (2)

Let rho=beta^S, so rho²=eta and rho⁴=q. The clock-normalized row query is therefore, up to a known unit beta^(mE),

    (beta^(-bN-c_b mu²-2mu)*rho^tau_b(mu)*q^-1;q^-1)_m.
                                                               (3)

All starts, carries and coefficients in (2),(3) are acquired in soft J total work on the supplied sparse catalogue. Integer exponents have O(log N) bits under the native scale, even though their separately lifted quadratic pieces are much larger than the original short phase range. No discrete logarithm or hidden root is used.

This is a genuinely quadratic exponent, not the linear balancing relation of a basic hypergeometric summation. Writing tau=4d+r, 0<=r<4, gives rho^tau=q^d rho^r. Omitting d translates the physical finite interval by a row-dependent d. That loses the original zero window and its short-label consumer. The conic congruence does NOT imply beta^(mu²-abN)=1 or rho^tau=1. These are exact acquired carries, not auxiliary roots of unity.

The ramified 3|b strata have their previous valuation/root-coset descriptions; this report does not silently infer their coverage or a new transform from (1). A successful full-family algorithm must include them and the independently handled axes. The unit-b stratum alone already exposes the obstruction in the tested Fourier transform below.

## 3. Execute the finite product contraction that is actually licensed

Phases mu and mu+S have the SAME a_b value and both are supplied. Their original exponents differ by exactly 2S, so their two q^-1-factorial starts differ by eta^-1. Set x=beta^(-E(mu))*q^-1. Then the finite identity

    (x;eta^-2)_m (x*eta^-1;eta^-2)_m
       =(x;eta^-1)_(2m)                              (4)

is exact: it interlaces the even and odd exponents. There is no denominator, analytic convergence or auxiliary root. Nonaxis public deletion leaves this pair intact. Normalization differences between the actual root differences and (4) are powers of supplied units, acquired with the row labels.

This phase-coset tiling/interlacing is PRIOR credit, not a new theorem. Its exact execution here tests whether the quadratic parametrization secretly gives a shorter clock. It halves the phase alphabet and doubles the clock; degree times clock mass changes by a constant factor only. Repeating the known smooth-content coset tilings gives the same previously paid tradeoff, not a new exponent. Pairing reciprocal directions adds a finite Habiro/Newton kernel but does not change that conclusion.

The remaining proposed gain would have to contract the product of (3) across the SPARSE low-a phases jointly across b. Applying a separate soft(J_b+sqrt m) oracle to each b would already cost up to sqrt(k)*sqrt(m)=k^(5/4) for its startup terms; it would not attain soft k even if each b-subproblem were individually improved. A useful algorithm must share that work across b, or supply a genuinely smaller proved cover.

## 4. Test the proposed quadratic-Gauss / small Fourier state

The obvious Gaussian plan is to encode (1) using an auxiliary S-th root of unity, apply finite q-binomial/quadratic transformations, and hope the native root indicator occupies only a small number of character modes. That last assertion can be tested EXACTLY on an actual native pair, without a sample.

For every native N coprime to3, take b=1 and a=7 if N=1 mod3, or a=5 if N=2 mod3. Then aN=1 mod3, 0<ab<k on the hard k>16 branch, gcd(a,b)=1 and a!=+/-b. This actual primitive pair avoids both diagonal and antidiagonal pruning, and satisfies |b|<=|a|. It is nonaxis, so the public integer-zero deletion cannot remove its labels: |E|>=N-H-k>HM on the prepared branch, as proved in the prior deletion-and-grouping audit. Complete-swap bookkeeping retains the corresponding actual representative and metadata. Since aN is a square unit modulo3, Hensel lifting gives exactly two roots +/-r modulo S, with r a unit. Its mu indicator on Z/S is precisely those two residues. (The two lifts to [0,2S) were handled by (4).) Actual opposite folding only pairs the corresponding orientations by a constant factor; it does not justify a sparse character support assertion for this phase mask.

Adjoin an auxiliary primitive S-th root zeta in an etale cyclotomic algebra; 3 and hence S are units modulo N. Its additive Fourier numerator at frequency t is

    hat I(t)=zeta^(t r)+zeta^(-t r).                 (5)

This is a UNIT at every frequency t, including t=0. Indeed z=zeta^(2tr) satisfies z^S=1 with S odd, and

    (1+z)*(1-z+z²-...+z^(S-1))=1+z^S=2.

Since 2 and zeta are units, 1+z and (5) are units. Thus there is no spectral support truncation at all. On a faithful auxiliary S-cycle Fourier representation every one of its S character modes is present. A complete cyclic basis has rank S=Theta(k²); even the primitive cyclotomic part has rank phi(S)=2S/3. Acquiring that whole expansion exceeds soft k.

This is a narrow failure of the proposed FULL Fourier/Gaussian expansion, not a lower bound on sparse Fourier algorithms, compressed character descriptions, native coverage or general q-difference algorithms. The original two-phase input itself is small and is easy to query in soft sqrt m; its dense transform would be an unnecessary expansion. The calculation shows specifically that quadratic-congruence input does not justify the desired small Fourier-state assumption. Combining many such pair indicators can have cancellations, but the nonlinear product contraction would then need a proved joint identity; it does not follow from one Gauss constant or from the conic equation.

No original target is identified with an auxiliary zeta^t. The arithmetic rho and q have large odd local orders and satisfy rho⁴=q, not rho^S=1. Substituting arithmetic beta for zeta would invalidate the transform's period, as in the prior carry audits.

## 5. Primary finite-summation and telescoping sources inspected

The relevant primary finite identities contain useful quadratic phases, but not the required sparse PRODUCT contraction:

* Berkovich–Warnaar, *Positivity preserving transformations for q-binomial coefficients*, Transactions AMS357 (2005),2291–2351; inspected arXiv:math/0302320v1,26 February2003, finite transformations and their iterates: https://arxiv.org/abs/math/0302320 . Their transformations act on weighted finite SUMS with specified q-binomial coefficients, contiguous/parity index ranges and retained finite parameters. Quadratic summand exponents do not alone turn the product (3) over I_b into one such sum. A specialization must supply its entire weight and endpoint data; the native low-a indicator and carries above are not those data. Primary PDF search also surfaced the authors' displayed finite Jacobi/bounded Euler and Rogers–Ramanujan transformations; none was used as a theorem evaluating this native norm.
* Warnaar, *q-Trinomial identities*, Journal of Mathematical Physics40 (1999),2514–2530, author PDF received10 November1998/accepted8 December1998, illustrates the same distinction; the specific primary PDF inspected is https://people.smp.uq.edu.au/OleWarnaar/pubs/qTrinomials.pdf . Its finite quadratic sums retain q-binomial/trinomial boundary coefficients. No quotient by a possibly zero endpoint is imported into R.
* Chen–Singer, *Residues and telescopers for rational functions*, Advances Applied Mathematics (2012), https://arxiv.org/abs/1203.4200 and author PDF https://singer.math.ncsu.edu/papers/YAAMA1465.pdf . Its rational q-summability criteria assume characteristic zero and a non-root-of-unity q. They do not automatically provide a multiplicative norm evaluator or a finite-ring recurrence. In particular a telescoper with a finite support cut leaves its explicit boundary terms; no scalar initial value is acquired merely by existence of a rational certificate.

The source role here is deliberately limited. The direct identities (1)–(5) are proved above over the actual arithmetic ring where stated. No characteristic-zero theorem is used to license inverses of a native collision factor, a fixed-order versus growing-order shortcut, or an unproved modular specialization. Earlier Habiro finite-descendant, q-Racah terminal, and finite-root-system reports remain authoritative and are not repeated as new findings.

## 6. Precise new arithmetic target and complete costs

One concrete sufficient primitive now has a fully initialized native coefficient interface. Given the sparse acquired set of triples

    (b,mu,a_b(mu)), with a_b(mu)=c_b mu² modS

in their original signed low-product bands, contract the product (3) with its exact tau_b(mu), jointly across b, in soft(J+sqrt m). It must tolerate all original zero factors and return a restriction-stable zero/nonunit bit or an actual original label/index. Its input acquisition is already soft J; a dense S-phase or S-character expansion is not supplied. For ramified strata the analogous scaled valuation data and the finite axis tiles must remain attached rather than dropped. An improvement restricted to one primitive pair is a diagnostic, not a complete native algorithm.

The positive normal form exposes two correlated variables a small row family might exploit: the same inverse slope c_b=(bN)^-1 modS and a low-a quadratic cutoff. The promising missing arithmetic is therefore a CARRY-AWARE SPARSE QUADRATIC-MASK q-product contraction across those inverse slopes, rather than a generic degree-J norm or a newly asserted Jones recurrence. The exact interlacing (4) and complete character calculation (5) test the two immediate finite-summation shortcuts and leave that shared primitive unpaid.

If a method actually returns a nonunit original factor, use the existing gcd/localization and short nonzero E+Hi consumer. If it returns only an auxiliary Fourier or Gaussian scalar zero, no original-leaf decoder is licensed without a new identity. All existing acquired data can still feed the common-base evaluator at soft(J+sqrt(Jm)); no coefficient enumeration, finite transformed sum, full character table or nominal constant-order recurrence inspected here improves that bound. The sixth-exponent goal remains open.
