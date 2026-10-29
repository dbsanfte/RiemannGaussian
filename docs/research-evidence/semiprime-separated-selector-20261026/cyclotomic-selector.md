# Cyclotomic row selection with a paid growing extension

26 October 2026. Paper-only candidate execution, scratch only. Retuned unique bank: K'=Theta(K^(2/3)), J=O(K'), h=O(K²); preparation, orders, short-label recovery and budget still use ORIGINAL K. No factor-field Frobenius, modular square root or order oracle is supplied.

**Outcome:** a concrete cheap cyclotomic certificate can supply a TWO-TAG factor palette on a publicly identifiable high-3-adic branch; the sharper existing restricted-HH consumer then factors in soft K. It is a conditional success gate, not a universally supplied selector. The growing-extension construction itself is old paid credit: its exact finite identity retains an unknown complementary exponent. Paying rank J does not remove that term.

## 1. Primary source and prior credit

Primary source inspected: René Schoof, *Four primality testing algorithms*, arXiv0801.3840, §§3, Proposition3.1, Theorem3.2, Proposition3.3(i), PDF pages10–14. Author publication: https://www.mat.uniroma2.it/~schoof/05rene.pdf ; inspected arXiv PDF: https://arxiv.org/pdf/0801.3840 . Proposition3.3(i) certifies a 3-adic relation p²=N^(2lambda_p) for every prime p|N if a cubic-power Gauss congruence is a primitive root. The relation is a consequence of a CHECKED congruence, not a free property of composite N.

The packed Gauss-power algorithm and unknown-Frobenius identity were already acquired/audited in the project journal, lines32100–32241 (22 October). They must not be counted as new extension acquisition. The wild nested-conductor failure there also applies: additive and character roots sharing a 3-power conductor cannot be assigned independent Galois actions.

## 2. An actual finite certificate: auxiliary modulus7

Let R0=Z/NZ. Test gcd(N,21) first; a proper gcd factors, and the prepared branch has gcd(N,3)=1. In the rank12 monic algebra

    A=R0[z,t]/(Phi_7(z),t²+t+1)

take a primitive root3 modulo7 and define chi(3^k)=t^k. Acquire

    tau=-sum_(x=1)^6 chi(x) z^x.

Complex conjugation sends z to z^-1 and t to t^-1; the primitive Gauss identity tau*conj(tau)=7 explicitly licenses tau^-1=conj(tau)/7. The ONLY coefficient inverse is 7^-1, certified by the initial gcd. Define sigma_N(z)=z, sigma_N(t)=t^N, and compute by binary powering

    gamma=sigma_N(tau)*(tau^-1)^N.                 (1)

This is exactly tau^(sigma_N-N). No map x->x^p at an unknown prime is evaluated. Rank is fixed, exponent bitlength O(log N), and all quotient reductions use monic polynomials, so the entire acquisition is polylogarithmic bit work.

For k=1,2 compute the gcd of N with ALL twelve coefficients of gamma-t^k. A proper gcd factors. Gcd N certifies the exact GLOBAL identity gamma=t^k. Otherwise decline this candidate: do not turn a failed primality congruence into a factor or a residue. Both primitive identities cannot hold globally since t-t² is a unit when gcd(N,3)=1. Individual coefficient gcds may additionally factor but are unnecessary to the validity of this gate.

On a global pass, the source proposition applies with l=3, r=3, q_aux=7, proving p²=N^(2lambda_p) in Z_3 for EACH prime divisor p. All its inputs have been checked in the actual composite-ring algebra.

## 3. Convert the certificate into useful acquired information

Acquire t0=v3(N²-1) by exact integer divisions and set

    n=3^min(t0,e), n|K.

The checked 3-adic identity implies p²=1 modulo n, hence p=+1 or -1 modulo n. This last step is an ordinary root classification modulo an odd prime power, not an invoked modular-square-root oracle. Thus a successful gate supplies the explicit palette {1,n-1}, covering the smaller factor P (indeed both factors). Deduplicate if necessary.

This is useful at n=Omega(K^(1/3)), not only at the older sqrt(K) modulus. Here is the ACTUAL sharper consumer ledger, checked against axis-supplier/review-restricted-residue.md and HH Proposition3.3/Algorithm4.3 (https://arxiv.org/html/2105.11105): for S candidates the initialized restricted giant/baby work is

    soft(S*r + sqrt(N)/(nr)^(3/2) + S + 1).

Set A0=ceil(cuberoot(K^4)) and r=ceil(16A0/n). With S≤2 and n=Omega(K^(1/3)), Sr=O(K), nr≥16K^(4/3), and

    lambda=ceil(4sqrt(N)/(nr)^(3/2))≤ceil(K/16),
    kappa=2lambda+1≤K/8+3<K.

All starts, lattice labels and exponents have O(log N) bits. The baby base beta^(n²) has local orders at least those of beta^H because n²|H. Therefore no new order preparation is needed. The source exact-recovery/global-match procedure handles a=0 or b=0 and literal-zero matches before deletion; it has no unlicensed annihilator step. It returns a verified factor in soft K under the acquired palette promise. This bound does not require T_ext.

For an entirely explicit public success branch require n≥ceil(cuberoot(K)); fixed constants in that test affect only the Sr constant. If the congruence gate fails, or n is too small, use the existing fallback. This is a factor-or-conditional-palette supplier, NOT a theorem that all prepared N reach the HH branch. The supplied scalar/torus orders are odd and 3-rough; that removes their 3-parts and does not impose a useful lower bound on t0. No claim that the current preparation excludes or forces this high-t0 branch is made.

Filtering the retuned bank by these residues alone would leave O(K'/n) colours and an O(K²) clock; that does not itself establish soft K. The useful composition here is the paid restricted-HH consumer, not a falsely free row selection.

## 4. Execute the proposed growing-extension alternative

Suppose a public auxiliary prime ell≤K and a character order d|ell-1 with d=O(K') are supplied or found by the public bounded sieve. Build the public logarithm table modulo ell and the Jacobi histograms. The ALREADY PAID packed algorithm acquires in R0[X]/(X^d-1) a coefficient vector C_N representing

    G(chi)^N=C_N(chi)G(chi^N)

for all character components. Its work is soft(ell+d) for O(log N)-bit exponents, including the trivial-character projector corrections. It uses neither rank d copies of the additive extension nor unknown prime-field logarithms. Finding ell in a PRESCRIBED progression with ell≤K is not automatic; an unsuccessful bounded search declines. Jacobi arithmetic can avoid materializing the rank d(ell-1) additive/character tensor algebra, whose naive size would exceed the proposed budget.

At P|N, the ACTUAL finite Frobenius identity is

    C_N(chi)=chi(P)^(-N) C_Q(chi^P) mod P, Q=N/P.   (2)

The vector C_N is acquired. The unknown complementary vector C_Q and the unknown permutation chi->chi^P are not. Even if chi^P were observed, this is a character of P modulo ell, not automatically its colour modulo K'. A Jacobi primality congruence can constrain this relation, but its pass must be proved or checked; a failure is not generally a factor.

Thus the first unpaid operation in THIS candidate is extracting a factor-indexed Frobenius eigencharacter from (2) without either C_Q, an unknown-P automorphism, or a passing congruence certificate. Paying d≈K' makes the whole packed vector affordable, but does not initialize that operation. The native beta/W odd coprime orders do not cancel C_Q: those elements do not occur in the Gauss identity, and replacing the Gauss base by them would require the old coupled long exponent relation again.

The conditional gate of §§2–3 is a genuine finite way to bypass that extraction on a specific public branch. A universally passing, affordable family of such certificates—or a bounded failure branch that returns a factor or sufficiently small true residue palette—would be a new supplier theorem. Neither follows from the cited primality test. This is a scoped missing input, not a general impossibility statement about finite extensions or character algorithms.

## 5. Executable conditional supplier

`cubic_gate.py` implements §2 with standard-library exact rank12 quotient arithmetic. Run `python3 cubic_gate.py --N INTEGER --K INTEGER` (or `--e E`), optionally `--output PATH`. It returns a verified proper factor, DECLINE, or an explicit two-residue PALETTE with n and a public HH size-budget flag. That flag does not verify the native scalar preparation or implement HH. Gamma is output as twelve coefficients with the basis convention stated, plus the two coefficient gcds. No hidden field or automorphism oracle is used.

`python3 cubic_gate.py --self-test --output PATH` checks the Gauss identity EXACTLY over the integer quotient, its reductions modulo three prime controls, the source Frobenius formula on those prime controls, a prime palette branch, one composite proper-factor branch, and one composite decline branch. Recorded output is `cubic-gate-validation.json`; `cubic-gate-decline-control.json` records the N=55 control. These are functional structural controls, not native coverage or success-frequency evidence.
