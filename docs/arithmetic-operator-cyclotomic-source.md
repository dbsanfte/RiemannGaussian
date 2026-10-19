# Integer q-factorial / cyclotomic Kummer source gate

Research audit, 2026-10-18. The finite cyclotomic identities are checked in
`scripts/ArithmeticOperatorCyclotomicConvolutionAudit.lean`; the analytic
source and inverse-convolution arguments below are paper-level. Original
probes and source pins are retained in
`.lake/arithmetic-operator-cyclotomic-factorial-gate/`. No independent RH
estimate or endpoint change is claimed.

## Decision: faithful source, exact scalar conservation, no new estimate

For each fixed integer b≥2, let A_b(d)=log Φ_d(b), including Φ₁(b)=b−1,
and let φ be Euler's totient. The actual cyclotomic residual

  R_b(d)=A_b(d)−φ(d)log b

has Dirichlet series C_b(s)/ζ(s), where

  c_b(n)=log(1−b^(-n)),  C_b(s)=Σ_(n≥1)c_b(n)n^(-s).

The entire numerator C_b is **uniformly nonzero on Re s≥0**. In particular,
|C₂(s)|≥2/81 there. Thus every hypothetical nontrivial zeta zero survives
with its multiplicity as a pole of this actual integer-norm residual series.
This conclusion does not assume a model prime density or an order-distribution
theorem. The source is in the ordinary integer cyclotomic index d.

However, R_b=μ*c_b exactly, and c_b has an inverse in ℓ¹ for Dirichlet
convolution. Consequently, for every θ≥0,

  Σ_(d≤X)R_b(d)=O_b(X^θ)  iff  Σ_(d≤X)μ(d)=O_b(X^θ).

The factorial floor aggregate cancels that same source exactly:

  Σ_(d≤N)floor(N/d)R_b(d)=Σ_(j≤N)c_b(j),

and the right side converges exponentially. This identifies a faithful
source-bearing object but provides no independent saving for it. Freeze
the shortcut from bounded q-factorial residual to a Möbius bound. Do not
freeze all q-Pascal, q-Lucas, or nonlinear common-divisor interactions.

At nonzero **prime-power** phase, the transported coefficients become an
order-weighted prime series. Its source/continuation is not supplied by
the unphased identity, by Artin density, or by a fixed smooth prime model.
All prime-power and exceptional factors are retained below.

## 1. Exact product, height, and cyclotomic exponents

Use [j]_b=(b^j−1)/(b−1), F_b(N)=∏_(1≤j≤N)[j]_b. Finite factorization gives

  F_b(N)=∏_(2≤d≤N)Φ_d(b)^floor(N/d),
  [N choose M]_b=∏_(2≤d≤N)Φ_d(b)^e_d(N,M),
  e_d=floor(N/d)−floor(M/d)−floor((N−M)/d)∈{0,1}.

The q-binomial is an actual positive integer. Its logarithmic height is
M(N−M)log b+O_b(1) when both legs grow. The factorial is exactly

  F_b(N)=b^(N(N+1)/2)(b−1)^(-N)∏_(j≤N)(1−b^(-j)),
  log F_b(N)=N(N+1)log b/2−N log(b−1)+κ_b+E_b(N),
  κ_b=Σ_(j≥1)c_b(j),
  0≤E_b(N)≤b^(-N)/[(b−1)(1−b^(-(N+1)))].

Thus its full norm, after the displayed archimedean terms and constant,
has exponentially small residual. For the central q-binomial,

  log [2N choose N]_b=N²log b−κ_b+O_b(b^(-N)).

This is distinct from ordinary binomial logarithmic height O(N). At fixed
b the q-factorial includes prime factors as large as b^N−1. An order-index
source N^ρ is not automatically an original prime-cutoff source X^ρ at
X≈b^N; on that exponential scale it is (log X/log b)^ρ.

## 2. Actual valuations, including every exceptional case

If p|b, v_p([j]_b)=v_p(F_b(N))=0. For odd p∤b, set
d=ord_p(b), a=v_p(b^d−1), c=v_p(b−1). LTE gives

  v_p(b^j−1)=0 if d∤j,
               a+v_p(j/d) if d|j;
  v_p(F_b(N))=a floor(N/d)+v_p(floor(N/d)! )−Nc.

If p|b−1 then d=1,a=c and this is exactly v_p(N!). These are finitely many
primes for fixed b; this is not an all-prime bridge to ordinary factorials.

For p=2 and odd b, put c=v₂(b−1), a=v₂(b+1). Then

  v₂([j]_b)=0 for odd j; a−1+v₂(j) for even j,
  v₂(F_b(N))=a floor(N/2)+v₂(floor(N/2)! ).

If b≡1 mod4 then a=1 and this equals v₂(N!). If b≡3 mod4, the additional
factor a must remain. For a q-binomial, the factorial difference gives the
following exact local Kummer bridge. In the odd-prime formula use
A=floor(N/d),B=floor(M/d),C=floor((N−M)/d), ε=A−B−C∈{0,1}; the denominator
correction Nc cancels. For p=2 use d=2 and a=v₂(b+1). Then

  v_p([N choose M]_b)=aε+v_p(A!)−v_p(B!)−v_p(C!).

If ε=0 this is v_p(binomial(A,B)); if ε=1 it is
a+v_p(A)+v_p(binomial(A−1,B)). This is an actual ordinary-factorial carry
constraint at the **p-dependent order quotient**, not a common rescaling
of the original prime index.

The same LTE calculation classifies cyclotomic factors, rather than silently
keeping only primitive primes. For odd p∤b with d>1:

  v_p Φ_d(b)=a; v_p Φ_(d p^k)(b)=1 for k≥1; otherwise zero.

For odd p|b−1: v_p Φ₁(b)=c; v_p Φ_(p^k)(b)=1 for k≥1.
For odd b: v₂ Φ₁(b)=c, v₂ Φ₂(b)=a, v₂ Φ_(2^k)(b)=1 for k≥2.
All other two-adic factors vanish; if 2|b they all vanish.

## 3. Literal prime-power phase transport and a finite counterexample

Define the additive q-integer packet (not the divisor packet of the whole
product F_b(N)) by

  V_b,y(N)=Σ_(j≤N) Σ_(p^r | [j]_b,r≥1) log p · p^(-iry).

For p∤b, c_p=v_p(b−1), define the exact landing index

  m_b(p^r)=ord_(p^(r+c_p))(b).

Then p^r|[j]_b iff m_b(p^r)|j, so the exact finite identity is

  V_b,y(N)=Σ_(p∤b,r≥1)log p · p^(-iry) floor(N/m_b(p^r))
           =Σ_(d≤N)W_b,y(d)floor(N/d),
  W_b,y(d)=Σ_(m_b(p^r)=d)log p · p^(-iry).

Only finitely many terms occur at any N, since p^r|[j]_b for some j≤N.
There are no terms for p|b. The denominator shift c_p is necessary.
At y=0, W_b,0(d)=log Φ_d(b) for d≥2 and W_b,0(1)=0.

For an odd p∤b(b−1), d=ord_p(b)>1 and a=v_p(b^d−1):

  m_b(p^r)=d p^max(0,r−a),
  W_p(d)=log p Σ_(1≤r≤a)p^(-iry),
  W_p(d p^k)=log p · p^(-i(a+k)y), k≥1.

For odd p|b−1: m_b(p^r)=p^r. For odd b and p=2:
if b≡1 mod4, m_b(2^r)=2^r;
if b≡3 mod4 and a=v₂(b+1), m_b(2^r)=2 for 1≤r≤a and
m_b(2^r)=2^(r−a+1) for r>a.

**Diagnostic failure of resetting the phase:** b=2,p=3 gives d=2,a=1.
The transported contribution at d=6 is log3·3^(-2iy), although Φ₆(2)=3.
Phasing that cyclotomic integer from its own first valuation layer would give
log3·3^(-iy), a different quantity. Similarly F₂(4)=315 contains 3²:
its whole-integer divisor packet has log3(z₃+z₃²), while adding packets of
its q-integer factors has 2log3·z₃ at p=3. Equality is restored only when y=0.
The regression retains the formal labels (p,r), not numerical phase samples.

## 4. Source first: exact nonzero reciprocal-zeta response

Möbius inversion of b^n−1=∏_(d|n)Φ_d(b) gives, for every d≥1,

  A_b(d)=φ(d)log b+Σ_(e|d)μ(d/e)c_b(e),
  R_b=μ*c_b.

For Re s>2 (then by continuation),

  Σ_(d≥1)A_b(d)d^(-s)=[log b·ζ(s−1)+C_b(s)]/ζ(s),
  Σ_(d≥1)R_b(d)d^(-s)=C_b(s)/ζ(s).

C_b is entire because c_b(n) decays exponentially. For Re s≥0,

  |C_b(s)|≥−log(1−1/b)−Σ_(n≥2)−log(1−b^(-n)),
  Σ_(n≥2)−log(1−b^(-n))≤ b/[(b²−1)(b−1)].

For b=2, log2>2/3+2/81 by the first two terms of
log2=2Σ_(k≥0)3^(-(2k+1))/(2k+1), whereas the tail bound is 2/3.
Thus |C₂(s)|≥2/81. For b≥3, −log(1−1/b)≥1/b and

  δ_b:=1/b−b/[(b²−1)(b−1)]>0.

At any hypothetical nontrivial zero ρ, C_b(ρ) is therefore nonzero with
this explicit lower bound. The pole order of C_b/ζ is exactly the zero
multiplicity. At a simple zero its residue is C_b(ρ)/ζ'(ρ). A smooth
Mellin test with transform nonzero at ρ retains that source; the exponential
test has the nonzero factor Γ(ρ), giving the local pole factor
Γ(ρ)C_b(ρ)/ζ'(ρ). This is an exact
meromorphic statement about the actual residual; no contour-shift estimate
or prime-weight explicit formula is asserted.

The full A_b-series numerator need not be assumed nonzero for every fixed
b: its φ term can interfere. The centered residual avoids that unsupported
claim and has the zero-free factor just proved.

## 5. Collapse second: an invertible scalar Möbius convolution

The same strict first-term dominance proves c_b=c_b(1)δ₁+t_b invertible in
the Banach algebra ℓ¹(N) with Dirichlet convolution:

  h_b=c_b(1)^(-1) Σ_(k≥0)(−t_b/c_b(1))^(*k),
  ||h_b||₁≤1/(|c_b(1)|−||t_b||₁),  μ=h_b*R_b.

All ℓ¹ spaces here are on positive integers. Explicitly, ||c₂||₁≤log2+2/3
and ||h₂||₁≤81/2. For b≥3, the respective constants are at most
log(b/(b−1))+b/[(b²−1)(b−1)] and 1/δ_b.

Let M(X)=Σ_(n≤X)μ(n), S_b(X)=Σ_(n≤X)R_b(n). Exact finite summation gives

  S_b(X)=Σ_(d≤X)c_b(d)M(X/d),
  M(X)=Σ_(d≤X)h_b(d)S_b(X/d).

For θ≥0 these transfer O(X^θ) in both directions using respectively
||c_b||₁ and ||h_b||₁. This includes θ=1/2+ε, the usual reciprocal-zeta
growth target. No arithmetic estimate has been gained by the change of
observable. In particular, a bounded factorial floor aggregate says nothing
stronger: because Σ_(d|n)R_b(d)=c_b(n),

  Σ_(d≤N)floor(N/d)R_b(d)=Σ_(n≤N)c_b(n)=κ_b+O_b(b^(-N)).

The source cancels by an **exact ζ factor**, rather than by an independently
stronger estimate. This is the concrete scoped conservation gate.

## 6. What changes at nonzero prime phase, and the exact unpaid input

For Re s>2 define

  W_b,y(s)=Σ_(p∤b,r≥1)log p · p^(-iry)m_b(p^r)^(-s).

Absolute convergence follows from |W_b,y(d)|≤W_b,0(d)=log Φ_d(b)=O_b(d).
For an odd prime with d>1,a as above its contribution is exactly

  log p · d^(-s)[Σ_(r=1)^a z_p^r
           + z_p^a p^(-(s+iy))/(1−p^(-(s+iy)))], z_p=p^(-iy).

An odd p|b−1 contributes log p·p^(-(s+iy))/(1−p^(-(s+iy))).
For odd b and p=2 in the b≡1 mod4 branch the analogous formula applies;
for b≡3 mod4 it is

  log2[2^(-s)Σ_(r=1)^a z₂^r
       +z₂^(a−1)2^(-2(s+iy))/(1−2^(-(s+iy)))].

This is a sum over order fibers, not an Euler product in d. A source theorem
for y≠0 would need a continuation/residue statement for this actual series,
or comparably strong joint prime-size/order/lift control. Specifically it
must control the measure

  Σ_(p≤P,p∤b)log p·1_(ord_p(b)=d, v_p(b^d−1)=a),

uniformly in the growing d,a ranges and with the literal phase weights.
For fixed d the primes are divisors of b^d−1, a finite set. Such a fiber is
not an ordinary positive-density prime progression. There is no homogeneous
identity d≈p: log_b p≤d≤p−1, with a huge possible gap. Primitive-root or
fixed order-congruence density alone also does not establish the secondary
zeta-zero covariance. For square bases a primitive-root subpopulation may
even be empty. No density is silently discarded or assumed nonzero here.

The unphased continuation is proved above by exact integer factorization.
It does not justify continuing in y: although real-y continuity holds in
Re s>2, positive imaginary y can amplify p^r as large as b^d. A joint
holomorphic neighborhood, let alone persistence of the zero source, is not
granted by dominated convergence in that original half-plane.

## 7. Actual q-Pascal/Frobenius scope; what is not a no-go

The integer identities genuinely retain addition:

  Q_b(N,M)=Q_b(N−1,M)+b^(N−M)Q_b(N−1,M−1),
  ∏_(0≤j<N)(1+b^jT)=Σ_(k=0)^N b^(k(k−1)/2)Q_b(N,k)T^k.

If p∤b and d=ord_p(b), a full d-block satisfies
∏_(j<d)(1+b^jT)=1−(−T)^d mod p. The polynomial q-Lucas theorem gives,
writing N=dA+a,M=dB+c with 0≤a,c<d,

  Q_b(N,M)≡binomial(A,B)Q_b(a,c) mod Φ_d(b).

These are actual congruences, stronger data than arbitrary scalar positivity.
But their local valuation consequence is exactly the order-quotient Kummer
formula of §2, and their full logarithmic norm has the explicit height of §1.
No extra simultaneous-prime estimate follows in this preflight.

Only the floor-exponent integrality alone admits the following countermodel:
replace Φ_d(b) by ANY integers C_d≥1. Then ∏C_d^e_d is still an integer for
all N,M. This does **not** preserve q-Pascal: C_d=2 gives Q(2,1)=2 while
the b=2 Pascal relation requires 3. Therefore the scalar collapse of §§4–5
does not prove that all genuine additive q-relations are useless. A next
escape would have to produce an estimate on the faithful R_b (or the exact
phased order series) using one of those additional joined relations; merely
rewriting the floor product does not provide it.

## Primary pins and formalization decision

* Pongsriiam, *Quasi-Injectivity of Some Arithmetic Functions*, JIS 24
  (2021), Article 21.10.1, Lemma 2, printed p3:
  https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf.
  It states the odd-prime LTE formula and both exceptional two-adic cases.
* Sagan, *Congruence properties of q-analogs*, Adv. Math. 95 (1992),
  127–143, Theorems 2.1–2.2, pp130–132:
  https://users.math.msu.edu/users/bsagan/Papers/Old/cpq-pub.pdf.
  The q-Lucas congruence is modulo the cyclotomic polynomial; integer
  evaluation gives precisely the modulus Φ_d(b), not arbitrary p-power
  strengthening. Web primary PDF was read; local direct retrieval hit an
  access page and is recorded as such, not mislabeled as a PDF.
* Zudilin, *Congruences for q-binomial coefficients*, arXiv:1901.07843v2
  (2019), pp1–3, Theorems 1–2:
  https://arxiv.org/pdf/1901.07843. Higher cyclotomic congruences are real
  additional identities; this gate does not prove they all collapse.
* Ziegler, *On the distribution of the order of number field elements
  modulo prime ideals*, Theorem 1, p2:
  https://math.sbg.ac.at/vziegler/Papers/Artin.pdf.
  The fixed order-congruence density theorem explicitly assumes GRH for
  the relevant radical/cyclotomic fields. It neither supplies an unconditional
  growing-order source theorem nor the required secondary zero covariance.
* Stewart, *On prime factors of terms of binary recurrence sequences*,
  §3, Lemmas 3–4: author PDF
  https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/onprimef.pdf.
  Inspected as a primitive-factor comparison; its stated algebraic/coprimality
  hypotheses are not silently applied to every pair (b,1). Existence or size
  of a primitive factor is not a source covariance theorem.

The authorized `scripts/ArithmeticOperatorCyclotomicConvolutionAudit.lean`
is strict green: 25 local declarations / 20 theorem declarations including
generated helpers; all 15 namespace linters and the all-local standard-axiom
audit pass. It proves literal integer-polynomial evaluation, positive log
arguments for all b≥2 (including index one), the actual residual divisor
profile, Möbius inversion, exact floor source deletion, and finite
tail-weighted Mertens prefix equality/comparison. The logarithm at b=2,d=1
is zero; no false strict positivity of every logarithm is asserted.

The zero-free numerator and infinite ℓ¹ inverse/equivalence remain explicitly
paper-level. The valuation/order/Frobenius assertions are paper-level with
35,865 exact regression checks; none is labeled a native Lean valuation
theorem. No broader carrier framework or formalized analytic continuation
is introduced.
