# Comparable high/high digital code: direct source gate

2026-10-18. Paper proof, exact finite regression, primary-source audit. This is
an ordinary-correlation/source-deletion result, **not a prime cancellation
estimate, a meromorphic continuation theorem, or an RH bound**. The full
spectral and moving-scale argument below remains paper-level. Its native
finite ternary recurrence and repeated-11 contraction are separately checked
in [ArithmeticOperatorTernaryCorrelationAudit.lean](../scripts/ArithmeticOperatorTernaryCorrelationAudit.lean).
Earlier frozen completion allowances are not reopened.

## Decision and native scope

Put e(x)=exp(2πix), ω=e(1/3), ε(n)=(-1)^s₂(n), η(n)=ω^s₃(n),
f(u)=ε(floor u), g(u)=η(floor u), u≥0. The following qualitative statement has
a direct proof below:

> For every compact interval 0<c≤r≤C<∞,
> M(L):=sup_{c≤r≤C, 0≤T≤L} |∫_[L,L+T] f(u)g(ru)du|/L →0.

It actually follows with any nonnegative moving interval origin in place of
L. Thus for H=2^a, K=3^b comparable, X=H², r=H/K, the actual high/high code
c_X(x)=ε(floor(x/H))η(floor(x/K)) has both mean o(1) and centered prefix
discrepancy o(1) on the annulus [X,2X]. More generally the same proof applies
to comparable positive H,K=o(X). It does not cover arbitrary changing digit
phases, other nonlinear masks, or growing source height.

For fixed ρ=β+iγ, the diagnostic matched mode is

  X^(-ρ) ∫_[X,2X] c_X(x)x^(ρ-1)dx = ∫_[1,2] c_X(Xt)t^(ρ-1)dt = o(1).

The centered version is also o(1). There is no nonzero normalized smooth
matched-power source in this prescribed family. The proof gives no explicit
power rate. It does not imply a uniform estimate for ΣΛ(n)c_X(n), and cannot
be substituted for such a prime estimate. The source gate is already negative
before seeking that estimate.

## 1. Uniform translated autocorrelation, proved by digit carries

For either q=2,F=ε or q=3,F=η (also conjugate η), define

  γ_q(h)=lim_(N→∞) N^(-1) Σ_(n<N) F(n+h)conj(F(n)).

This limit and convergence uniform in the translated interval origin follow
elementarily. For fixed integer h≥0 and q^d>h, the correlation summand agrees
with a q^d-periodic function except when n mod q^d lies in the final h
residues. Use zero for that periodic function on the exceptional residues.
For an interval of N integers its average differs from the limiting average
by at most

  2h/q^d + 2q^d/N.

To justify this constant without overlooking a carry-tail error, partition
the translated interval into floor(N/q^d) consecutive full blocks of length
q^d starting at its actual origin, and ONE final remainder. Each full block
differs from the periodic approximant's period sum by at most h. The actual
remainder sum minus its length times the periodic mean costs at most 2q^d.
Thus the finite average differs from the periodic mean by at most
h/q^d+2q^d/N. Its limiting mean differs by at most h/q^d, already paying the
second carry-tail term in the displayed bound.

The periodic averages are Cauchy as d→∞ by the same carry exception argument;
this also proves existence, without assuming a dynamical theorem. Negative
lags follow by conjugation and translating the origin. Endpoints in continuous
intervals cost O_h(1/N).

For the real step function F(floor u), its limiting autocorrelation Γ_q is
exactly linear interpolation:

  Γ_q(h+s)=(1-s)γ_q(h)+sγ_q(h+1), h∈Z, 0≤s≤1.

Convergence is uniform in nonnegative moving interval origins, for every fixed
lag. Γ_q is continuous, positive definite and Γ_q(0)=1. Let σ_q be its Bochner
probability measure on **R**, with Γ_q(t)=∫e(tξ)dσ_q(ξ). This construction keeps
all continuous-suspension aliases; it does not identify σ_q with a single
circle alias or discard a pure point component by assumption.

The passage to moving bounded lags is also uniform: for |t-t'|≤1, a length-N
average can change by at most 2|t-t'|(1+2/N), apart from its O(1/N) window
edges. This follows by counting the integer discontinuities crossed by the
two arguments. Thus fixed-lag convergence extends to convergent moving lags.

## 2. Exact ternary contraction; matrix orientation

Write γ=γ₃ and v(n)=(γ(n),γ(n+1))ᵀ. Complete digit multiplicativity gives

  γ(3n+d)=ω^d[(3-d)γ(n)+dγ(n+1)]/3, d=0,1,2.

In particular γ(0)=1 and γ(1)=2ω/(3-ω). The exact matrices are

  A₀ = [[1,0],[2ω/3,ω/3]],
  A₁ = [[2ω/3,ω/3],[ω²/3,2ω²/3]],
  A₂ = [[ω²/3,2ω²/3],[0,1]],
  v(3n+d)=A_d v(n).

Every ||A_d||∞≤1. For n with digits d₀,d₁,...,d_l in **LSB-first order**,
v(n)=A_d₀ A_d₁ ... A_d_l v(0). The contraction block is

  A₁²=(1/9)[[1+4ω²,2+2ω²],[2+2ω,1+4ω]],
  θ:=||A₁²||∞=(sqrt(13)+2)/9 < 2/3 <1.

Consequently 2j consecutive *leading* ternary digits 1 give a rightmost
A₁^(2j), and ||v(n)||∞≤θ^j. The intervening lower-digit factors have norm≤1.
Exactly the same statement holds after conjugating ω. No LSB/MSB reversal
is being used to infer a contraction that is absent from the actual product.

There is also a genuinely finite cyclic identity, checked independently of
γ: C_(q,l)(h)=q^(-l)Σ_(n<q^l)F((n+h) mod q^l)conj(F(n)). If ζ=-1 for
q=2 or ζ=ω for q=3, then

  C_(q,l+1)(qn+d)=ζ^d[(q-d)C_(q,l)(n)+dC_(q,l)(n+1)]/q.

For ternary cyclic vectors the same A_d act, with terminal v₀=(1,1).
The regression verifies all cyclic correlations directly through l=5 in
base 3 and l=7 in base 2, then checks their recurrences and LSB products.

## 3. Every fixed real dilation has a ternary zero-rigidity subsequence

Fix r>0. The irrational rotation

  {m log₃2 + log₃r}

is dense, with arbitrarily late visits to every nonempty open interval. For
each j let P_j=(3^(2j)-1)/2, whose ternary expansion is 2j copies of 1. Choose
m_j increasing so that for an integer v_j→∞,

  (P_j+1/3)3^v_j < r2^m_j < (P_j+2/3)3^v_j,
  3^v_j/3 > j+2.

These are precisely an open mantissa cylinder and a lower bound on m_j, so
density proves the choice. Therefore floor(r2^m_j)+h retains its first 2j
ternary digits 1 for every integer |h|≤j. Hence

  γ₃(floor(r2^m_j)+h)→0 for every fixed integer h,
  Γ₃(r2^m_j+t)→0 for every fixed real t.

The second assertion uses interpolation, with the two adjacent offsets
bounded in terms of t; the fractional part of r2^m_j need not converge.
Central-third protection is essential here: a bare statement about a long
leading word, with no distance from its cylinder boundary, would not justify
all fixed shifted lags.

## 4. Binary nonzero rigidity and all-real-dilation spectral singularity

The exact binary relations are

  γ₂(0)=1, γ₂(1)=-1/3,
  γ₂(2n)=γ₂(n),
  γ₂(2n+1)=-(γ₂(n)+γ₂(n+1))/2.

They imply, for every fixed integer h,

  γ₂(2^m+h)→-(1/3)γ₂(h).

For completeness, h=0 is exact; h=1 obeys u_m=1/6-u_(m-1)/2
and tends to 1/9; h=-1 obeys the same contraction. Strong induction on
|h| then uses the displayed recurrences; every other index on the right has
smaller absolute value. Interpolation gives the same identity for every real
t with Γ₂ in place of γ₂.

Let D_rσ₃ be the pushforward under ξ↦rξ. Along m_j from §3, the bounded
characters e(2^m_j ξ) converge weak* in L∞(σ₂) to -1/3, and weak* in
L∞(D_rσ₃) to 0. Indeed the preceding correlation limits give this against
each exponential e(tξ); linear combinations are L¹-dense for finite Borel
measures on R, and the characters are uniformly bounded. If a nonzero finite
positive measure ν were dominated by both σ₂ and D_rσ₃, using the two L¹
Radon–Nikodym derivatives would force

  ∫e(2^m_j ξ)dν → -(1/3)ν(R) and →0,

a contradiction. Thus σ₂ ⟂ D_rσ₃ for **every** r>0. Replacing η by conjugate
η gives the same proof, which is the version needed for the nonconjugated
product f(u)g(ru). This proves singularity for these observable measures;
no assertion about disjointness of their entire suspension systems is needed.

## 5. Moving slopes and intervals: compactness, tightness, and overlap

For any interval I=[A,A+T]⊂[0,∞), define probability measures

  dμ_I(ξ)=T^(-1)|Fourier(1_I f)(ξ)|²dξ,
  dν_(I,r)(ξ)=T^(-1)|Fourier(1_I conj(g(r·)))(ξ)|²dξ.

Their mass is exactly 1 by Plancherel. Their characteristic functions are
the windowed autocorrelations, including the exact overlap I∩(I-t). The
lost edge has measure≤|t|, so costs at most |t|/T. Section 1 therefore gives,
uniformly in A, as T→∞,

  μ_I ⇒ σ₂;
  if r_j→r₀∈[c,C], ν_(I_j,r_j) ⇒ D_r₀(conjugate-observable σ₃).

For the second assertion, change variable by r_j; the averaged interval has
length r_jT_j→∞, the tested lag tends to r₀t, and the interpolated Γ₃ is
continuous. Pointwise characteristic convergence to a continuous probability
characteristic function implies weak convergence and tightness. There is no
escape-of-mass gap at high aliases.

Plancherel and Cauchy give

  |T^(-1)∫_I f(u)g(ru)du| ≤ affinity(μ_I,ν_(I,r)).

Here affinity is ∫sqrt(dμ dν). If probability measures μ_j⇒μ,ν_j⇒ν and
μ⟂ν, their affinity tends to 0. One elementary proof chooses a continuous
0≤φ≤1 with ∫φdμ arbitrarily close to 1 and ∫φdν arbitrarily close to 0,
then bounds the affinity by

  sqrt(∫φdμ_j ∫φdν_j)
  +sqrt(∫(1-φ)dμ_j ∫(1-φ)dν_j).

Use §4, compactness of [c,C], and contradiction to get uniform cancellation
for all moving r∈[c,C], all origins A, and lengths T→∞. For a prefix T≤L,
split T<δL (trivial bound≤δL) from T≥δL (the just-proved uniform result).
First L→∞, then δ→0. This proves the stated M(L)→0. It is not a fixed-ratio
theorem silently applied along a moving diagonal: the compactness and spectral
continuity argument is precisely the uniformity bridge.

## 6. Centered source calculation and limitations

With L=X/H→∞ and r=H/K∈[c,C], let m_X=∫_[1,2]c_X(Xt)dt and
A_X(v)=∫_[1,v] (c_X(Xt)-m_X)dt. The rescaling in §0 gives

  |m_X|≤M(L), sup_v|A_X(v)|≤2M(L), A_X(1)=A_X(2)=0.

Integration by parts gives, for every fixed complex ρ,

  ∫_[1,2] (c_X(Xt)-m_X)t^(ρ-1)dt
    =(1-ρ)∫_[1,2]A_X(t)t^(ρ-2)dt.

Its modulus is at most 2M(L)|1-ρ|∫_[1,2]t^(Reρ-2)dt=o(1); the removed mean
is also o(1). Thus neither a nonzero mean nor a centered smooth response
survives in the prescribed comparable high/high family. The discrete
unit-cell correction is O_ρ(1/X), since H,K are integer here and the code is
constant on physical unit cells.

No rate for M is extracted: protected-prefix hitting times and compactness
are qualitative. This does not rule out smaller arithmetic responses,
height-dependent resonances, different digital codes, or an estimate using
actual arithmetic information not described by the matched smooth mode.

## Primary literature audit (not an application by name alone)

* Grabner–Liardet–Tichy, *Spectral disjointness of dynamical systems related
  to some arithmetic functions*, Publ. Math. Debrecen 66 (2005), 213–244,
  [author PDF](https://www.math.tugraz.at/~grabner/Publications/Disjoint.pdf).
  Lemma 1 / (2.4), author PDF pp5–6: digit-block matrix contraction;
  Lemma 2, pp7–8: block occurrence along powers of a multiplicatively
  independent base; Theorems 3–4, pp8–9: different scalar rigid-time limits
  imply spectral singularity; Theorem 6, pp10–11: p-power scalar rigidity.
  The paper's stated disjointness is for discrete systems, not the uniform
  moving real dilation result above. Sections 1–5 supply the additional
  continuous-step, protected-prefix and compactness arguments explicitly.
* Kamae, *Sum of digits to different bases and mutual singularity of their
  spectral measures*, Osaka J. Math. 15 (1978), 569–574,
  [primary PDF](https://ir.library.osaka-u.ac.jp/repo/ouka/all/4456/ojm15_03_08.pdf),
  theorem p569. The stated theorem is undilated spectral singularity.
  It alone does not justify a uniform moving-threshold application.
* Drmota–Spiegelhofer, *The joint distribution of binary and ternary digits
  sums*, [arXiv:2501.00850v1](https://arxiv.org/abs/2501.00850), Proposition 1.1,
  p4. Uniform power cancellation is stated for e(t₁s₂(3^K n)+t₂s₃(n)) and
  e(t₁s₂(n)+t₂s₃(2^K n+r)), with 0≤K≤c₂log N and r∈{0,1}, also restricting
  n to either parity. This is genuine growing-multiplier uniformity, but not
  our two growing high-digit cutoffs. It is not used to infer the conclusion.
* Spiegelhofer, *Piatetski-Shapiro sequences via Beatty sequences*, Acta
  Arith. 166 (2014), Proposition 3 / (17)–(18), pp209–212:
  [primary PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/81902).
  Its fixed full-digit, translated sums do not state the moving-threshold
  theorem. The old period-completion allowance stays frozen.

The exact regression passes 34,836 checks, including 617 finite cyclic
recurrences and 364 finite cyclic matrix products. It checks only finite
identities in §§1–4 and native overlap/rescaling identities. It is not
numerical evidence for qualitative limits in §5; those are proved on paper
above. See the pinned exact-results.json for the individual counts.

## Formal boundary and review

The finite Lean leaf defines the actual code `omega^(digits 3 n).sum`, already
identified with its integer factorial valuation, and its literal cyclic
correlations at period `3^M`. It proves the digit recurrence exactly at each
finite level, with the finite initial vector `(1,1)`. It then proves a rational
two-one-digit contraction `7/9`, and its iteration on native finite
correlations. The sharper matrix constant above is not required by that leaf.

These are not substitutes for the spectral limit, Bochner, uniform translated
autocorrelation, dilation-singularity or Hellinger arguments. Those arguments
were reviewed independently in this session, but have not been formalized.
The 34,836 exact regression checks also do not certify them. No analytic
source theorem for the actual nonlinear prime-weighted code is asserted.

Evidence, local strict validation and source hashes are recorded in
[the checkpoint](arithmetic-operator-native-gauge-digital-tn2-gates.json).
