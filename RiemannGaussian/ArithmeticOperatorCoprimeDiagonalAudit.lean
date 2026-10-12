/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGaussianCoprimeAudit

/-!
# Actual semiprime diagonals obstruct even moving Schur PSD rescues

The full actual Mobius divisor row is multiplicative, with every proper
power still present in its definition. Its diagonal on two distinct prime
factors is exactly the product of their two phased prime diagonals. At
each prescribed nonzero height, genuine primes cofinally occupy one fixed
small positive-phase band. Their squarefree product has a negative literal
diagonal, including the native diagonal credit.

Consequently ANY unit-diagonal Schur factor leaves this unrestricted PSD
premise false. No continuity, fixed width, stationary coordinates or
off-diagonal hypothesis is needed. This rejects a PSD rescue, not a
restricted signed packet, a native source asymptotic or the Gaussian/Weil
endpoint. Qualitative PNT is used only to locate counterexample rows.
-/

namespace RiemannGaussian.ArithmeticOperatorCoprimeDiagonalAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGcdAudit ArithmeticOperatorMoebiusCoprimeAudit
open SuzukiCarryCorrelation
open scoped BigOperators Topology ComplexConjugate

private def actualColumn (y : ℝ) : ArithmeticFunction ℂ :=
  ⟨column y,by simp [column,ArithmeticOperatorMoebiusCoprimeAudit.mu]⟩

private theorem actualColumn_multiplicative (y : ℝ) :
    (actualColumn y).IsMultiplicative := by
  refine ⟨by simp [actualColumn,column,ArithmeticOperatorMoebiusCoprimeAudit.mu,primePhase],?_⟩
  intro a b hc
  by_cases ha : a=0
  · subst a
    simp [actualColumn,column,ArithmeticOperatorMoebiusCoprimeAudit.mu]
  by_cases hb : b=0
  · subst b
    simp [actualColumn,column,ArithmeticOperatorMoebiusCoprimeAudit.mu]
  have hm : (ArithmeticFunction.moebius (a*b) : ℂ)=
      (ArithmeticFunction.moebius a : ℂ)*(ArithmeticFunction.moebius b : ℂ) := by
    exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.2 hc
  change (ArithmeticFunction.moebius (a*b) : ℂ)*primePhase y (a*b)=_
  rw [hm,ArithmeticOperatorGammaTwistAudit.primePhase_mul y
    (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)]
  change _=((ArithmeticFunction.moebius a : ℂ)*primePhase y a)*
    ((ArithmeticFunction.moebius b : ℂ)*primePhase y b)
  ring

private def divisorRow (y : ℝ) : ArithmeticFunction ℂ :=
  actualColumn y*(ArithmeticFunction.zeta : ArithmeticFunction ℂ)

private theorem divisorRow_eq (y : ℝ) (n : ℕ) :
    divisorRow y n=gcdKernel (column y) n n := by
  rw [divisorRow,ArithmeticFunction.coe_mul_zeta_apply,gcdKernel,Nat.gcd_self]
  rfl

/-- Exact native diagonal product, with ordinary actual Mobius and its
complete divisor fibers; no prime-only surrogate is inserted. -/
theorem semiprime_diagonal {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (y : ℝ) :
    augmentedKernel y (p*q) (p*q)=2*(1-primePhase y p)*(1-primePhase y q) := by
  have hc := (Nat.coprime_primes hp hq).mpr hpq
  have hmult : (divisorRow y).IsMultiplicative :=
    (actualColumn_multiplicative y).mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hprime (r : ℕ) (hr : r.Prime) : divisorRow y r=1-primePhase y r := by
    rw [divisorRow_eq,gcdKernel,Nat.gcd_self,hr.divisors,Finset.sum_pair hr.ne_one.symm]
    simp [column,ArithmeticOperatorMoebiusCoprimeAudit.mu,
      ArithmeticFunction.moebius_apply_prime hr,primePhase]
    ring
  rw [augmentedKernel,ite_eq_left rfl,←divisorRow_eq,hmult.2 hc,hprime p hp,hprime q hq]
  ring

private theorem phase_re (y : ℝ) (n : ℕ) :
    (primePhase y n).re=Real.cos (y*Real.log n) := by
  simp only [primePhase,Complex.exp_re,Complex.neg_re,Complex.neg_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,one_mul,
    zero_add,sub_zero,neg_zero,Real.exp_zero]
  rw [neg_mul,Real.cos_neg]

private theorem phase_im (y : ℝ) (n : ℕ) :
    (primePhase y n).im= -Real.sin (y*Real.log n) := by
  simp only [primePhase,Complex.exp_im,Complex.neg_re,Complex.neg_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,one_mul,
    zero_add,sub_zero,neg_zero,Real.exp_zero,one_mul]
  rw [neg_mul,Real.sin_neg]

/-- Both prime phases are retained through the joint diagonal. -/
theorem semiprime_diagonal_real {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (y : ℝ) :
    (augmentedKernel y (p*q) (p*q)).re=
      2*((1-Real.cos (|y| *Real.log p))*(1-Real.cos (|y| *Real.log q))-
        Real.sin (|y| *Real.log p)*Real.sin (|y| *Real.log q)) := by
  rw [semiprime_diagonal hp hq hpq]
  norm_num [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,phase_re,phase_im]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    ring
  · rw [abs_of_nonpos hy]
    simp only [neg_mul,Real.cos_neg,Real.sin_neg]
    ring

/-- Exact rational sign margin on the small phase rectangle. -/
theorem small_angles_negative {a b : ℝ} (ha0 : 1/4≤a) (ha1 : a≤1/2)
    (hb0 : 1/4≤b) (hb1 : b≤1/2) :
    2*((1-Real.cos a)*(1-Real.cos b)-Real.sin a*Real.sin b)≤-(1/25 : ℝ) := by
  have hcos (x : ℝ) (hx0 : 1/4≤x) (hx1 : x≤1/2) :
      0≤1-Real.cos x ∧ 1-Real.cos x≤1/8 := by
    have hsq : x^2≤1/4 := by nlinarith
    exact ⟨sub_nonneg.mpr (Real.cos_le_one _),by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]⟩
  have hsin (x : ℝ) (hx0 : 1/4≤x) (hx1 : x≤1/2) : 1/5≤Real.sin x := by
    have hx : 0≤x := by linarith
    have hcube : x^3≤1/8 := by
      have h := pow_le_pow_left₀ hx hx1 3
      norm_num at h
      exact h
    nlinarith [Real.sin_ge_sub_cube hx]
  have ha := hcos a ha0 ha1
  have hb := hcos b hb0 hb1
  have hprod := mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0 : ℝ)≤1/8)
  have hsa := hsin a ha0 ha1
  have hsb := hsin b hb0 hb1
  have hsinprod := mul_le_mul hsa hsb (by norm_num : (0 : ℝ)≤1/5)
    (by linarith : 0≤Real.sin a)
  nlinarith

/-- Shifted logarithmic phase scale; the small band is away from a
zero phase, so its two-factor diagonal has a UNIFORM negative margin. -/
def smallPhaseScale (y : ℝ) (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ)*(2*Real.pi)+1/4)/|y|)

private theorem scale_tendsto {y : ℝ} (hy : y≠0) :
    Tendsto (smallPhaseScale y) atTop atTop := by
  have ht : Tendsto (fun J : ℕ => (J : ℝ)*(2*Real.pi)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by positivity : 0<2*Real.pi)
  have ht' : Tendsto (fun J : ℕ => ((J : ℝ)*(2*Real.pi)+1/4)/|y|) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (1/4 : ℝ) ht).atTop_div_const (abs_pos.mpr hy)
  exact Real.tendsto_exp_atTop.comp ht'

private theorem eventually_prime_window {x : ℕ → ℝ} (hx : ∀ J,0<x J)
    (ht : Tendsto x atTop atTop) {A : ℝ} (hA : 1<A) :
    ∀ᶠ J in atTop,∃ p∈PrimeWindow.primesInWindow (x J) A,True := by
  have hs := (PrimeWindow.theta_interval_div_tendsto (zero_lt_one.trans hA)).comp ht
  filter_upwards [hs.eventually (eventually_gt_nhds (by linarith : (0 : ℝ)<A-1))] with J hJ
  have hd := (lt_div_iff₀ (hx J)).mp hJ
  rw [zero_mul] at hd
  have hv := PrimeWindow.sum_log_primesInWindow (hx J).le hA.le
  have hn : (PrimeWindow.primesInWindow (x J) A).Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty.mp hh,Finset.sum_empty] at hv
    linarith
  obtain ⟨p,hp⟩ := hn
  exact ⟨p,hp,trivial⟩

/-- Every head has a squarefree semiprime with a negative actual
diagonal at the prescribed fixed height. No source assumption is used. -/
theorem exists_negative_semiprime_diagonal {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧ Squarefree (p*q) ∧
      (augmentedKernel y (p*q) (p*q)).re≤-(1/25 : ℝ) := by
  let A := Real.exp (1/(8*|y|))
  have ha := abs_pos.mpr hy
  have hA : 1<A := Real.one_lt_exp_iff.mpr (by positivity)
  have hpos (J : ℕ) : 0<smallPhaseScale y J := Real.exp_pos _
  have hpos' (J : ℕ) : 0<A*smallPhaseScale y J := mul_pos (zero_lt_one.trans hA) (hpos J)
  have hfirst := eventually_prime_window hpos (scale_tendsto hy) hA
  have hsecond := eventually_prime_window hpos'
    ((scale_tendsto hy).const_mul_atTop (zero_lt_one.trans hA)) hA
  have hbig := (scale_tendsto hy).eventually (eventually_gt_atTop (H : ℝ))
  obtain ⟨J,hJ⟩ := (hfirst.and (hsecond.and hbig)).exists
  obtain ⟨p,hp,_⟩ := hJ.1
  obtain ⟨q,hq,_⟩ := hJ.2.1
  obtain ⟨hpl,hpu,hpPrime⟩ := PrimeWindow.mem_primesInWindow_bounds
    (hpos J).le (zero_lt_one.trans hA).le hp
  obtain ⟨hql,hqu,hqPrime⟩ := PrimeWindow.mem_primesInWindow_bounds
    (hpos' J).le (zero_lt_one.trans hA).le hq
  have hpq : p<q := by exact_mod_cast hpu.trans_lt hql
  have hpH : H<p := by exact_mod_cast hJ.2.2.trans hpl
  let T := (J : ℝ)*(2*Real.pi)
  have hlo : (T+1/4)/|y|<Real.log p := by
    simpa [T,smallPhaseScale] using Real.log_lt_log (hpos J) hpl
  have hhi : Real.log q≤1/(8*|y|)+(1/(8*|y|)+(T+1/4)/|y|) := by
    have h := Real.log_le_log (by exact_mod_cast hqPrime.pos) hqu
    rw [Real.log_mul (by positivity : A≠0) (hpos' J).ne',
      Real.log_mul (by positivity : A≠0) (hpos J).ne'] at h
    simpa [A,T,smallPhaseScale] using h
  have hlogs : Real.log p≤Real.log q :=
    Real.log_le_log (by exact_mod_cast hpPrime.pos) (by exact_mod_cast hpq.le)
  let a := |y| *Real.log p-T
  let b := |y| *Real.log q-T
  have ha0 : 1/4≤a := by
    have h := (div_lt_iff₀ ha).mp hlo
    dsimp [a]
    nlinarith
  have hb1 : b≤1/2 := by
    have h := mul_le_mul_of_nonneg_left hhi ha.le
    field_simp at h
    dsimp [b]
    nlinarith
  have hab : a≤b := by
    dsimp [a,b]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hlogs ha.le) T
  have ha1 : a≤1/2 := hab.trans hb1
  have hb0 : 1/4≤b := ha0.trans hab
  refine ⟨p,q,hpH,hpq,hpPrime,hqPrime,
    (Nat.squarefree_mul ((Nat.coprime_primes hpPrime hqPrime).mpr hpq.ne)).mpr
      ⟨hpPrime.squarefree,hqPrime.squarefree⟩,?_⟩
  rw [semiprime_diagonal_real hpPrime hqPrime hpq.ne]
  have hap : |y| *Real.log p=a+(J : ℝ)*(2*Real.pi) := by dsimp [a,T]; ring
  have hbq : |y| *Real.log q=b+(J : ℝ)*(2*Real.pi) := by dsimp [b,T]; ring
  rw [hap,hbq,Real.cos_add_nat_mul_two_pi,Real.cos_add_nat_mul_two_pi,
    Real.sin_add_nat_mul_two_pi,Real.sin_add_nat_mul_two_pi]
  exact small_angles_negative ha0 ha1 hb0 hb1

/-- Full finite Schur quadratic, retaining actual Mobius, every proper
power, the native diagonal credit and arbitrary off-diagonal coupling. -/
def schurQuadratic (K : ℕ → ℕ → ℂ) (y : ℝ) (S : Finset ℕ) (alpha : ℕ → ℂ) : ℂ :=
  ∑ m∈S,∑ n∈S,alpha m*conj (alpha n)*K m n*augmentedKernel y m n

/-- Exact singleton embedding of the actual diagonal. -/
theorem singleton_eq (K : ℕ → ℕ → ℂ) (y : ℝ) (n : ℕ) (hK : K n n=1) :
    schurQuadratic K y {n} (fun _ => 1)=augmentedKernel y n n := by
  simp [schurQuadratic,hK]

/-- No Schur factor preserving the unit diagonal can make this actual
matrix PSD beyond a head. Moving, nonstationary and ADDITIVE Gaussians
are included; only the full unrestricted PSD premise is refuted. -/
theorem not_unit_diagonal_schur_psd {y : ℝ} (hy : y≠0) (H : ℕ)
    (K : ℕ → ℕ → ℂ) (hK : ∀ n,H<n → K n n=1) :
    ¬(∀ S : Finset ℕ,(∀ n∈S,H<n) → ∀ alpha : ℕ → ℂ,
      0≤(schurQuadratic K y S alpha).re) := by
  intro hPSD
  obtain ⟨p,q,hpH,_,_,hq,_,hneg⟩ := exists_negative_semiprime_diagonal hy H
  have hn : H<p*q := hpH.trans_le (Nat.le_mul_of_pos_right p hq.pos)
  have hs : ∀ n∈({p*q} : Finset ℕ),H<n := by
    intro n h
    have he : n=p*q := by simpa using h
    simpa [he] using hn
  have h := hPSD {p*q} hs (fun _ => 1)
  rw [singleton_eq K y (p*q) (hK (p*q) hn)] at h
  linarith

/-- At an actual zero ordinate the same negative literal semiprime
diagonal survives ANY unit-diagonal Schur coupling. -/
theorem not_unit_diagonal_schur_psd_at_zero (rho : NontrivialZetaZero) (H : ℕ)
    (K : ℕ → ℕ → ℂ) (hK : ∀ n,H<n → K n n=1) :
    ¬(∀ S : Finset ℕ,(∀ n∈S,H<n) → ∀ alpha : ℕ → ℂ,
      0≤(schurQuadratic K rho.1.im S alpha).re) :=
  not_unit_diagonal_schur_psd (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H K hK

end
end RiemannGaussian.ArithmeticOperatorCoprimeDiagonalAudit
