/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorMoebiusCoprimeAudit

/-!
# Logarithmic Gaussian damping does not repair actual coprimality PSD

This tests a different coupling from the earlier negative-diagonal
obstruction. Actual Mobius coprimality has nonnegative prime diagonals;
here a pair of nearby LOGARITHMIC prime rows defeats every fixed positive
Gaussian width, including the literal native diagonal credit. The phase
is the prescribed fixed height, not a freely chosen counterexample height.

No weighted-packet zero asymptotic is inferred from the unweighted source
theorem. The proposed unrestricted PSD constraint itself already fails,
including at every actual zero ordinate, so this candidate stops at that
gate. Restricted signed packets and Gaussians in additive distance are not
covered by this logarithmic-distance theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorGaussianCoprimeAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGcdAudit ArithmeticOperatorMoebiusCoprimeAudit
open SuzukiCarryCorrelation
open scoped BigOperators Topology ComplexConjugate

/-- Fixed logarithmic Gaussian, retaining the relative arithmetic scale. -/
def logGaussian (c : ℝ) (m n : ℕ) : ℝ :=
  Real.exp (-c*(Real.log m-Real.log n)^2)

theorem logGaussian_diag (c : ℝ) (n : ℕ) : logGaussian c n n=1 := by
  simp [logGaussian]

theorem logGaussian_symm (c : ℝ) (m n : ℕ) : logGaussian c m n=logGaussian c n m := by
  unfold logGaussian
  congr 1
  ring

/-- Exact full native matrix, with unaltered Mobius and all prime powers. -/
def quadratic (c y : ℝ) (S : Finset ℕ) (alpha : ℕ → ℂ) : ℂ :=
  ∑ m∈S,∑ n∈S,alpha m*conj (alpha n)*(logGaussian c m n : ℂ)*augmentedKernel y m n

/-- Literal antisymmetric pair, including BOTH credited diagonals. -/
def twoPrimeGaussian (c y : ℝ) (p q : ℕ) : ℂ :=
  augmentedKernel y p p+augmentedKernel y q q-
    (logGaussian c p q : ℂ)*augmentedKernel y p q-
    (logGaussian c q p : ℂ)*augmentedKernel y q p

theorem twoPrimeGaussian_eq_quadratic {p q : ℕ} (hpq : p≠q) (c y : ℝ) :
    twoPrimeGaussian c y p q=
      quadratic c y {p,q} (fun n => if n=p then 1 else -1) := by
  simp [quadratic,Finset.sum_pair hpq,Ne.symm hpq,logGaussian_diag,twoPrimeGaussian]
  ring

private theorem prime_diagonal {p : ℕ} (hp : p.Prime) (y : ℝ) :
    augmentedKernel y p p=2*(1-primePhase y p) := by
  rw [augmentedKernel,ite_eq_left rfl,gcdKernel,Nat.gcd_self,hp.divisors,
    Finset.sum_pair hp.ne_one.symm]
  simp [column,ArithmeticOperatorMoebiusCoprimeAudit.mu,
    ArithmeticFunction.moebius_apply_prime hp,primePhase]
  ring

private theorem distinct_prime_entry {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (y : ℝ) : augmentedKernel y p q=1 := by
  have hg := ((Nat.coprime_primes hp hq).mpr hpq).gcd_eq_one
  simp [augmentedKernel,hpq,gcdKernel,hg,column,ArithmeticOperatorMoebiusCoprimeAudit.mu,primePhase]

/-- Gaussian damping changes only the actual off-diagonal correlation. -/
theorem twoPrimeGaussian_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (c y : ℝ) :
    twoPrimeGaussian c y p q=
      4-2*primePhase y p-2*primePhase y q-2*(logGaussian c p q : ℂ) := by
  rw [twoPrimeGaussian,prime_diagonal hp,prime_diagonal hq,
    distinct_prime_entry hp hq hpq,distinct_prime_entry hq hp hpq.symm,logGaussian_symm c q p]
  ring

private theorem phase_re (y : ℝ) (n : ℕ) :
    (primePhase y n).re=Real.cos (y*Real.log n) := by
  simp only [primePhase,Complex.exp_re,Complex.neg_re,Complex.neg_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,one_mul,
    zero_add,sub_zero,neg_zero,Real.exp_zero]
  rw [neg_mul,Real.cos_neg]

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

private theorem phase_near_center {y : ℝ} (hy : y≠0) {J : ℕ} {l e : ℝ}
    (hl : (J : ℝ)*(2*Real.pi)/|y|≤l)
    (hu : l≤(J : ℝ)*(2*Real.pi)/|y|+e) (he : e≤1/(2*|y|)) :
    7/8≤Real.cos (y*l) := by
  have ha := abs_pos.mpr hy
  let v := |y| *l-(J : ℝ)*(2*Real.pi)
  have h0 : 0≤v := by
    have h := (div_le_iff₀ ha).mp hl
    dsimp [v]
    nlinarith
  have h1 : v≤1/2 := by
    have h := mul_le_mul_of_nonneg_left hu ha.le
    have h' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) ha)).mp he
    dsimp [v]
    field_simp at h
    nlinarith
  have hc : 7/8≤Real.cos v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hcos : Real.cos (y*l)=Real.cos (|y| *l) := by
    rcases le_total 0 y with hy0 | hy0
    · rw [abs_of_nonneg hy0]
    · rw [abs_of_nonpos hy0,neg_mul,Real.cos_neg]
  have harg : |y| *l=v+(J : ℝ)*(2*Real.pi) := by dsimp [v]; ring
  rwa [hcos,harg,Real.cos_add_nat_mul_two_pi]

/-- Two distinct actual primes occupy one arbitrarily narrow FIXED
logarithmic phase band cofinally. PNT is only used to locate the rows. -/
theorem exists_close_positive_primes {y e : ℝ} (hy : y≠0) (he : 0<e)
    (hePhase : e≤1/(2*|y|)) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      7/8≤Real.cos (y*Real.log p) ∧ 7/8≤Real.cos (y*Real.log q) ∧
      |Real.log p-Real.log q|≤e := by
  let A := Real.exp (e/2)
  have hA : 1<A := Real.one_lt_exp_iff.mpr (by linarith)
  have hpos (J : ℕ) : 0<positiveScale y J := Real.exp_pos _
  have hpos' (J : ℕ) : 0<A*positiveScale y J := mul_pos (zero_lt_one.trans hA) (hpos J)
  have hfirst := eventually_prime_window hpos (positiveScale_tendsto hy) hA
  have hsecond := eventually_prime_window hpos'
    ((positiveScale_tendsto hy).const_mul_atTop (zero_lt_one.trans hA)) hA
  have hbig := (positiveScale_tendsto hy).eventually (eventually_gt_atTop (H : ℝ))
  obtain ⟨J,hJ⟩ := (hfirst.and (hsecond.and hbig)).exists
  obtain ⟨p,hp,_⟩ := hJ.1
  obtain ⟨q,hq,_⟩ := hJ.2.1
  obtain ⟨hpl,hpu,hpPrime⟩ := PrimeWindow.mem_primesInWindow_bounds
    (hpos J).le (zero_lt_one.trans hA).le hp
  obtain ⟨hql,hqu,hqPrime⟩ := PrimeWindow.mem_primesInWindow_bounds
    (hpos' J).le (zero_lt_one.trans hA).le hq
  have hpq : p<q := by exact_mod_cast hpu.trans_lt hql
  have hpH : H<p := by exact_mod_cast hJ.2.2.trans hpl
  let t := (J : ℝ)*(2*Real.pi)/|y|
  have hplog : t<Real.log p := by
    simpa [positiveScale,t] using Real.log_lt_log (hpos J) hpl
  have hqlog : t<Real.log q := hplog.trans (Real.log_lt_log (by exact_mod_cast hpPrime.pos) (by exact_mod_cast hpq))
  have hqulog : Real.log q≤t+e := by
    have h := Real.log_le_log (by exact_mod_cast hqPrime.pos) hqu
    rw [Real.log_mul (by positivity : A≠0) (hpos' J).ne',
      Real.log_mul (by positivity : A≠0) (hpos J).ne'] at h
    simp only [A,positiveScale,Real.log_exp] at h
    dsimp [t]
    linarith
  have hpulog : Real.log p≤t+e :=
    (Real.log_le_log (by exact_mod_cast hpPrime.pos) (by exact_mod_cast hpq.le)).trans hqulog
  refine ⟨p,q,hpH,hpq,hpPrime,hqPrime,
    phase_near_center hy hplog.le hpulog hePhase,
    phase_near_center hy hqlog.le hqulog hePhase,?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- Every fixed logarithmic Gaussian, at EVERY fixed nonzero height,
still has an actual negative two-prime form after EVERY head deletion. -/
theorem exists_negative_gaussian_form {c y : ℝ} (hc : 0≤c) (hy : y≠0) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      (twoPrimeGaussian c y p q).re≤-(1 : ℝ) := by
  let e := min (1/(2*|y|)) (1/(4*(c+1)))
  have he : 0<e := lt_min
    (div_pos zero_lt_one (mul_pos (by norm_num) (abs_pos.mpr hy)))
    (div_pos zero_lt_one (mul_pos (by norm_num) (by linarith)))
  obtain ⟨p,q,hpH,hpq,hp,hq,hcp,hcq,hlog⟩ :=
    exists_close_positive_primes hy he (min_le_left _ _) H
  have hden : 0<4*(c+1) := by positivity
  have hec : 4*(c+1)*e≤1 := by
    have h := (le_div_iff₀ hden).mp (show e≤1/(4*(c+1)) from min_le_right _ _)
    nlinarith
  have he1 : e≤1 := by nlinarith
  have hsq : (Real.log p-Real.log q)^2≤e^2 := by
    rw [abs_le] at hlog
    nlinarith
  have hGaussian : 3/4≤logGaussian c p q := by
    unfold logGaussian
    have hmul := mul_le_mul_of_nonneg_left hsq hc
    have hpow : e^2≤e := by nlinarith
    have hmul' := mul_le_mul_of_nonneg_left hpow hc
    have hbound : c*(Real.log p-Real.log q)^2≤1/4 := by nlinarith
    nlinarith [Real.add_one_le_exp (-c*(Real.log p-Real.log q)^2)]
  refine ⟨p,q,hpH,hpq,hp,hq,?_⟩
  rw [twoPrimeGaussian_eq hp hq hpq.ne]
  norm_num [Complex.mul_re,phase_re]
  nlinarith

/-- The failed Gaussian constraint occurs at the hypothetical ordinate
itself, without exposure, simplicity or any free-prime countermodel. -/
theorem exists_negative_gaussian_at_zero (rho : NontrivialZetaZero) {c : ℝ}
    (hc : 0≤c) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      (twoPrimeGaussian c rho.1.im p q).re≤-(1 : ℝ) :=
  exists_negative_gaussian_form hc (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H

/-- A head deletion and ANY fixed logarithmic Gaussian leave the
unrestricted PSD premise false on the literal integer matrix. -/
theorem not_psd_after_head {c y : ℝ} (hc : 0≤c) (hy : y≠0) (H : ℕ) :
    ¬(∀ S : Finset ℕ,(∀ n∈S,H<n) → ∀ alpha : ℕ → ℂ,
      0≤(quadratic c y S alpha).re) := by
  intro hPSD
  obtain ⟨p,q,hpH,hpq,_,_,hnegative⟩ := exists_negative_gaussian_form hc hy H
  have hsupport : ∀ n∈({p,q} : Finset ℕ),H<n := by
    intro n hn
    have hpair : n=p ∨ n=q := by simpa using hn
    rcases hpair with rfl | rfl
    · exact hpH
    · exact hpH.trans hpq
  have h := hPSD {p,q} hsupport (fun n => if n=p then 1 else -1)
  rw [←twoPrimeGaussian_eq_quadratic hpq.ne c y] at h
  linarith

/-- No exposure or simple-zero hypothesis repairs the failed PSD gate
at an actual zero ordinate. This is not a new zero exclusion. -/
theorem not_psd_at_zero (rho : NontrivialZetaZero) {c : ℝ} (hc : 0≤c) (H : ℕ) :
    ¬(∀ S : Finset ℕ,(∀ n∈S,H<n) → ∀ alpha : ℕ → ℂ,
      0≤(quadratic c rho.1.im S alpha).re) :=
  not_psd_after_head hc (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H

/-- General fixed stationary real damping in logarithmic coordinates;
both ordered incidences remain, so evenness is not assumed. -/
def twoPrimeDamped (g : ℝ → ℝ) (y : ℝ) (p q : ℕ) : ℂ :=
  augmentedKernel y p p+augmentedKernel y q q-
    (g (Real.log p-Real.log q) : ℂ)*augmentedKernel y p q-
    (g (Real.log q-Real.log p) : ℂ)*augmentedKernel y q p

private theorem twoPrimeDamped_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (g : ℝ → ℝ) (y : ℝ) :
    twoPrimeDamped g y p q=4-2*primePhase y p-2*primePhase y q-
      (g (Real.log p-Real.log q) : ℂ)-(g (Real.log q-Real.log p) : ℂ) := by
  rw [twoPrimeDamped,prime_diagonal hp,prime_diagonal hq,
    distinct_prime_entry hp hq hpq,distinct_prime_entry hq hp hpq.symm]
  ring

/-- The obstruction is shared by EVERY fixed continuous stationary
logarithmic Schur kernel with unit diagonal, not only Gaussians. It is
an actual-prime statement, not a free-weight or smooth countermodel. -/
theorem exists_negative_continuous_damping {g : ℝ → ℝ}
    (hg : ContinuousAt g 0) (hg0 : g 0=1) {y : ℝ} (hy : y≠0) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      (twoPrimeDamped g y p q).re≤-(1 : ℝ) := by
  have hsmall : ∀ᶠ x in 𝓝 (0 : ℝ),(3/4 : ℝ)<g x :=
    hg.eventually (eventually_gt_nhds (by rw [hg0]; norm_num))
  obtain ⟨e,he,hs⟩ := Metric.eventually_nhds_iff.mp hsmall
  let w := min (e/2) (1/(2*|y|))
  have hw : 0<w := lt_min (by linarith)
    (div_pos zero_lt_one (mul_pos (by norm_num) (abs_pos.mpr hy)))
  have hwe : w<e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨p,q,hpH,hpq,hp,hq,hcp,hcq,hlog⟩ :=
    exists_close_positive_primes hy hw (min_le_right _ _) H
  have habs : |Real.log p-Real.log q|<e := hlog.trans_lt hwe
  have hgp : 3/4<g (Real.log p-Real.log q) := hs (by simpa [Real.dist_eq] using habs)
  have hgq : 3/4<g (Real.log q-Real.log p) := hs (by
    simpa [Real.dist_eq,abs_sub_comm] using habs)
  refine ⟨p,q,hpH,hpq,hp,hq,?_⟩
  rw [twoPrimeDamped_eq hp hq hpq.ne]
  norm_num [Complex.mul_re,phase_re]
  linarith

/-- Every actual zero ordinate is covered by the same continuous-
kernel obstruction, independent of its multiplicity or exposure. -/
theorem exists_negative_continuous_damping_at_zero (rho : NontrivialZetaZero)
    {g : ℝ → ℝ} (hg : ContinuousAt g 0) (hg0 : g 0=1) (H : ℕ) :
    ∃ p q : ℕ,H<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      (twoPrimeDamped g rho.1.im p q).re≤-(1 : ℝ) :=
  exists_negative_continuous_damping hg hg0
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho) H

end
end RiemannGaussian.ArithmeticOperatorGaussianCoprimeAudit
