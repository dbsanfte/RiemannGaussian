/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorNormalizedRamanujanAudit
import RiemannGaussian.ArithmeticOperatorRamanujanFreedom
import RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit

/-!
# Critical normalized codes cannot be paid uniformly

The sub-source theorem does not extend to all centered codes at or above
the source exponent. A bounded, normalized, finite prime-modulus code
undoes the full prime phase on an actual prime band. Its unit-modulus
centering coefficient has norm at most one half. When the cutoff lies
below the square of the band, every proper power is excluded EXACTLY
by its physical support, not dropped as an error. The observation is
the positive actual prime logarithmic mass. The PNT is used only for
this counterexample lower bound, never for a signed upper estimate.

This closes a UNIFORM all-code payment shortcut; it does not refute a
particular arithmetically restricted code or prove an RH source theorem.
-/

namespace RiemannGaussian.ArithmeticOperatorCriticalRamanujanAudit
noncomputable section
open ArithmeticOperatorRamanujanAudit ArithmeticOperatorRamanujanFreedom
open ArithmeticOperatorNormalizedRamanujanAudit ArithmeticOperatorCrtBoundaryAudit
open ArithmeticOperatorRamanujanPayment
open SuzukiCarryCorrelation Filter
open scoped BigOperators Topology ComplexConjugate

/-- The exact inverse of the retained fixed-height prime phase. -/
def bandProfile (y : ℝ) (p : ℕ) : ℂ := conj (primePhase y p)

/-- Include the unit modulus: principal centering is part of the code. -/
def bandModuli (H : ℕ) : Finset ℕ := insert 1 (primeBand H 2 3)

/-- A normalized coefficient budget, including its exact unit centering. -/
def bandEta (H : ℕ) (y : ℝ) (q : ℕ) : ℂ :=
  if q = 1 then ∑ p ∈ primeBand H 2 3, bandProfile y p/(p : ℂ)
  else bandProfile y q

theorem bandProfile_norm (y : ℝ) (p : ℕ) : ‖bandProfile y p‖ = 1 := by
  simp only [bandProfile,Complex.norm_conj,norm_primePhase]

theorem bandProfile_phase (y : ℝ) (p : ℕ) :
    bandProfile y p*primePhase y p = 1 := by
  rw [bandProfile,←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,
    norm_primePhase]
  norm_num

private theorem band_prime {H p : ℕ} (hp : p ∈ primeBand H 2 3) : p.Prime :=
  (Finset.mem_filter.mp hp).2

private theorem band_bounds {H p : ℕ} (hp : p ∈ primeBand H 2 3) :
    2*H<p ∧ p≤3*H := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1

/-- The exact normalization reproduces the existing centered code. -/
theorem normalizedCoefficient_band (H : ℕ) (y : ℝ) :
    normalizedCoefficient (bandEta H y) =
      weightedCoefficients (primeBand H 2 3) (bandProfile y) := by
  funext q
  unfold normalizedCoefficient bandEta weightedCoefficients
  split_ifs with hq
  · simp [hq]
  · rfl

theorem band_principal_zero (H : ℕ) (y : ℝ) :
    principalCoefficient (bandModuli H) (normalizedCoefficient (bandEta H y)) = 0 := by
  rw [normalizedCoefficient_band]
  exact principalCoefficient_weighted_eq_zero (fun _ hp => band_prime hp) _

theorem bandModuli_subset {H : ℕ} (hH : 0<H) :
    bandModuli H ⊆ Finset.Icc 1 (3*H) := by
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl|hq
  · exact Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
  · have hh := band_bounds hq
    exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩

/-- Principal centering also respects the bounded normalized budget. -/
theorem bandEta_one_le {H : ℕ} (hH : 0<H) (y : ℝ) :
    ‖bandEta H y 1‖ ≤ 1/2 := by
  have hcard : (primeBand H 2 3).card ≤ H := by
    apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
    simp only [Nat.card_Ioc]
    omega
  have hH0 : (0 : ℝ)<H := by exact_mod_cast hH
  simp only [bandEta,ite_true]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ primeBand H 2 3, 1/(2*(H : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_div,bandProfile_norm,Complex.norm_natCast]
      have hh : 2*(H : ℝ)≤p := by exact_mod_cast (band_bounds hp).1.le
      exact one_div_le_one_div_of_le (by positivity) hh
    _ = ((primeBand H 2 3).card : ℝ)/(2*(H : ℝ)) := by simp [div_eq_mul_inv]
    _ ≤ (H : ℝ)/(2*(H : ℝ)) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = 1/2 := by field_simp

theorem bandEta_le_one {H : ℕ} (hH : 0<H) (y : ℝ) (q : ℕ) :
    ‖bandEta H y q‖ ≤ 1 := by
  by_cases hq : q=1
  · rw [hq]
    exact (bandEta_one_le hH y).trans (by norm_num)
  · simp only [bandEta,hq,ite_false,bandProfile_norm,le_refl]

/-- Physical support, not a prime-power approximation: no proper power
of an admitted band prime can occur below this cutoff. -/
theorem band_primePower_order_one {H X p k : ℕ}
    (hp : p ∈ primeBand H 2 3) (hk : 0<k) (hpX : p^k≤X)
    (hX : X<(2*H)^2) : k=1 := by
  have hp0 := (band_prime hp).pos
  by_contra hh
  have hk2 : 2≤k := by omega
  have hlow : (2*H)^2≤p^2 := Nat.pow_le_pow_left (band_bounds hp).1.le 2
  have hpow : p^2≤p^k := Nat.pow_le_pow_right hp0 hk2
  exact (not_lt_of_ge (hlow.trans (hpow.trans hpX))) hX

/-- Every Mangoldt label and both physical endpoints have been retained.
The complete observation is EXACTLY positive ordinary-prime log mass. -/
theorem band_observation_eq {H X : ℕ} (hX0 : 3*H≤X) (hX : X<(2*H)^2)
    (y : ℝ) :
    codeObservation (bandModuli H) (normalizedCoefficient (bandEta H y)) X y =
      (logMass H 2 3 : ℂ) := by
  classical
  rw [normalizedCoefficient_band]
  unfold codeObservation bandModuli
  have he (n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
      (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n*
        code (insert 1 (primeBand H 2 3))
          (weightedCoefficients (primeBand H 2 3) (bandProfile y)) n =
      if n ∈ primeBand H 2 3 then (Real.log n : ℂ) else 0 := by
    rw [code_eq_weightedCode (fun _ hp => band_prime hp)]
    by_cases hz : ArithmeticFunction.vonMangoldt n=0
    · have hnot : n ∉ primeBand H 2 3 := by
        intro hh
        exact (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr
          (isPrimePow_nat_iff n |>.mpr ⟨n,1,band_prime hh,by omega,by simp⟩)) hz
      simp [hz,hnot]
    · obtain ⟨p,k,hp,hk,hpk⟩ := (isPrimePow_nat_iff n).mp
        (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hz)
      rw [←hpk,weightedCode_prime_pow (fun _ hh => band_prime hh) _ hp hk]
      by_cases hpB : p ∈ primeBand H 2 3
      · have hk1 := band_primePower_order_one hpB hk
          (by simpa [hpk] using (Finset.mem_Icc.mp hn).2) hX
        subst k
        simp only [pow_one,ite_eq_left hpB,ArithmeticFunction.vonMangoldt_apply_prime hp]
        rw [mul_assoc,mul_comm (primePhase y p),bandProfile_phase,mul_one]
      · have hnB : p^k ∉ primeBand H 2 3 := by
          intro hh
          have hnP := band_prime hh
          have hdiv := dvd_pow_self p hk.ne'
          have hpp : p=p^k := ((Nat.dvd_prime hnP).mp hdiv).resolve_left hp.ne_one
          exact hpB (hpp.symm ▸ hh)
        simp [hpB,hnB]
  simp_rw [Finset.sum_congr rfl he]
  rw [←Finset.sum_filter]
  have hfilter : (Finset.Icc 1 X).filter (fun n => n ∈ primeBand H 2 3) =
      primeBand H 2 3 := by
    ext n
    simp only [Finset.mem_filter,and_iff_right_iff_imp]
    intro hn
    exact Finset.mem_Icc.mpr ⟨(band_prime hn).pos,(band_bounds hn).2.trans hX0⟩
  rw [hfilter]
  simp only [logMass,Complex.ofReal_sum]

/-- The centered contrast is the SAME literal observation; no density
approximation or missing prime-power payment is involved. -/
theorem band_contrast_eq {H X : ℕ} (hX0 : 3*H≤X) (hX : X<(2*H)^2)
    (y : ℝ) : contrast (bandModuli H) (bandEta H y) X y = (logMass H 2 3 : ℂ) := by
  rw [contrast,band_principal_zero,zero_mul,sub_zero,band_observation_eq hX0 hX]

private theorem logMass_nonneg (H : ℕ) : 0≤logMass H 2 3 :=
  Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)

/-- Constant factors in the physical cutoff do not alter its exponent. -/
def dyadicContrast (A B J : ℕ) (y : ℝ) : ℂ :=
  contrast (bandModuli (2^(B*J))) (bandEta (2^(B*J)) y) (4*2^(A*J)) y

private theorem dyadic_physical {A B J : ℕ} (hBA : B≤A) (hAB : A<2*B)
    (hJ : 0<J) :
    3*2^(B*J)≤4*2^(A*J) ∧ 4*2^(A*J)<(2*2^(B*J))^2 := by
  have hle : 2^(B*J)≤2^(A*J) :=
    Nat.pow_le_pow_right (by omega : 0<(2 : ℕ)) (Nat.mul_le_mul_right J hBA)
  have hlt : 2^(A*J)<(2^(B*J))^2 := by
    rw [←pow_mul]
    apply Nat.pow_lt_pow_right (by omega : 1<(2 : ℕ))
    nlinarith only [hAB,hJ]
  constructor
  · omega
  · nlinarith only [hlt]

private theorem scaling_identity (A B J : ℕ) (beta : ℝ) :
    Real.exp (-(A : ℝ)*beta*Real.log 2)^J*((2^(B*J) : ℕ) : ℝ) =
      Real.exp (((B : ℝ)-(A : ℝ)*beta)*Real.log 2)^J := by
  simp only [Nat.cast_pow,Nat.cast_ofNat,pow_mul]
  rw [←mul_pow]
  congr 1
  rw [show (2 : ℝ)^B=Real.exp ((B : ℝ)*Real.log 2) by
    rw [←Real.log_pow,Real.exp_log (by positivity)],←Real.exp_add]
  congr 1
  ring

/-- Exact cofinal source normalization, not a floating prime-band model. -/
theorem eventually_scaled_norm_eq {A B : ℕ} (hBA : B≤A) (hAB : A<2*B)
    (beta y : ℝ) :
    ∀ᶠ J : ℕ in atTop,
      ‖(Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*dyadicContrast A B J y‖ =
        Real.exp (((B : ℝ)-(A : ℝ)*beta)*Real.log 2)^J*
          (logMass (2^(B*J)) 2 3/((2^(B*J) : ℕ) : ℝ)) := by
  filter_upwards [eventually_gt_atTop 0] with J hJ
  obtain ⟨hX0,hX⟩ := dyadic_physical hBA hAB hJ
  rw [dyadicContrast,band_contrast_eq hX0 hX,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le,Complex.norm_real,
    Real.norm_of_nonneg (logMass_nonneg _)]
  have hH : (((2^(B*J) : ℕ) : ℝ))≠0 := by positivity
  rw [←scaling_identity]
  field_simp

/-- At and above the source exponent, a bounded normalized centered
code retains at least one half unit of source-normalized ACTUAL mass. -/
theorem eventually_scaled_norm_lower {A B : ℕ} (hBA : B≤A) (hAB : A<2*B)
    (beta y : ℝ) :
    ∀ᶠ J : ℕ in atTop,
      (1/2 : ℝ)*Real.exp (((B : ℝ)-(A : ℝ)*beta)*Real.log 2)^J ≤
        ‖(Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*dyadicContrast A B J y‖ := by
  have hB : 0<B := by omega
  have hindex : Tendsto (fun J : ℕ => B*J) atTop atTop := by
    exact tendsto_atTop_mono (fun J => by
      change J≤B*J
      have hB1 : 1≤B := hB
      nlinarith only [hB1]) tendsto_id
  have hm : Tendsto (fun J : ℕ =>
      logMass (2^(B*J)) 2 3/((2^(B*J) : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,Nat.cast_ofNat,show (3 : ℝ)-2=1 by norm_num] using
      (tendsto_logMass_dyadic (a := 2) (b := 3) (by omega) (by omega)).comp hindex
  have hm0 : ∀ᶠ J : ℕ in atTop,
      (1/2 : ℝ)<logMass (2^(B*J)) 2 3/((2^(B*J) : ℕ) : ℝ) :=
    hm.eventually (lt_mem_nhds (show (1/2 : ℝ)<1 by norm_num))
  filter_upwards [eventually_scaled_norm_eq hBA hAB beta y,hm0] with J he hmJ
  rw [he,mul_comm (1/2 : ℝ)]
  exact mul_le_mul_of_nonneg_left hmJ.le (pow_nonneg (Real.exp_pos _).le _)

/-- The critical endpoint has limit one: uniform source-small payment
fails even when the modulus and source exponents agree EXACTLY. -/
theorem tendsto_critical_scaled_norm {A B : ℕ} (hBA : B≤A) (hAB : A<2*B)
    {beta : ℝ} (hcritical : (B : ℝ)=(A : ℝ)*beta) (y : ℝ) :
    Tendsto (fun J : ℕ =>
      ‖(Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*dyadicContrast A B J y‖)
      atTop (𝓝 1) := by
  have hindex : Tendsto (fun J : ℕ => B*J) atTop atTop := by
    exact tendsto_atTop_mono (fun J => by
      change J≤B*J
      have hB1 : 1≤B := by omega
      nlinarith only [hB1]) tendsto_id
  have hm : Tendsto (fun J : ℕ =>
      logMass (2^(B*J)) 2 3/((2^(B*J) : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,Nat.cast_ofNat,show (3 : ℝ)-2=1 by norm_num] using
      (tendsto_logMass_dyadic (a := 2) (b := 3) (by omega) (by omega)).comp hindex
  apply hm.congr'
  filter_upwards [eventually_scaled_norm_eq hBA hAB beta y] with J hJ
  simpa only [hcritical,sub_self,zero_mul,Real.exp_zero,one_pow,one_mul] using hJ.symm

/-- Above the source exponent, the counterexample grows geometrically
at rate exp((B-A*beta)*log(2)), with all phases still literal. -/
theorem tendsto_supercritical_scaled_norm {A B : ℕ} (hBA : B≤A) (hAB : A<2*B)
    {beta : ℝ} (hsource : (A : ℝ)*beta<(B : ℝ)) (y : ℝ) :
    Tendsto (fun J : ℕ =>
      ‖(Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*dyadicContrast A B J y‖)
      atTop atTop := by
  have hr : 1<Real.exp (((B : ℝ)-(A : ℝ)*beta)*Real.log 2) :=
    Real.one_lt_exp_iff.mpr (mul_pos (sub_pos.mpr hsource) (Real.log_pos (by norm_num)))
  exact tendsto_atTop_mono' atTop (eventually_scaled_norm_lower hBA hAB beta y)
    ((tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop (by norm_num : (0 : ℝ)<1/2))

/-- A uniform all-code source-o(1) estimate is false throughout the
critical/super-source window. This is NOT a source-sensitive RH estimate. -/
theorem not_tendsto_scaled_contrast {A B : ℕ} (hBA : B≤A) (hAB : A<2*B)
    {beta : ℝ} (hsource : (A : ℝ)*beta≤(B : ℝ)) (y : ℝ) :
    ¬Tendsto (fun J : ℕ =>
      (Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*dyadicContrast A B J y)
      atTop (𝓝 0) := by
  intro ht
  have hupper : ∀ᶠ J : ℕ in atTop,
      ‖(Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*dyadicContrast A B J y‖<1/2 := by
    simpa only [norm_zero] using
      ht.norm.eventually (gt_mem_nhds (show (‖(0 : ℂ)‖ : ℝ)<1/2 by norm_num))
  have hr : 1≤Real.exp (((B : ℝ)-(A : ℝ)*beta)*Real.log 2) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (sub_nonneg.mpr hsource) (Real.log_natCast_nonneg 2))
  obtain ⟨J,hJ⟩ := ((eventually_scaled_norm_lower hBA hAB beta y).and hupper).exists
  have hp : (1 : ℝ)≤Real.exp (((B : ℝ)-(A : ℝ)*beta)*Real.log 2)^J := one_le_pow₀ hr
  nlinarith only [hp,hJ.1,hJ.2]

/-- The obstruction satisfies ALL the proposed finite normalized
budget and centering premises. Extra structure on the code, not a
sharper all-code allowance, is necessary in this exponent range. -/
theorem exists_bounded_centered_counterexample {A B : ℕ}
    (hBA : B≤A) (hAB : A<2*B) {beta : ℝ}
    (hsource : (A : ℝ)*beta≤(B : ℝ)) (y : ℝ) :
    ∃ (S : ℕ → Finset ℕ) (eta : ℕ → ℕ → ℂ),
      (∀ J, S J ⊆ Finset.Icc 1 (4*2^(B*J))) ∧
      (∀ J q, ‖eta J q‖≤1) ∧
      (∀ J, principalCoefficient (S J) (normalizedCoefficient (eta J))=0) ∧
      ¬Tendsto (fun J : ℕ => (Real.exp (-(A : ℝ)*beta*Real.log 2)^J : ℂ)*
        contrast (S J) (eta J) (4*2^(A*J)) y) atTop (𝓝 0) := by
  refine ⟨fun J => bandModuli (2^(B*J)),fun J => bandEta (2^(B*J)) y,?_,?_,?_,?_⟩
  · intro J
    exact (bandModuli_subset (by positivity)).trans
      (Finset.Icc_subset_Icc le_rfl (by omega))
  · intro J q
    exact bandEta_le_one (by positivity) y q
  · intro J
    exact band_principal_zero _ y
  · exact not_tendsto_scaled_contrast hBA hAB hsource y

/-- The campaign's lower endpoint admits an EXACT critical code with
unit limiting norm, despite bounded coefficients and zero principal channel. -/
theorem tendsto_campaign_critical_norm (y : ℝ) :
    Tendsto (fun J : ℕ =>
      ‖(Real.exp (-19999*Real.log 2)^J : ℂ)*dyadicContrast 20000 19999 J y‖)
      atTop (𝓝 1) := by
  convert tendsto_critical_scaled_norm (A := 20000) (B := 19999)
    (beta := 19999/20000) (by omega) (by omega) (by norm_num) y using 1
  norm_num

/-- At full modulus scale the same legitimate codes grow at EVERY
fixed height and EVERY beta<1. No zero or exposure hypothesis enters. -/
theorem tendsto_campaign_full_scale_norm {beta : ℝ} (hbeta : beta<1) (y : ℝ) :
    Tendsto (fun J : ℕ =>
      ‖(Real.exp (-beta*Real.log 2)^J : ℂ)*dyadicContrast 1 1 J y‖)
      atTop atTop := by
  simpa only [Nat.cast_one,one_mul,neg_mul] using
    tendsto_supercritical_scaled_norm (A := 1) (B := 1) (by omega) (by omega)
      (by simpa using hbeta) y

end
end RiemannGaussian.ArithmeticOperatorCriticalRamanujanAudit
