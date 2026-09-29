/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPrimeError

/-!
# Arithmetic prime discrepancy through both Riesz cutoffs

The actual prime tail and its signed smooth tail are subtracted before
forming the cutoff energy.  The arithmetic error pays the common log-span,
not the Riesz length or the number of divisor crossings.  The smooth term
is retained, not declared small.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszDiscrepancyEnergy
open Real ZetaRieszPrimeTailEnergy

/-- The exact signed density tail, with both exterior endpoints retained. -/
def smoothTail (F : ℝ → ℝ) (a b L t : ℝ) : ℝ :=
  (Ioc (L-b) L).indicator (fun t =>
    ∫ x in exp (max a (L-t))..exp b, F (log x)/(x*log x)) t

/-- The difference between the literal prime tail and its smooth tail. -/
def errorTail (F : ℝ → ℝ) (a b L t : ℝ) : ℝ :=
  tail ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
    (fun p => F (log p)/(p : ℝ)) (fun p => log p) L t-smoothTail F a b L t

private theorem smooth_primitive_continuous (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (L : ℝ) :
    ContinuousOn (fun t => ∫ x in exp (max a (L-t))..exp b,
      F (log x)/(x*log x)) (Icc (L-b) L) := by
  have he : exp a ≤ exp b := exp_le_exp.mpr hab
  have hx x (hx : x ∈ Icc (exp a) (exp b)) : 0 < x := (exp_pos a).trans_le hx.1
  have hl x (hx' : x ∈ Icc (exp a) (exp b)) : 0 < log x := by
    exact ha.trans_le ((le_log_iff_exp_le (hx x hx')).mpr hx'.1)
  have hc : ContinuousOn (fun x => F (log x)/(x*log x)) (Icc (exp a) (exp b)) :=
    (hF.comp_continuousOn (continuousOn_id.log (fun x hx' => (hx x hx').ne'))).div
      (continuousOn_id.mul (continuousOn_id.log (fun x hx' => (hx x hx').ne')))
      (fun x hx' => mul_ne_zero (hx x hx').ne' (hl x hx').ne')
  have hi : IntegrableOn (fun x => F (log x)/(x*log x)) (uIcc (exp a) (exp b)) := by
    rw [uIcc_of_le he]
    exact hc.integrableOn_Icc
  have hp := intervalIntegral.continuousOn_primitive_interval_left hi
  rw [uIcc_of_le he] at hp
  apply hp.comp (by fun_prop)
  intro t ht
  exact ⟨exp_le_exp.mpr (le_max_left _ _),
    exp_le_exp.mpr (max_le hab (by linarith [ht.1]))⟩

/-- A continuous signed prime profile has an integrable compact cutoff tail. -/
theorem smoothTail_integrable (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (L : ℝ) :
    Integrable (smoothTail F a b L) :=
  (((smooth_primitive_continuous F hF ha hab L).integrableOn_Icc).mono_set
    Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

/-- The signed compact density tail has integrable squared modulus. -/
theorem smoothTail_square_integrable (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (L : ℝ) :
    Integrable (fun t => smoothTail F a b L t^2) := by
  have hi : Integrable ((Ioc (L-b) L).indicator (fun t : ℝ =>
      (∫ x in exp (max a (L-t))..exp b, F (log x)/(x*log x))^2)) :=
    ((((smooth_primitive_continuous F hF ha hab L).pow 2).integrableOn_Icc (μ := volume)).mono_set
    Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  convert hi using 1
  ext t
  simp only [smoothTail,indicator_apply]
  split_ifs <;> simp

private theorem errorTail_integrable (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (L : ℝ) :
    Integrable (errorTail F a b L) := by
  apply Integrable.sub _ (smoothTail_integrable F hF ha hab L)
  exact integrable_finsetSum _ (fun p _ =>
    (integrableOn_const (μ := volume) (s := Ioc (L-log p) L)
      (C := F (log p)/(p : ℝ)) (hs := by simp)).integrable_indicator measurableSet_Ioc)

private theorem errorTail_square_integrable (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (L : ℝ) :
    Integrable (fun t => errorTail F a b L t^2) := by
  have hp : MemLp (tail ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
      (fun p => F (log p)/(p : ℝ)) (fun p => log p) L) 2 volume :=
    memLp_finsetSum _ (fun p _ => memLp_indicator_const 2 measurableSet_Ioc
      (F (log p)/(p : ℝ)) (Or.inr (by simp)))
  have hs : MemLp (smoothTail F a b L) 2 volume :=
    (memLp_two_iff_integrable_sq
      (smoothTail_integrable F hF ha hab L).aestronglyMeasurable).mpr
        (smoothTail_square_integrable F hF ha hab L)
  exact (hp.sub hs).integrable_sq

private theorem errorTail_eq_zero (F : ℝ → ℝ) {a b L t : ℝ}
    (ht : t ∉ Ioc (L-b) L) : errorTail F a b L t = 0 := by
  rw [errorTail,smoothTail,indicator_of_notMem ht,sub_zero]
  apply Finset.sum_eq_zero
  intro p hp
  apply indicator_of_notMem
  intro h
  apply ht
  exact ⟨by linarith [(prime_interval_logs hp).2,h.1],h.2⟩

private theorem errorTail_eq_interval (F : ℝ → ℝ) {a b L t : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (ht : t ∈ Ioc (L-b) L) :
    errorTail F a b L t =
      (∑ p ∈ (Finset.Ioc ⌊exp (max a (L-t))⌋₊ ⌊exp b⌋₊).filter Nat.Prime,
        F (log p)/(p : ℝ))-
      (∫ x in Ioc (exp (max a (L-t))) (exp b), F (log x)/(x*log x)) := by
  have hDb : max a (L-t) ≤ b := max_le hab (by linarith [ht.1])
  rw [errorTail,smoothTail,indicator_of_mem ht,
    intervalIntegral.integral_of_le (exp_le_exp.mpr hDb)]
  congr 1
  by_cases hat : a ≤ L-t
  · rw [max_eq_right hat]
    convert tail_eq_prime_interval hat (ha.trans hat) L (fun p => F (log p)/(p : ℝ)) using 1
    congr 1
    ring
  · have hta : L-a < t := by linarith [lt_of_not_ge hat]
    rw [max_eq_left (le_of_not_ge hat)]
    apply Finset.sum_congr rfl
    intro p hp
    exact indicator_of_mem (show t ∈ Ioc (L-log p) L from
      ⟨by linarith [(prime_interval_logs hp).1],ht.2⟩) _

/-- Arithmetic price for a single joined interval, including its endpoints. -/
def intervalError (a b W V : ℝ) : ℝ := 5*(2*W+(V+2*W)*(b-a))/a^3

private theorem errorTail_bound (T : ℝ) (hT : 5000 ≤ T)
    (hprime : ∀ (F G : ℝ → ℝ) (c a b W V : ℝ),
      (∀ t, HasDerivAt F (G t) t) → Continuous G →
      T ≤ a → a ≤ b → 0 ≤ W → 0 ≤ V →
      (∀ t ∈ Icc (a+c) (b+c), |F t| ≤ W) →
      (∀ t ∈ Icc (a+c) (b+c), |G t| ≤ V) →
      |(∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime,
        F (log p+c)/(p : ℝ))-
        (∫ x in Ioc (exp a) (exp b), F (log x+c)/(x*log x))| ≤
        5*(2*W+(V+2*W)*(b-a))/a^3)
    (F G : ℝ → ℝ) (hF : ∀ t, HasDerivAt F (G t) t) (hG : Continuous G)
    {a b W V : ℝ} (ha : T ≤ a) (hab : a ≤ b) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hFW : ∀ t ∈ Icc a b, |F t| ≤ W) (hGV : ∀ t ∈ Icc a b, |G t| ≤ V)
    (L t : ℝ) : |errorTail F a b L t| ≤ intervalError a b W V := by
  have ha0 : 0 < a := by linarith
  have hba : 0 ≤ b-a := sub_nonneg.mpr hab
  have hcost : 0 ≤ intervalError a b W V := by dsimp [intervalError]; positivity
  by_cases ht : t ∈ Ioc (L-b) L
  · let D := max a (L-t)
    have haD : a ≤ D := le_max_left _ _
    have hDb : D ≤ b := max_le hab (by linarith [ht.1])
    have hD0 : 0 < D := ha0.trans_le haD
    have hh := hprime F G 0 D b W V hF hG (ha.trans haD) hDb hW hV
      (fun x hx => hFW x ⟨haD.trans (by simpa using hx.1),by simpa using hx.2⟩)
      (fun x hx => hGV x ⟨haD.trans (by simpa using hx.1),by simpa using hx.2⟩)
    simp only [add_zero] at hh
    rw [errorTail_eq_interval F ha0.le hab ht]
    apply hh.trans
    dsimp [intervalError]
    have hwidth : (V+2*W)*(b-D) ≤ (V+2*W)*(b-a) :=
      mul_le_mul_of_nonneg_left (by linarith : b-D ≤ b-a) (by positivity)
    apply (div_le_div_of_nonneg_right (by linarith :
      5*(2*W+(V+2*W)*(b-D)) ≤ 5*(2*W+(V+2*W)*(b-a)))
      (pow_nonneg hD0.le 3)).trans
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha0 3)
      (pow_le_pow_left₀ ha0.le haD 3)
  · rw [errorTail_eq_zero F ht,abs_zero]
    exact hcost

private theorem square_integral (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t^2) volume a b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, f t^2) := by
  let m := (∫ t in a..b, f t)/(b-a)
  have hm : m*(b-a) = ∫ t in a..b, f t := by
    dsimp [m]
    exact div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hv := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun t => sq_nonneg (f t-m))
  have he t : (f t-m)^2 = f t^2-2*m*f t+m^2 := by ring
  simp_rw [he] at hv
  rw [intervalIntegral.integral_add (hf2.sub (hf.const_mul (2*m))) intervalIntegrable_const,
    intervalIntegral.integral_sub hf2 (hf.const_mul (2*m)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hv
  simp only [smul_eq_mul] at hv
  have h := mul_nonneg (sub_pos.mpr hab).le hv
  nlinarith only [h,hm]

/-- Logarithmic cutoff increments cost at most their continuous squared energy. -/
theorem logarithmic_energy (f : ℝ → ℝ) (hf : Integrable f)
    (hf2 : Integrable (fun t => f t^2)) (R : ℕ) :
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*
      (∫ t in log k..log (k+1 : ℕ), f t)^2) ≤ ∫ t : ℝ, f t^2 := by
  have hp k (hk : k ∈ Finset.Icc 1 R) :
      (k : ℝ)*(∫ t in log k..log (k+1 : ℕ), f t)^2 ≤
        ∫ t in log k..log (k+1 : ℕ), f t^2 := by
    have hkN : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hkN
    have hk1 : (0 : ℝ) < (k+1 : ℕ) := by positivity
    have hab : log k < log (k+1 : ℕ) := log_lt_log hk0 (by norm_cast; omega)
    have hlog : (k : ℝ)*(log (k+1 : ℕ)-log k) ≤ 1 := by
      have h := log_le_sub_one_of_pos (div_pos hk1 hk0)
      rw [log_div hk1.ne' hk0.ne'] at h
      have hh := mul_le_mul_of_nonneg_left h hk0.le
      have he : (k : ℝ)*(((k+1 : ℕ) : ℝ)/k-1) = 1 := by
        push_cast
        field_simp
        ring
      exact hh.trans_eq he
    have hs := mul_le_mul_of_nonneg_left
      (square_integral f hab hf.intervalIntegrable hf2.intervalIntegrable) hk0.le
    have hpos : 0 ≤ ∫ t in log k..log (k+1 : ℕ), f t^2 :=
      intervalIntegral.integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
    exact hs.trans (by nlinarith only [mul_le_mul_of_nonneg_right hlog hpos])
  apply (Finset.sum_le_sum hp).trans
  have he := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun k : ℕ => log k) (m := 1) (n := R+1) (by omega)
    (fun k _ => hf2.intervalIntegrable)
  rw [Finset.Ico_add_one_right_eq_Icc,Nat.cast_one,log_one] at he
  rw [he,intervalIntegral.integral_of_le (log_natCast_nonneg (R+1))]
  exact setIntegral_le_integral hf2 (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

/-- The smooth increment across a divisor cutoff keeps the entire signed
prime-density tail.  It is not an absolute prime-density majorant. -/
def smoothDifference (F : ℝ → ℝ) (a b L : ℝ) (k : ℕ) : ℝ :=
  ∫ t in log k..log (k+1 : ℕ), smoothTail F a b L t

/-- The actual prime discrepancy passes through BOTH Riesz cutoffs with
one joint squared-energy price.  The start T is proved but unevaluated.
There is no Riesz-length, divisor-count or internal-period multiplier. -/
theorem eventually_profile_error_energy :
    ∃ T : ℝ, 5000 ≤ T ∧ ∀ (F G : ℝ → ℝ) (a b W V L : ℝ) (R : ℕ),
      (∀ t, HasDerivAt F (G t) t) → Continuous G →
      T ≤ a → a ≤ b → 0 ≤ W → 0 ≤ V →
      (∀ t ∈ Icc a b, |F t| ≤ W) → (∀ t ∈ Icc a b, |G t| ≤ V) →
      let f := profile ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
        (fun p => F (log p)/(p : ℝ)) (fun p => log p) L;
      (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*
        (f k-f (k+1)-smoothDifference F a b L k)^2) ≤ b*(intervalError a b W V)^2 := by
  obtain ⟨T,hT,hprime⟩ := ZetaRieszJointPrimeError.eventually_signed_profile_error
  refine ⟨T,hT,fun F G a b W V L R hF hG ha hab hW hV hFW hGV => ?_⟩
  dsimp only
  have ha0 : 0 < a := by linarith
  have hb0 : 0 ≤ b := ha0.le.trans hab
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)
  have hi := errorTail_integrable F hFc ha0 hab L
  have hi2 := errorTail_square_integrable F hFc ha0 hab L
  have hbnd := errorTail_bound T hT hprime F G hF hG ha hab hW hV hFW hGV L
  have hcost : 0 ≤ intervalError a b W V := (abs_nonneg _).trans (hbnd 0)
  have hident k (hk : k ∈ Finset.Icc 1 R) :
      profile ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
        (fun p => F (log p)/(p : ℝ)) (fun p => log p) L k-
      profile ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
        (fun p => F (log p)/(p : ℝ)) (fun p => log p) L (k+1)-
      smoothDifference F a b L k = ∫ t in log k..log (k+1 : ℕ), errorTail F a b L t := by
    rw [profile_difference _ _ _ L (fun p _ => log_natCast_nonneg p)
      (Finset.mem_Icc.mp hk).1]
    have hitail := integrable_finsetSum
      ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime) (fun p _ =>
        (integrableOn_const (μ := volume) (s := Ioc (L-log p) L)
          (C := F (log p)/(p : ℝ)) (hs := by simp)).integrable_indicator measurableSet_Ioc)
    exact (intervalIntegral.integral_sub hitail.intervalIntegrable
      (smoothTail_integrable F hFc ha0 hab L).intervalIntegrable).symm
  have heq : (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*
      (profile ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
        (fun p => F (log p)/(p : ℝ)) (fun p => log p) L k-
      profile ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
        (fun p => F (log p)/(p : ℝ)) (fun p => log p) L (k+1)-
      smoothDifference F a b L k)^2) =
      ∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(∫ t in log k..log (k+1 : ℕ), errorTail F a b L t)^2 :=
    Finset.sum_congr rfl (fun k hk => by rw [hident k hk])
  rw [heq]
  apply (logarithmic_energy _ hi hi2 R).trans
  let H := (Ioc (L-b) L).indicator (fun _ : ℝ => (intervalError a b W V)^2)
  have hH : Integrable H := (integrableOn_const (μ := volume)
    (s := Ioc (L-b) L) (C := (intervalError a b W V)^2)
    (hs := by simp)).integrable_indicator measurableSet_Ioc
  have he t : errorTail F a b L t^2 ≤ H t := by
    by_cases ht : t ∈ Ioc (L-b) L
    · dsimp only [H]
      rw [indicator_of_mem ht]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hcost).mpr (hbnd t)
    · dsimp only [H]
      rw [indicator_of_notMem ht,errorTail_eq_zero F ht]
      norm_num
  apply (integral_mono hi2 hH he).trans_eq
  dsimp only [H]
  rw [integral_indicator_const _ measurableSet_Ioc,Real.volume_real_Ioc,
    show L-(L-b)=b by ring,max_eq_left hb0]
  rfl

/-- The literal prime sum containing the two correlated Riesz responses. -/
def primeResponse (F : ℝ → ℝ) (a b L : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime,
    F (log p)/(p : ℝ)*
      (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-log p) n)

/-- The signed smooth response, integrated through the same divisor-cutoff
increments as the literal prime sum.  Every endpoint and subset sign remains. -/
def smoothResponse (F : ℝ → ℝ) (a b L : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊exp L⌋₊, smoothDifference F a b L k*
    (∑ d ∈ Finset.Icc 1 k, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0)

private theorem abel_profile (R : ℕ) (f z : ℕ → ℝ) (hend : f (R+1)=0) :
    (∑ d ∈ Finset.Icc 1 R, f d*z d) =
      ∑ k ∈ Finset.Icc 1 R, (f k-f (k+1))*(∑ d ∈ Finset.Icc 1 k, z d) := by
  have htail d (hd : d ≤ R+1) : (∑ k ∈ Finset.Icc d R, (f k-f (k+1))) = f d := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    calc
      _ = -(∑ k ∈ Finset.Ico d (R+1), (f (k+1)-f k)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = f d := by rw [Finset.sum_Ico_sub f hd,hend]; ring
  calc
    _ = ∑ d ∈ Finset.Icc 1 R, ∑ k ∈ Finset.Icc d R, (f k-f (k+1))*z d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_mul,htail d (by have := (Finset.mem_Icc.mp hd).2; omega)]
    _ = _ := by
      have h := Finset.sum_Ico_Ico_comm 1 (R+1) (fun d k => (f k-f (k+1))*z d)
      simp only [Finset.Ico_add_one_right_eq_Icc,← Finset.mul_sum] at h
      exact h

/-- Exact finite Abel identity for the arithmetic error, retaining both
literal Riesz cutoffs.  No smooth term or cutoff boundary is omitted. -/
theorem response_error_eq_profile (F : ℝ → ℝ) (a b L : ℝ) {n : ℕ} (hn : 0 < n) :
    let f := profile ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
      (fun p => F (log p)/(p : ℝ)) (fun p => log p) L;
    primeResponse F a b L n-smoothResponse F a b L n =
      ∑ k ∈ Finset.Icc 1 ⌊exp L⌋₊, (f k-f (k+1)-smoothDifference F a b L k)*
        (∑ d ∈ Finset.Icc 1 k, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
  let R := ⌊exp L⌋₊
  let P := (Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime
  let f := profile P (fun p => F (log p)/(p : ℝ)) (fun p => log p) L
  have hR : exp L < R+1 := Nat.lt_floor_add_one (exp L)
  have hf : f (R+1)=0 := profile_endpoint P _ _ L R hR (fun p _ => log_natCast_nonneg p)
  have he : primeResponse F a b L n =
      ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
    unfold primeResponse
    have hr (p : ℕ) := ZetaRieszCutoffMean.riesz_difference_eq_prefix R
      (sub_le_self L (log_natCast_nonneg p)) hR hn
    simp_rw [hr,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    simp only [f,profile,P,Finset.sum_mul,mul_assoc]
  rw [he,abel_profile R f _ hf,smoothResponse,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- All squarefree cofactor counts obey the sharper JOINT arithmetic-error
mean.  The prime-density response remains signed and explicit; this is not
a source-scale replacement of the arithmetic carrier by density. -/
theorem exists_response_error_mean :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (F G : ℝ → ℝ) (a b W V L : ℝ) (X : ℕ) (S : Finset ℕ),
      (∀ t, HasDerivAt F (G t) t) → Continuous G →
      T ≤ a → a ≤ b → 0 ≤ W → 0 ≤ V →
      (∀ t ∈ Icc a b, |F t| ≤ W) → (∀ t ∈ Icc a b, |G t| ≤ V) →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (primeResponse F a b L n-smoothResponse F a b L n)^2) ≤
        E*X*b*(intervalError a b W V)^2 := by
  obtain ⟨T,hT,henergy⟩ := eventually_profile_error_energy
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_signed_profile_mean
  refine ⟨T,E,hT,hE,fun F G a b W V L X S hF hG ha hab hW hV hFW hGV hS hSF => ?_⟩
  let f := profile ((Finset.Ioc ⌊exp a⌋₊ ⌊exp b⌋₊).filter Nat.Prime)
    (fun p => F (log p)/(p : ℝ)) (fun p => log p) L
  have he n (hn : n ∈ S) := response_error_eq_profile F a b L
    (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega : 0 < n)
  have hs := hmean X ⌊exp L⌋₊ S (fun k => f k-f (k+1)-smoothDifference F a b L k) hS hSF
  have hb := henergy F G a b W V L ⌊exp L⌋₊ hF hG ha hab hW hV hFW hGV
  calc
    _ = _ := Finset.sum_congr rfl (fun n hn => congrArg (fun z : ℝ => z^2) (he n hn))
    _ ≤ E*X*(b*(intervalError a b W V)^2) := hs.trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = _ := by ring

/-- Both signed bounds for the actual prime-minus-smooth Riesz response,
with arbitrary signed cofactor weights and no count ceiling.  Only the
joint discrepancy is priced; the remaining smooth carrier is NOT paid. -/
theorem exists_joint_response_error_bounds :
    ∃ T E : ℝ, 5000 ≤ T ∧ 0 < E ∧
      ∀ (F G : ℝ → ℝ) (a b W V L : ℝ) (X : ℕ) (S : Finset ℕ) (w : ℕ → ℝ),
      (∀ t, HasDerivAt F (G t) t) → Continuous G →
      T ≤ a → a ≤ b → 0 ≤ W → 0 ≤ V →
      (∀ t ∈ Icc a b, |F t| ≤ W) → (∀ t ∈ Icc a b, |G t| ≤ V) →
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      let J := ∑ n ∈ S, w n*primeResponse F a b L n;
      let M := ∑ n ∈ S, w n*smoothResponse F a b L n;
      let K := sqrt ((∑ n ∈ S, (w n)^2)*E*X*b)*intervalError a b W V;
      M-K ≤ J ∧ J ≤ M+K := by
  obtain ⟨T,E,hT,hE,hmean⟩ := exists_response_error_mean
  refine ⟨T,E,hT,hE,fun F G a b W V L X S w hF hG ha hab hW hV hFW hGV hS hSF => ?_⟩
  dsimp only
  have hb0 : 0 ≤ b := by linarith
  have hba : 0 ≤ b-a := sub_nonneg.mpr hab
  have ha0 : 0 < a := by linarith
  have hcost : 0 ≤ intervalError a b W V := by dsimp [intervalError]; positivity
  have hm := hmean F G a b W V L X S hF hG ha hab hW hV hFW hGV hS hSF
  have h := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => primeResponse F a b L n-smoothResponse F a b L n)).trans
      (mul_le_mul_of_nonneg_left hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hk : 0 ≤ (∑ n ∈ S, (w n)^2)*E*X*b := by positivity
  have he : (∑ n ∈ S, w n*(primeResponse F a b L n-smoothResponse F a b L n)) =
      (∑ n ∈ S, w n*primeResponse F a b L n)-(∑ n ∈ S, w n*smoothResponse F a b L n) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [he] at h
  have hsq := Real.sq_sqrt hk
  have hsmall : |(∑ n ∈ S, w n*primeResponse F a b L n)-
      (∑ n ∈ S, w n*smoothResponse F a b L n)| ≤
        sqrt ((∑ n ∈ S, (w n)^2)*E*X*b)*intervalError a b W V := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (sqrt_nonneg _) hcost)).mp
    rw [sq_abs,mul_pow,hsq]
    nlinarith only [h]
  obtain ⟨hl,hu⟩ := abs_le.mp hsmall
  constructor <;> linarith

end RiemannGaussian.ZetaRieszDiscrepancyEnergy
