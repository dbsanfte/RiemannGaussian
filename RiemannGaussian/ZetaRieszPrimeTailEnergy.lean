/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedCutoffEnergy
import RiemannGaussian.ZetaRieszQuantitativePrimePeriod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Signed prime-tail energy pays the coupled cutoff response

The complete signed prime tails are integrated before taking their squared
energy. This pays all moving hinge crossings with a bound independent of the
Riesz cutoff length. The actual prime-period estimates discharge the prime
counting input; no smooth prime-density replacement is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPrimeTailEnergy

/-- The signed window derivative of the exact combined two-cutoff profile. -/
def tail {ι : Type*} (P : Finset ι) (c x : ι → ℝ) (L t : ℝ) : ℝ :=
  ∑ p ∈ P, (Ioc (L-x p) L).indicator (fun _ => c p) t

/-- The original two-hinge profile, with the prime sum still signed. -/
def profile {ι : Type*} (P : Finset ι) (c x : ι → ℝ) (L : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ P, c p*(max 0 (L-Real.log k)-max 0 (L-x p-Real.log k))

private theorem tail_integrable {ι : Type*} (P : Finset ι) (c x : ι → ℝ) (L : ℝ) :
    Integrable (tail P c x L) := by
  exact integrable_finsetSum P (fun p _ =>
    (integrableOn_const (μ := volume) (s := Ioc (L-x p) L) (C := c p)
      (hs := by simp)).integrable_indicator measurableSet_Ioc)

private theorem tail_square_integrable {ι : Type*} (P : Finset ι)
    (c x : ι → ℝ) (L : ℝ) : Integrable (fun t => tail P c x L t ^ 2) := by
  have h : MemLp (tail P c x L) 2 volume := by
    exact memLp_finsetSum P (fun p _ => memLp_indicator_const 2 measurableSet_Ioc (c p)
      (Or.inr (by simp)))
  exact h.integrable_sq

private theorem overlap_hinges {a b v z : ℝ} (hab : a ≤ b) (hz : 0 ≤ z) :
    max (min v b-max (v-z) a) 0 =
      (max 0 (v-a)-max 0 (v-z-a))-(max 0 (v-b)-max 0 (v-z-b)) := by
  simp only [min_def,max_def]
  split_ifs <;> linarith

private theorem integral_window {a b v z : ℝ} (hab : a ≤ b) (hz : 0 ≤ z) (c : ℝ) :
    (∫ t in a..b, (Ioc (v-z) v).indicator (fun _ => c) t) =
      c*((max 0 (v-a)-max 0 (v-z-a))-(max 0 (v-b)-max 0 (v-z-b))) := by
  rw [intervalIntegral.integral_of_le hab,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,Ioc_inter_Ioc,setIntegral_const,
    Real.volume_real_Ioc,smul_eq_mul,overlap_hinges hab hz]
  ring

/-- The exact cutoff difference integrates one common SIGNED prime tail.
No divisor crossing or end atom is omitted. -/
theorem profile_difference {ι : Type*} (P : Finset ι) (c x : ι → ℝ) (L : ℝ)
    (hx : ∀ p ∈ P, 0 ≤ x p) {k : ℕ} (hk : 0 < k) :
    profile P c x L k-profile P c x L (k+1) =
      ∫ t in Real.log k..Real.log (k+1 : ℕ), tail P c x L t := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hab : Real.log k ≤ Real.log (k+1 : ℕ) :=
    Real.log_le_log hk0 (by norm_cast; omega)
  rw [profile,profile,← Finset.sum_sub_distrib]
  dsimp only [tail]
  rw [intervalIntegral.integral_finsetSum (fun p _ =>
    ((integrableOn_const (μ := volume) (s := Ioc (L-x p) L) (C := c p)
      (hs := by simp)).integrable_indicator measurableSet_Ioc).intervalIntegrable)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_window hab (hx p hp)]
  ring

private theorem integral_square_bound (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
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

/-- The discrete logarithmic cutoff energy is bounded by the energy of the
whole signed prime tail. All prime/cutoff cross terms remain inside the square. -/
theorem profile_energy_le_integral {ι : Type*} (P : Finset ι) (c x : ι → ℝ) (L : ℝ)
    (hx : ∀ p ∈ P, 0 ≤ x p) (R : ℕ) :
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(profile P c x L k-profile P c x L (k+1))^2) ≤
      ∫ t : ℝ, tail P c x L t^2 := by
  have hfi := tail_integrable P c x L
  have hf2 := tail_square_integrable P c x L
  have hp k (hk : k ∈ Finset.Icc 1 R) :
      (k : ℝ)*(profile P c x L k-profile P c x L (k+1))^2 ≤
        ∫ t in Real.log k..Real.log (k+1 : ℕ), tail P c x L t^2 := by
    have hkN : 0 < k := (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hkN
    have hk1 : (0 : ℝ) < (k+1 : ℕ) := by positivity
    have hab : Real.log k < Real.log (k+1 : ℕ) :=
      Real.log_lt_log hk0 (by norm_cast; omega)
    have hlog : (k : ℝ)*(Real.log (k+1 : ℕ)-Real.log k) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos hk1 hk0)
      rw [Real.log_div hk1.ne' hk0.ne'] at h
      have hh := mul_le_mul_of_nonneg_left h hk0.le
      have he : (k : ℝ)*(((k+1 : ℕ) : ℝ)/k-1) = 1 := by
        push_cast
        field_simp
        ring
      exact hh.trans_eq he
    rw [profile_difference P c x L hx hkN]
    have hs := mul_le_mul_of_nonneg_left
      (integral_square_bound (tail P c x L) hab hfi.intervalIntegrable hf2.intervalIntegrable) hk0.le
    have hpos : 0 ≤ ∫ t in Real.log k..Real.log (k+1 : ℕ), tail P c x L t^2 :=
      intervalIntegral.integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
    exact hs.trans (by nlinarith only [mul_le_mul_of_nonneg_right hlog hpos])
  apply (Finset.sum_le_sum hp).trans
  have he := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun k : ℕ => Real.log k) (m := 1) (n := R+1) (by omega)
    (fun k _ => hf2.intervalIntegrable)
  rw [Finset.Ico_add_one_right_eq_Icc,Nat.cast_one,Real.log_one] at he
  rw [he,intervalIntegral.integral_of_le (Real.log_natCast_nonneg (R+1))]
  exact setIntegral_le_integral hf2 (Filter.Eventually.of_forall (fun _ => sq_nonneg _))


/-- Only the transition strip pays the signed partial-prime budget. The
remaining strip pays the FULL signed moment, and all other cutoffs vanish. -/
theorem tail_energy_bound {ι : Type*} (P : Finset ι) (c x : ι → ℝ) (L : ℝ)
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hB0 : 0 ≤ B)
    (hx : ∀ p ∈ P, a ≤ x p ∧ x p ≤ b)
    (hB : ∀ t ∈ Ioc (L-b) (L-a), |tail P c x L t| ≤ B) :
    (∫ t : ℝ, tail P c x L t^2) ≤ a*(∑ p ∈ P, c p)^2+(b-a)*B^2 := by
  let F := (Ioc (L-a) L).indicator (fun _ => (∑ p ∈ P, c p)^2)
  let G := (Ioc (L-b) (L-a)).indicator (fun _ => B^2)
  have hiF : Integrable F := (integrableOn_const (μ := volume)
    (s := Ioc (L-a) L) (C := (∑ p ∈ P, c p)^2) (hs := by simp)).integrable_indicator measurableSet_Ioc
  have hiG : Integrable G := (integrableOn_const (μ := volume)
    (s := Ioc (L-b) (L-a)) (C := B^2) (hs := by simp)).integrable_indicator measurableSet_Ioc
  have hmajor t : tail P c x L t^2 ≤ F t+G t := by
    by_cases hh : t ∈ Ioc (L-a) L
    · have hg : t ∉ Ioc (L-b) (L-a) := by
        intro h
        exact (not_lt_of_ge h.2) hh.1
      have he : tail P c x L t = ∑ p ∈ P, c p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact indicator_of_mem (show t ∈ Ioc (L-x p) L from
          ⟨by linarith [(hx p hp).1,hh.1],hh.2⟩) _
      simp only [F,G,indicator_of_mem hh,indicator_of_notMem hg,he,add_zero,le_refl]
    · by_cases hl : t ∈ Ioc (L-b) (L-a)
      · simp only [F,G,indicator_of_notMem hh,indicator_of_mem hl,zero_add]
        have hs := (sq_le_sq₀ (abs_nonneg _) hB0).mpr (hB t hl)
        simpa only [sq_abs] using hs
      · have ht : t ≤ L-b ∨ L < t := by
          by_cases h : t ≤ L
          · left
            by_contra hn
            have htlo : L-b < t := lt_of_not_ge hn
            have hthi : L-a < t := by
              by_contra h'
              exact hl ⟨htlo,le_of_not_gt h'⟩
            exact hh ⟨hthi,h⟩
          · exact Or.inr (lt_of_not_ge h)
        have he : tail P c x L t = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          apply indicator_of_notMem
          intro h
          rcases ht with ht | ht
          · linarith [(hx p hp).2,h.1]
          · exact (not_le_of_gt ht) h.2
        simp only [F,G,indicator_of_notMem hh,indicator_of_notMem hl,he,zero_add]
        norm_num
  have h := integral_mono (tail_square_integrable P c x L) (hiF.add hiG) hmajor
  have he : (∫ t : ℝ, F t+G t) = a*(∑ p ∈ P, c p)^2+(b-a)*B^2 := by
    rw [integral_add hiF hiG]
    dsimp only [F,G]
    rw [integral_indicator_const _ measurableSet_Ioc,
      integral_indicator_const _ measurableSet_Ioc,Real.volume_real_Ioc,Real.volume_real_Ioc]
    rw [show L-(L-a)=a by ring,show (L-a)-(L-b)=b-a by ring,
      max_eq_left ha,max_eq_left (sub_nonneg.mpr hab)]
    rfl
  exact h.trans_eq he

/-- The full coupled cutoff energy pays the signed full-period moment and
one transition-width times the signed tail budget. There is no length-L cost. -/
theorem profile_energy_bound {ι : Type*} (P : Finset ι) (c x : ι → ℝ) (L : ℝ)
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hB0 : 0 ≤ B)
    (hx : ∀ p ∈ P, a ≤ x p ∧ x p ≤ b)
    (hB : ∀ t ∈ Ioc (L-b) (L-a), |tail P c x L t| ≤ B) (R : ℕ) :
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(profile P c x L k-profile P c x L (k+1))^2) ≤
      a*(∑ p ∈ P, c p)^2+(b-a)*B^2 :=
  (profile_energy_le_integral P c x L (fun p hp => ha.trans (hx p hp).1) R).trans
    (tail_energy_bound P c x L ha hab hB0 hx hB)

/-- Every clipped part of one actual prime period has a numerical signed
bound; no full-period completion or unproved prime discrepancy is used. -/
theorem clipped_cosine_bound {a b y : ℝ} (ha : 5000 ≤ a) (hab : a ≤ b)
    (hy : 54 ≤ |y|) (hlen : b-a ≤ 2*Real.pi/|y|) (c : ℝ) :
    |∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
      Real.cos (y*(Real.log p+c))/(p : ℝ)| ≤ 2/(|y| *a)+4/a^2 := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < |y| := by linarith
  have hyne := abs_pos.mp hy0
  have hlen0 : 0 ≤ b-a := sub_nonneg.mpr hab
  have hlen' : b-a ≤ 1/8 := by
    have hh : 2*Real.pi/|y| ≤ 1/8 := by
      apply (div_le_iff₀ hy0).mpr
      nlinarith [Real.pi_lt_d4]
    exact hlen.trans hh
  have hylen : |y| *(b-a) ≤ 2*Real.pi := by
    have h := (le_div_iff₀ hy0).mp hlen
    nlinarith only [h]
  have hcost : (b-a)^2+(41/100 : ℝ)*(2+(|y|+2)*(b-a)) ≤ 4 := by
    have hh := pow_le_pow_left₀ hlen0 hlen' 2
    nlinarith [Real.pi_lt_d4]
  have herr := (ZetaRieszQuantitativePrimePeriod.cosine_interval_error ha hab hyne c).trans
    (div_le_div_of_nonneg_right hcost (sq_nonneg a))
  have hmain : |(Real.sin (y*(b+c))-Real.sin (y*(a+c)))/(y*a)| ≤ 2/(|y| *a) := by
    rw [abs_div,abs_mul,abs_of_pos ha0]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (abs_sub _ _).trans (by linarith [Real.abs_sin_le_one (y*(b+c)),Real.abs_sin_le_one (y*(a+c))])
  have h := (abs_sub_le (∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime,
      Real.cos (y*(Real.log p+c))/(p : ℝ))
    ((Real.sin (y*(b+c))-Real.sin (y*(a+c)))/(y*a)) 0).trans (add_le_add herr (by simpa using hmain))
  simpa only [sub_zero,add_comm] using h


/-- Membership in the literal prime interval retains its exact log edges. -/
theorem prime_interval_logs {a b : ℝ} {p : ℕ}
    (hp : p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime) :
    a < Real.log p ∧ Real.log p ≤ b := by
  have hs := Finset.mem_filter.mp hp
  have hI := Finset.mem_Ioc.mp hs.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hs.2.pos
  constructor
  · exact (Real.lt_log_iff_exp_lt hp0).mpr (Nat.lt_of_floor_lt hI.1)
  · apply (Real.log_le_iff_le_exp hp0).mpr
    exact (by exact_mod_cast hI.2 : (p : ℝ) ≤ ⌊Real.exp b⌋₊).trans
      (Nat.floor_le (Real.exp_pos b).le)

/-- A cutoff tail is exactly a clipped prime interval, for arbitrary signed
prime weights. The strict lower endpoint is not completed. -/
theorem tail_eq_prime_interval {a b D : ℝ} (haD : a ≤ D) (hD0 : 0 ≤ D)
    (L : ℝ) (c : ℕ → ℝ) :
    tail ((Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime)
      c (fun p => Real.log p) L (L-D) =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp D⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime, c p := by
  let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime
  have he (p : ℕ) : (Ioc (L-Real.log p) L).indicator (fun _ => c p) (L-D) =
      if D < Real.log p then c p else 0 := by
    have hh : (L-Real.log p < L-D ∧ L-D ≤ L) ↔ D < Real.log p := by
      constructor
      · intro h; linarith [h.1]
      · intro h; constructor <;> linarith
    simp only [indicator_apply,mem_Ioc,hh]
  have hset : P.filter (fun p : ℕ => D < Real.log p) =
      (Finset.Ioc ⌊Real.exp D⌋₊ ⌊Real.exp b⌋₊).filter Nat.Prime := by
    ext p
    simp only [P,Finset.mem_filter,Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_,hpb⟩,hp⟩,hDp⟩
      refine ⟨⟨?_,hpb⟩,hp⟩
      exact (Nat.floor_lt (Real.exp_pos D).le).mpr
        ((Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mp hDp)
    · rintro ⟨⟨hDp,hpb⟩,hp⟩
      refine ⟨⟨⟨?_,hpb⟩,hp⟩,?_⟩
      · exact (Nat.floor_mono (Real.exp_le_exp.mpr haD)).trans_lt hDp
      · exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mpr (Nat.lt_of_floor_lt hDp)
  dsimp only [tail]
  simp_rw [he]
  change (∑ p ∈ P, if D < Real.log p then c p else 0) = _
  rw [← Finset.sum_filter,hset]

/-- Every moving cutoff tail inside one prime period has the explicit
signed clipping budget. Both literal prime endpoints are retained. -/
theorem cosine_tail_bound {a y : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|)
    (c L : ℝ) {t : ℝ} (ht : t ∈ Ioc (L-(a+2*Real.pi/|y|)) (L-a)) :
    |tail ((Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime)
      (fun p => Real.cos (y*(Real.log p+c))/(p : ℝ)) (fun p => Real.log p) L t| ≤
      2/(|y| *a)+4/a^2 := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < |y| := by linarith
  let D := L-t
  have haD : a ≤ D := by dsimp [D]; linarith [ht.2]
  have hD0 : 0 < D := ha0.trans_le haD
  have hDb : D ≤ a+2*Real.pi/|y| := by dsimp [D]; linarith [ht.1]
  have he : t = L-D := by dsimp [D]; ring
  rw [he,tail_eq_prime_interval haD hD0.le]
  have hb := clipped_cosine_bound (ha.trans haD) hDb hy
    (by linarith : a+2*Real.pi/|y|-D ≤ 2*Real.pi/|y|) c
  apply hb.trans
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left haD hy0.le)
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ ha0.le haD 2)

/-- Actual-prime cancellation gives a numerical bound for the ENTIRE cutoff
energy, including its transition crossings. It is uniform in the Riesz
length and the number of primes or divisor cutoffs. -/
theorem cosine_profile_energy {a y : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|)
    (c L : ℝ) (R : ℕ) :
    let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime;
    let f := profile P (fun p => Real.cos (y*(Real.log p+c))/(p : ℝ))
      (fun p => Real.log p) L;
    (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2) ≤
      16/a^3+(2*Real.pi/|y|)*(2/(|y| *a)+4/a^2)^2 := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < |y| := by linarith
  let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime
  let c' := fun p : ℕ => Real.cos (y*(Real.log p+c))/(p : ℝ)
  have hb := profile_energy_bound P c' (fun p => Real.log p) L ha0.le
    (show a ≤ a+2*Real.pi/|y| by
      have : 0 ≤ 2*Real.pi/|y| := by positivity
      linarith)
    (by positivity : 0 ≤ 2/(|y| *a)+4/a^2)
    (fun p hp => ⟨(prime_interval_logs hp).1.le,(prime_interval_logs hp).2⟩)
    (fun t ht => cosine_tail_bound ha hy c L ht) R
  have hp := ZetaRieszQuantitativePrimePeriod.cosine_period_bound ha hy c
  have hs := pow_le_pow_left₀ (abs_nonneg _) hp 2
  rw [sq_abs] at hs
  have he : a*(4/a^2)^2 = 16/a^3 := by field_simp; ring
  have hc := (mul_le_mul_of_nonneg_left hs ha0.le).trans_eq he
  dsimp only
  change (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(profile P c' (fun p => Real.log p) L k-
    profile P c' (fun p => Real.log p) L (k+1))^2) ≤ _
  have hh : (a+2*Real.pi/|y|)-a = 2*Real.pi/|y| := by ring
  rw [hh] at hb
  exact hb.trans (add_le_add hc le_rfl)

/-- Numerical cost of the full signed moment and every moving cutoff tail. -/
def periodEnergy (a y : ℝ) : ℝ :=
  16/a^3+(2*Real.pi/|y|)*(2/(|y| *a)+4/a^2)^2

/-- The numerical joint moment/crossing budget is at most 1/(256*a^2).
This is an inverse-logarithmic estimate, not a source-scale decay theorem. -/
theorem sqrt_periodEnergy_le {a y : ℝ} (ha : 5000 ≤ a) (hy : 54 ≤ |y|) :
    Real.sqrt (periodEnergy a y) ≤ 1/(16*a) := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < |y| := by linarith
  have h16 : 16/a ≤ 16/5000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha
  have h4 : 4/a ≤ 4/5000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha
  have h2 : 2/|y| ≤ 2/54 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hy
  have hh : 2*Real.pi/|y| ≤ 1/8 := by
    apply (div_le_iff₀ hy0).mpr
    nlinarith [Real.pi_lt_d4]
  have hsmall : 2/|y|+4/a ≤ 1/25 := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2/|y|+4/a) hsmall 2
  have hprod := mul_le_mul hh hs (by positivity : 0 ≤ (2/|y|+4/a)^2) (by norm_num : (0 : ℝ) ≤ 1/8)
  have he : a^2*periodEnergy a y = 16/a+(2*Real.pi/|y|)*(2/|y|+4/a)^2 := by
    dsimp [periodEnergy]
    field_simp
  have hbudget : periodEnergy a y ≤ (1/(16*a))^2 := by
    have he' : a^2*(1/(16*a))^2 = (1/256 : ℝ) := by field_simp; norm_num
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ha0)).mp
    rw [he,he']
    nlinarith only [hprod,h16]
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity,hbudget⟩

/-- The literal ordinary-prime sum of the two Riesz cutoffs. This definition
is used immediately in the unconditional squarefree mean below. -/
def periodResponse (a y L c : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime,
    Real.cos (y*(Real.log p+c))/(p : ℝ)*
      (VaughanLogAverage.riesz L n-VaughanLogAverage.riesz (L-Real.log p) n)

/-- The combined finite hinge profile vanishes beyond its physical cutoff. -/
theorem profile_endpoint {ι : Type*} (P : Finset ι) (c x : ι → ℝ)
    (L : ℝ) (R : ℕ) (hR : Real.exp L < R+1) (hx : ∀ p ∈ P, 0 ≤ x p) :
    profile P c x L (R+1)=0 := by
  have hl : L < Real.log (R+1 : ℕ) := by
    simpa only [Real.log_exp,Nat.cast_add,Nat.cast_one] using
      Real.log_lt_log (Real.exp_pos L) hR
  apply Finset.sum_eq_zero
  intro p hp
  rw [max_eq_left (by linarith : L-Real.log (R+1 : ℕ) ≤ 0),
    max_eq_left (by linarith [hx p hp] : L-x p-Real.log (R+1 : ℕ) ≤ 0)]
  ring

private theorem response_eq_profile (a y L c : ℝ) (R : ℕ)
    (hR : Real.exp L < R+1) {n : ℕ} (hn : 0 < n) :
    periodResponse a y L c n =
      ∑ d ∈ Finset.Icc 1 R,
        profile ((Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime)
          (fun p => Real.cos (y*(Real.log p+c))/(p : ℝ)) (fun p => Real.log p) L d*
            (if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) := by
  unfold periodResponse
  have he (p : ℕ) := ZetaRieszCutoffMean.riesz_difference_eq_prefix R
    (sub_le_self L (Real.log_natCast_nonneg p)) hR hn
  simp_rw [he]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [profile,Finset.sum_mul,mul_assoc]

/-- An actual prime period, with all hinge crossings still signed, has an
all-count squarefree mean bounded by the explicit numerical tail energy.
The one absolute constant E is proved, but not numerically evaluated. -/
theorem exists_cosine_period_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (a y L c : ℝ) (X : ℕ) (S : Finset ℕ),
      5000 ≤ a → 54 ≤ |y| → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (periodResponse a y L c n)^2) ≤ E*X*periodEnergy a y := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_divisor_profile_mean
  refine ⟨E,hE,fun a y L c X S ha hy hS hSF => ?_⟩
  let R := ⌊Real.exp L⌋₊
  have hR : Real.exp L < R+1 := Nat.lt_floor_add_one (Real.exp L)
  let P := (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp (a+2*Real.pi/|y|)⌋₊).filter Nat.Prime
  let f := profile P (fun p => Real.cos (y*(Real.log p+c))/(p : ℝ))
    (fun p => Real.log p) L
  have hf : f (R+1)=0 := profile_endpoint P _ _ L R hR (fun p _ => Real.log_natCast_nonneg p)
  have he n (hn : n ∈ S) : periodResponse a y L c n =
      ∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) :=
    response_eq_profile a y L c R hR (by have := (Finset.mem_Ioc.mp (hS hn)).1; omega)
  rw [Finset.sum_congr rfl (fun n hn => congrArg (fun x : ℝ => x^2) (he n hn))]
  exact (hmean X R S f hS hSF hf).trans
    (mul_le_mul_of_nonneg_left (cosine_profile_energy ha hy c L R) (by positivity))

private theorem response_phase (a y L : ℝ) (hy : y ≠ 0) (v : ℝ) (n : ℕ) :
    periodResponse a y L v n =
      Real.cos (y*v)*periodResponse a y L 0 n+
      Real.sin (y*v)*periodResponse a y L (Real.pi/(2*y)) n := by
  have he p : Real.cos (y*(Real.log p+Real.pi/(2*y))) = -Real.sin (y*Real.log p) := by
    rw [show y*(Real.log p+Real.pi/(2*y)) = y*Real.log p+Real.pi/2 by field_simp,
      Real.cos_add_pi_div_two]
  unfold periodResponse
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [he]
  simp only [add_zero,mul_add,Real.cos_add]
  ring

private theorem response_phase_square (a y L : ℝ) (hy : y ≠ 0) (v : ℝ) (n : ℕ) :
    (periodResponse a y L v n)^2 ≤ (periodResponse a y L 0 n)^2+
      (periodResponse a y L (Real.pi/(2*y)) n)^2 := by
  rw [response_phase a y L hy v n]
  let C := periodResponse a y L 0 n
  let D := periodResponse a y L (Real.pi/(2*y)) n
  have ht := Real.sin_sq_add_cos_sq (y*v)
  have he : (Real.cos (y*v)*C+Real.sin (y*v)*D)^2+
      (Real.sin (y*v)*C-Real.cos (y*v)*D)^2 = C^2+D^2 := by
    calc
      _ = (Real.sin (y*v)^2+Real.cos (y*v)^2)*(C^2+D^2) := by ring
      _ = _ := by rw [ht,one_mul]
  nlinarith only [he,sq_nonneg (Real.sin (y*v)*C-Real.cos (y*v)*D)]

/-- The cofactor phase may vary arbitrarily across every squarefree count.
In particular c(n)=log(n) keeps the actual product phase cos(y log(p*n)).
No phase freezing, zero hypothesis or omitted cutoff crossing is used. -/
theorem exists_correlated_period_mean :
    ∃ E : ℝ, 0 < E ∧ ∀ (a y L : ℝ) (c : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      5000 ≤ a → 54 ≤ |y| → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      (∑ n ∈ S, (periodResponse a y L (c n) n)^2) ≤ E*X*periodEnergy a y := by
  obtain ⟨E,hE,hmean⟩ := exists_cosine_period_mean
  refine ⟨2*E,by positivity,fun a y L c X S ha hy hS hSF => ?_⟩
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have hs := Finset.sum_le_sum (fun n (_ : n ∈ S) => response_phase_square a y L hyne (c n) n)
  rw [Finset.sum_add_distrib] at hs
  have h0 := hmean a y L 0 X S ha hy hS hSF
  have h1 := hmean a y L (Real.pi/(2*y)) X S ha hy hS hSF
  nlinarith only [hs,h0,h1]

/-- Both signed sides of the actual prime/Riesz period are bounded with
arbitrary correlated cofactor weights and phases. The budget is explicit
apart from the single proved universal squarefree-mean constant. -/
theorem exists_correlated_period_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (a y L : ℝ) (c w : ℕ → ℝ) (X : ℕ) (S : Finset ℕ),
      5000 ≤ a → 54 ≤ |y| → S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      let J := ∑ n ∈ S, w n*periodResponse a y L (c n) n;
      let K := Real.sqrt ((∑ n ∈ S, (w n)^2)*E*X*periodEnergy a y);
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_correlated_period_mean
  refine ⟨E,hE,fun a y L c w X S ha hy hS hSF => ?_⟩
  dsimp only
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => periodResponse a y L (c n) n)).trans
      (mul_le_mul_of_nonneg_left (hmean a y L c X S ha hy hS hSF)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  have hp : 0 ≤ periodEnergy a y := by
    dsimp [periodEnergy]
    have ha0 : 0 < a := by linarith
    positivity
  rw [sq_abs,Real.sq_sqrt (by positivity)]
  nlinarith only [hs]

/-- Reciprocal cofactor weights pay their entire energy uniformly across
all prime counts. No cofactor-energy sum remains in the numerical budget. -/
theorem exists_shell_period_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (a y L W : ℝ) (c w : ℕ → ℝ) (M : ℕ) (S : Finset ℕ),
      5000 ≤ a → 54 ≤ |y| → 0 ≤ W → 1 ≤ M → S ⊆ Finset.Ioc M (2*M) →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, |w n| ≤ W/n) →
      let J := ∑ n ∈ S, w n*periodResponse a y L (c n) n;
      let K := Real.sqrt E*W*Real.sqrt (periodEnergy a y);
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hmean⟩ := exists_correlated_period_mean
  refine ⟨2*E,by positivity,fun a y L W c w M S ha hy hW hM hS hSF hw => ?_⟩
  dsimp only
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hSI : S ⊆ Finset.Ioc 1 (2*M) := by
    intro n hn
    have h := Finset.mem_Ioc.mp (hS hn)
    exact Finset.mem_Ioc.mpr ⟨by omega,h.2⟩
  have hcard : (S.card : ℝ) ≤ M := by
    have h := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h
    have he : 2*M-M=M := by omega
    rw [he] at h
    exact_mod_cast h
  have hwE : (∑ n ∈ S, (w n)^2) ≤ W^2/M := by
    have hp n (hn : n ∈ S) : (w n)^2 ≤ (W/M)^2 := by
      have hnM : (M : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1.le
      have h := (hw n hn).trans (div_le_div_of_nonneg_left hW hM0 hnM)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    calc
      _ ≤ ∑ _n ∈ S, (W/M)^2 := Finset.sum_le_sum hp
      _ = S.card*(W/M)^2 := by simp
      _ ≤ M*(W/M)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = W^2/M := by field_simp
  have hQ : 0 ≤ periodEnergy a y := by
    dsimp [periodEnergy]
    have ha0 : 0 < a := by linarith
    positivity
  have hmean' := hmean a y L c (2*M) S ha hy hSI hSF
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => periodResponse a y L (c n) n)).trans
      (mul_le_mul hwE hmean' (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  have he : W^2/M*(E*(2*M)*periodEnergy a y) = 2*E*W^2*periodEnergy a y := by
    field_simp
  push_cast at hs
  rw [he] at hs
  apply abs_le.mp
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hQ]
  nlinarith only [hs]

/-- Finite radial/period families share the same absolute constant and sum
their explicitly paid costs. Each period retains its full signed cutoff
response and arbitrary cofactor phase; no prime-count ceiling is introduced.
This does not license filling cofactor-dependent holes in a prime period. -/
theorem exists_radial_period_bounds {ι : Type*} :
    ∃ E : ℝ, 0 < E ∧ ∀ (B : Finset ι) (a L W : ι → ℝ) (y : ℝ)
      (c w : ι → ℕ → ℝ) (M : ι → ℕ) (S : ι → Finset ℕ),
      54 ≤ |y| → (∀ i ∈ B, 5000 ≤ a i) → (∀ i ∈ B, 0 ≤ W i) →
      (∀ i ∈ B, 1 ≤ M i) → (∀ i ∈ B, S i ⊆ Finset.Ioc (M i) (2*M i)) →
      (∀ i ∈ B, ∀ n ∈ S i, Squarefree n) →
      (∀ i ∈ B, ∀ n ∈ S i, |w i n| ≤ W i/n) →
      let J := ∑ i ∈ B, ∑ n ∈ S i, w i n*periodResponse (a i) y (L i) (c i n) n;
      let K := Real.sqrt E*(∑ i ∈ B, W i*Real.sqrt (periodEnergy (a i) y));
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_shell_period_bounds
  refine ⟨E,hE,fun B a L W y c w M S hy ha hW hM hS hSF hw => ?_⟩
  dsimp only
  have hp i (hi : i ∈ B) := hbound (a i) y (L i) (W i) (c i) (w i) (M i) (S i)
    (ha i hi) hy (hW i hi) (hM i hi) (hS i hi) (hSF i hi) (hw i hi)
  constructor
  · have h := Finset.sum_le_sum (fun i hi => (hp i hi).1)
    simp_rw [mul_assoc] at h
    simpa only [Finset.sum_neg_distrib,← Finset.mul_sum] using h
  · have h := Finset.sum_le_sum (fun i hi => (hp i hi).2)
    simpa only [← Finset.mul_sum,mul_assoc] using h

/-- A numerical reciprocal-prime-log cost pays an arbitrary finite family
of full signed prime/Riesz periods over all squarefree cofactor counts. The
original factorial/allocation variation within a prime period is not assumed
paid, and the remaining carrier still needs its global independent bounds. -/
theorem exists_radial_log_bounds {ι : Type*} :
    ∃ E : ℝ, 0 < E ∧ ∀ (B : Finset ι) (a L W : ι → ℝ) (y : ℝ)
      (c w : ι → ℕ → ℝ) (M : ι → ℕ) (S : ι → Finset ℕ),
      54 ≤ |y| → (∀ i ∈ B, 5000 ≤ a i) → (∀ i ∈ B, 0 ≤ W i) →
      (∀ i ∈ B, 1 ≤ M i) → (∀ i ∈ B, S i ⊆ Finset.Ioc (M i) (2*M i)) →
      (∀ i ∈ B, ∀ n ∈ S i, Squarefree n) →
      (∀ i ∈ B, ∀ n ∈ S i, |w i n| ≤ W i/n) →
      let J := ∑ i ∈ B, ∑ n ∈ S i, w i n*periodResponse (a i) y (L i) (c i n) n;
      let K := Real.sqrt E/16*(∑ i ∈ B, W i/a i);
      -K ≤ J ∧ J ≤ K := by
  obtain ⟨E,hE,hbound⟩ := exists_radial_period_bounds (ι := ι)
  refine ⟨E,hE,fun B a L W y c w M S hy ha hW hM hS hSF hw => ?_⟩
  have h := hbound B a L W y c w M S hy ha hW hM hS hSF hw
  dsimp only at h ⊢
  have hb : Real.sqrt E*(∑ i ∈ B, W i*Real.sqrt (periodEnergy (a i) y)) ≤
      Real.sqrt E/16*(∑ i ∈ B, W i/a i) := by
    calc
      _ ≤ Real.sqrt E*(∑ i ∈ B, W i*(1/(16*a i))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
          mul_le_mul_of_nonneg_left (sqrt_periodEnergy_le (ha i hi) hy) (hW i hi)))
            (Real.sqrt_nonneg E)
      _ = _ := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  exact ⟨(neg_le_neg hb).trans h.1,h.2.trans hb⟩

end RiemannGaussian.ZetaRieszPrimeTailEnergy
