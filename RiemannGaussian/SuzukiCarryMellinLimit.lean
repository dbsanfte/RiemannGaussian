/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseCode
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Module

/-!
# The continuum limit of the same finite Fejer packet

The exact triangular amplitude is sampled at `(N+1)/H`. Carry jumps are
rounded upwards, with their signs and all coincident jumps retained. The
sampling error is estimated before any source determinant is considered.
-/

namespace RiemannGaussian.SuzukiCarryMellinLimit
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryGramSource SuzukiCarryFejer SuzukiCarryPhaseCode
open scoped BigOperators Topology ComplexConjugate

/-- The exact continuous triangle underlying the finite Fejer vector. -/
def tent (v : ℝ) : ℝ := max 0 (min (v-1) (3-v))

/-- The continuum modulation uses normalized logarithmic scale. -/
def amplitude (tau v : ℝ) : ℂ := (tent v : ℂ)*Complex.exp (I*tau*v)

/-- Upward grid rounding. No boundary convention is replaced by an a.e. one. -/
def roundUp (H : ℕ) (v : ℝ) : ℝ := (⌈(H : ℝ)*v⌉₊ : ℝ)/(H : ℝ)

/-- Number of jumps needed to cover the triangle's full support. -/
def jumpCount (x : ℝ) : ℕ := ⌈6/x⌉₊

/-- The continuum alternating carry-jump response. -/
def profile (tau x : ℝ) : ℂ := ∑ k ∈ Finset.range (jumpCount x),
  (-1 : ℂ)^k*amplitude tau (((k+1 : ℕ) : ℝ)*x/2)

/-- Same jumps with the exact finite grid used by the Fejer packet. -/
def roundedProfile (H : ℕ) (tau x : ℝ) : ℂ := ∑ k ∈ Finset.range (jumpCount x),
  (-1 : ℂ)^k*amplitude tau (roundUp H (((k+1 : ℕ) : ℝ)*x/2))

theorem tent_nonneg (v : ℝ) : 0 ≤ tent v := le_max_left _ _

theorem tent_le_one (v : ℝ) : tent v ≤ 1 := by
  unfold tent
  apply max_le (by norm_num)
  by_cases hv : v ≤ 2
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

theorem tent_eq_zero_of_le {v : ℝ} (hv : v ≤ 1) : tent v = 0 := by
  apply max_eq_left
  exact (min_le_left _ _).trans (by linarith)

theorem tent_eq_zero_of_ge {v : ℝ} (hv : 3 ≤ v) : tent v = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem tent_eq_left {v : ℝ} (hlo : 1 ≤ v) (hhi : v ≤ 2) : tent v = v-1 := by
  rw [tent, min_eq_left (by linarith), max_eq_right (by linarith)]

theorem tent_eq_right {v : ℝ} (hlo : 2 ≤ v) (hhi : v ≤ 3) : tent v = 3-v := by
  rw [tent, min_eq_right (by linarith), max_eq_right (by linarith)]

theorem tent_lipschitz (v w : ℝ) : |tent v-tent w| ≤ |v-w| := by
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (min (v-1) (3-v))
    (0 : ℝ) (min (w-1) (3-w))
  have h2 := abs_min_sub_min_le_max (v-1) (3-v) (w-1) (3-w)
  have he : |(v-1)-(w-1)| = |v-w| := by congr 1; ring
  have he' : |(3-v)-(3-w)| = |v-w| := by rw [show (3-v)-(3-w) = -(v-w) by ring, abs_neg]
  rw [he, he', max_self] at h2
  simp only [sub_self, abs_zero] at h1
  rw [max_eq_right (abs_nonneg (min (v-1) (3-v)-min (w-1) (3-w)))] at h1
  exact h1.trans h2

theorem amplitude_norm (tau v : ℝ) : ‖amplitude tau v‖ = tent v := by
  rw [amplitude, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, abs_of_nonneg (tent_nonneg v)]

theorem amplitude_zero_of_ge (tau : ℝ) {v : ℝ} (hv : 3 ≤ v) : amplitude tau v = 0 := by
  simp [amplitude, tent_eq_zero_of_ge hv]

private theorem phase_lipschitz (tau v w : ℝ) :
    ‖Complex.exp (I*tau*v)-Complex.exp (I*tau*w)‖ ≤ |tau| *|v-w| := by
  have he : Complex.exp (I*tau*v)-Complex.exp (I*tau*w) =
      Complex.exp (I*tau*w)*(Complex.exp (I*(tau*(v-w) : ℝ))-1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    have hh : I*(tau : ℂ)*(w : ℂ)+I*(tau*(v-w) : ℝ) = I*tau*v := by
      push_cast
      ring
    rw [hh]
  rw [he, norm_mul, Complex.norm_exp]
  have hi : (I*(tau : ℂ)*(w : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [hi, Real.exp_zero, one_mul]
  simpa only [Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := tau*(v-w)))

/-- The modulation changes only the Lipschitz constant, uniformly in v. -/
theorem amplitude_lipschitz (tau v w : ℝ) :
    ‖amplitude tau v-amplitude tau w‖ ≤ (1+|tau|)*|v-w| := by
  have he : amplitude tau v-amplitude tau w =
      ((tent v-tent w : ℝ) : ℂ)*Complex.exp (I*tau*v)+
      (tent w : ℂ)*(Complex.exp (I*tau*v)-Complex.exp (I*tau*w)) := by
    unfold amplitude
    push_cast
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hn : ‖Complex.exp (I*tau*v)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [norm_mul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tent_nonneg w)]
  calc
    _ ≤ |v-w|+tent w*(|tau| *|v-w|) :=
      add_le_add (tent_lipschitz v w)
        (mul_le_mul_of_nonneg_left (phase_lipschitz tau v w) (tent_nonneg w))
    _ ≤ |v-w|+1*(|tau| *|v-w|) := by gcongr; exact tent_le_one w
    _ = _ := by ring

theorem roundUp_bounds {H : ℕ} (hH : 0 < H) {v : ℝ} (hv : 0 ≤ v) :
    v ≤ roundUp H v ∧ roundUp H v ≤ v+1/(H : ℝ) := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  constructor
  · rw [roundUp, le_div_iff₀ hp]
    simpa only [mul_comm] using Nat.le_ceil ((H : ℝ)*v)
  · rw [roundUp, div_le_iff₀ hp]
    have hc := (Nat.ceil_lt_add_one (mul_nonneg hp.le hv)).le
    convert hc using 1; field_simp

theorem roundUp_monotone {H : ℕ} (hH : 0 < H) : Monotone (roundUp H) := by
  intro v w hvw
  unfold roundUp
  gcongr

/-- Sampling error for every jump, including grid coincidences. -/
theorem roundedProfile_sub_profile_norm {H : ℕ} (hH : 0 < H)
    (tau : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖roundedProfile H tau x-profile tau x‖ ≤
      (1+|tau|)*(6/x+1)/(H : ℝ) := by
  rw [roundedProfile, profile, ← Finset.sum_sub_distrib]
  have hterm (k : ℕ) :
      ‖(-1 : ℂ)^k*amplitude tau (roundUp H (((k+1 : ℕ) : ℝ)*x/2))-
        (-1 : ℂ)^k*amplitude tau (((k+1 : ℕ) : ℝ)*x/2)‖ ≤ (1+|tau|)/(H : ℝ) := by
    rw [← mul_sub, norm_mul]
    have hb := roundUp_bounds hH (show 0 ≤ (((k+1 : ℕ) : ℝ)*x/2) by positivity)
    have hl := amplitude_lipschitz tau (roundUp H (((k+1 : ℕ) : ℝ)*x/2))
      (((k+1 : ℕ) : ℝ)*x/2)
    rw [abs_of_nonneg (sub_nonneg.mpr hb.1)] at hl
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
    apply hl.trans
    have hp : (0 : ℝ) < H := by exact_mod_cast hH
    have hd : roundUp H (((k+1 : ℕ) : ℝ)*x/2)-(((k+1 : ℕ) : ℝ)*x/2) ≤ 1/(H : ℝ) := by
      linarith [hb.2]
    calc
      _ ≤ (1+|tau|)*(1/(H : ℝ)) := by gcongr
      _ = _ := by ring
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range (jumpCount x), (1+|tau|)/(H : ℝ) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = (jumpCount x : ℝ)*((1+|tau|)/(H : ℝ)) := by simp
    _ ≤ (6/x+1)*((1+|tau|)/(H : ℝ)) := by
      gcongr
      exact (Nat.ceil_lt_add_one (show 0 ≤ 6/x by positivity)).le
    _ = _ := by ring

private theorem alternating_prefix_norm (K : ℕ) :
    ‖∑ k ∈ Finset.range K, (-1 : ℂ)^k‖ ≤ 1 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (-1 : ℂ)^k) K, Fin.sum_neg_one_pow]
  split_ifs <;> norm_num

/-- A joined alternating chain is controlled by its variation; no count
factor is introduced into this uniform integrability envelope. -/
private theorem alternating_chain_norm {K : ℕ} (g : ℝ → ℂ) (v : ℕ → ℝ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hl : ∀ a b, ‖g a-g b‖ ≤ C*|a-b|)
    (hm : Monotone v) (hend : g (v (K-1)) = 0) :
    ‖∑ k ∈ Finset.range K, (-1 : ℂ)^k*g (v k)‖ ≤ C*(v (K-1)-v 0) := by
  have he := Finset.sum_range_by_parts (fun k => g (v k)) (fun k => (-1 : ℂ)^k) K
  simp only [smul_eq_mul, hend, zero_mul, zero_sub] at he
  have hf : (∑ k ∈ Finset.range K, (-1 : ℂ)^k*g (v k)) =
      -(∑ k ∈ Finset.range (K-1), (g (v (k+1))-g (v k))*
        ∑ i ∈ Finset.range (k+1), (-1 : ℂ)^i) := by
    rw [← he]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hf, norm_neg]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (K-1), C*(v (k+1)-v k) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      have hk := hl (v (k+1)) (v k)
      rw [abs_of_nonneg (sub_nonneg.mpr (hm (by omega)))] at hk
      apply (mul_le_mul_of_nonneg_left (alternating_prefix_norm (k+1)) (norm_nonneg _)).trans
      simpa only [mul_one] using hk
    _ = C*(v (K-1)-v 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]

private theorem jumpCount_pos {x : ℝ} (hx : 0 < x) : 0 < jumpCount x :=
  Nat.ceil_pos.mpr (by positivity)

private theorem last_jump_ge {x : ℝ} (hx : 0 < x) :
    3 ≤ (jumpCount x : ℝ)*x/2 := by
  have hc := Nat.le_ceil (6/x)
  have hm := mul_le_mul_of_nonneg_right hc hx.le
  rw [div_mul_cancel₀ _ hx.ne'] at hm
  change 6 ≤ (jumpCount x : ℝ)*x at hm
  linarith

private theorem jump_span_le {x : ℝ} (hx : 0 < x) :
    (((jumpCount x-1+1 : ℕ) : ℝ)*x/2)-((1 : ℝ)*x/2) ≤ 3 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 6/x by positivity)
  have hj := jumpCount_pos hx
  rw [Nat.sub_add_cancel hj]
  have hm := mul_lt_mul_of_pos_right hc hx
  rw [add_mul, div_mul_cancel₀ _ hx.ne', one_mul] at hm
  change (jumpCount x : ℝ)*x < 6+x at hm
  linarith

/-- The continuum profile has a count-independent envelope. -/
theorem profile_norm_le (tau : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖profile tau x‖ ≤ 3*(1+|tau|) := by
  have hv : Monotone (fun k : ℕ => (((k+1 : ℕ) : ℝ)*x/2)) := by
    intro a b hab
    apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hx.le) (by norm_num)
    exact_mod_cast Nat.add_le_add_right hab 1
  have hend : amplitude tau (((jumpCount x-1+1 : ℕ) : ℝ)*x/2) = 0 := by
    rw [Nat.sub_add_cancel (jumpCount_pos hx)]
    exact amplitude_zero_of_ge tau (last_jump_ge hx)
  have h := alternating_chain_norm (amplitude tau) _ (by positivity)
    (amplitude_lipschitz tau) hv hend
  change ‖profile tau x‖ ≤ _ at h
  apply h.trans
  have hs := jump_span_le hx
  simp only [Nat.cast_one, zero_add] at hs ⊢
  nlinarith [abs_nonneg tau]

/-- Grid rounding also preserves a count-independent envelope. -/
theorem roundedProfile_norm_le {H : ℕ} (hH : 0 < H) (tau : ℝ)
    {x : ℝ} (hx : 0 < x) : ‖roundedProfile H tau x‖ ≤ 4*(1+|tau|) := by
  let v : ℕ → ℝ := fun k => (((k+1 : ℕ) : ℝ)*x/2)
  have hv : Monotone v := by intro a b hab; dsimp [v]; gcongr
  have hend : amplitude tau (roundUp H (v (jumpCount x-1))) = 0 := by
    apply amplitude_zero_of_ge
    have hr := (roundUp_bounds hH (show 0 ≤ v (jumpCount x-1) by dsimp [v]; positivity)).1
    have hj : 3 ≤ v (jumpCount x-1) := by
      dsimp [v]
      rw [Nat.sub_add_cancel (jumpCount_pos hx)]
      exact last_jump_ge hx
    exact hj.trans hr
  have h := alternating_chain_norm (amplitude tau) (roundUp H ∘ v) (by positivity)
    (amplitude_lipschitz tau) ((roundUp_monotone hH).comp hv) hend
  have h0 := (roundUp_bounds hH (show 0 ≤ v 0 by dsimp [v]; positivity)).1
  have hlast := (roundUp_bounds hH
    (show 0 ≤ v (jumpCount x-1) by dsimp [v]; positivity)).2
  have hspan : v (jumpCount x-1)-v 0 ≤ 3 := by simpa [v] using jump_span_le hx
  have hi : 1/(H : ℝ) ≤ 1 := by
    have hp : (1 : ℝ) ≤ H := by exact_mod_cast hH
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
  change ‖roundedProfile H tau x‖ ≤ _ at h
  apply h.trans
  dsimp [Function.comp_def] at *
  nlinarith [abs_nonneg tau]

theorem profile_eq_zero_above {x : ℝ} (hx : 6 ≤ x) (tau : ℝ) : profile tau x = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hk : (1 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
  have hv : 3 ≤ (((k+1 : ℕ) : ℝ)*x/2) := by nlinarith
  rw [amplitude_zero_of_ge tau hv, mul_zero]

theorem roundedProfile_eq_zero_above {H : ℕ} (hH : 0 < H) {x : ℝ}
    (hx : 6 ≤ x) (tau : ℝ) : roundedProfile H tau x = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hp : 0 ≤ (((k+1 : ℕ) : ℝ)*x/2) := by positivity
  have hr := (roundUp_bounds hH hp).1
  have hk : (1 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
  have hv : 3 ≤ (((k+1 : ℕ) : ℝ)*x/2) := by nlinarith
  rw [amplitude_zero_of_ge tau (hv.trans hr), mul_zero]

private theorem coefficient_eq_filter_card (A H N : ℕ) :
    coefficient A H N =
      (((((Finset.range H).filter (fun t => A+t ≤ N ∧ N < A+t+H)).card : ℝ)/H) : ℂ) := by
  classical
  unfold coefficient
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- The literal vector samples the tent one grid step to the right.
This exact shift is retained in the phase and rounding bridge. -/
theorem coefficient_eq_tent {H : ℕ} (hH : 0 < H) (N : ℕ) :
    coefficient H H N = (tent (((N+1 : ℕ) : ℝ)/(H : ℝ)) : ℂ) := by
  classical
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have hpC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  rw [coefficient_eq_filter_card]
  rcases lt_or_ge N H with hn | hn
  · have hf : (Finset.range H).filter (fun t => H+t ≤ N ∧ N < H+t+H) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      omega
    rw [tent_eq_zero_of_le (by rw [div_le_iff₀ hp]; exact_mod_cast (show N+1 ≤ 1*H by omega))]
    simp [hf]
  · rcases lt_or_ge N (2*H) with h2 | h2
    · have hf : (Finset.range H).filter (fun t => H+t ≤ N ∧ N < H+t+H) =
          Finset.range (N+1-H) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [hf, Finset.card_range,
        tent_eq_left (by rw [le_div_iff₀ hp]; exact_mod_cast (show 1*H ≤ N+1 by omega))
          (by rw [div_le_iff₀ hp]; exact_mod_cast (show N+1 ≤ 2*H by omega))]
      rw [Nat.cast_sub (by omega : H ≤ N+1)]
      push_cast
      field_simp [hpC]
    · rcases lt_or_ge N (3*H) with h3 | h3
      · have hf : (Finset.range H).filter (fun t => H+t ≤ N ∧ N < H+t+H) =
            Finset.Ico (N+1-2*H) H := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          omega
        rw [hf, Nat.card_Ico]
        have hc : H-(N+1-2*H) = 3*H-(N+1) := by omega
        rw [hc, Nat.cast_sub (by omega : N+1 ≤ 3*H),
          tent_eq_right (by rw [le_div_iff₀ hp]; exact_mod_cast (show 2*H ≤ N+1 by omega))
            (by rw [div_le_iff₀ hp]; exact_mod_cast (show N+1 ≤ 3*H by omega))]
        push_cast
        field_simp [hpC]
      · have hf : (Finset.range H).filter (fun t => H+t ≤ N ∧ N < H+t+H) = ∅ := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          omega
        rw [tent_eq_zero_of_ge (by rw [le_div_iff₀ hp]; exact_mod_cast (show 3*H ≤ N+1 by omega))]
        simp [hf]

/-- The only phase shift introduced by right sampling is a unit scalar. -/
theorem modulate_eq_amplitude {H : ℕ} (hH : 0 < H) (tau : ℝ) (N : ℕ) :
    modulate (coefficient H H) (tau/(H : ℝ)) N =
      Complex.exp (-(I*(tau/(H : ℝ))))*amplitude tau (((N+1 : ℕ) : ℝ)/(H : ℝ)) := by
  rw [modulate, coefficient_eq_tent hH, amplitude, modulation]
  push_cast
  conv_rhs => rw [mul_left_comm]
  rw [← Complex.exp_add]
  congr 2
  ring

/-- The normalized continuous carry, retaining the inclusive floor boundary. -/
def quotientCarry (v x : ℝ) : ℝ := if Even (⌊2*v/x⌋₊ : ℕ) then 0 else 1

private theorem quotientCarry_eq_prefix {v x : ℝ} (_hv : 0 ≤ v) (_hx : 0 < x) :
    (quotientCarry v x : ℂ) =
      ∑ k ∈ Finset.range (⌊2*v/x⌋₊), (-1 : ℂ)^k := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (-1 : ℂ)^k), Fin.sum_neg_one_pow]
  unfold quotientCarry
  split_ifs <;> norm_num

private theorem quotientCarry_eq_jumps {v x : ℝ} (hv : 0 ≤ v) (hhi : v ≤ 3)
    (hx : 0 < x) :
    (quotientCarry v x : ℂ) = ∑ k ∈ Finset.range (jumpCount x),
      if (((k+1 : ℕ) : ℝ)*x/2) ≤ v then (-1 : ℂ)^k else 0 := by
  classical
  rw [quotientCarry_eq_prefix hv hx]
  have hc : (⌊2*v/x⌋₊ : ℕ) ≤ jumpCount x := by
    have hf := Nat.floor_le (show 0 ≤ 2*v/x by positivity)
    have hj := Nat.le_ceil (6/x)
    have hh : 2*v/x ≤ 6/x := by gcongr; linarith
    exact_mod_cast hf.trans (hh.trans hj)
  have he (k : ℕ) : ((((k+1 : ℕ) : ℝ)*x/2) ≤ v) ↔ k < ⌊2*v/x⌋₊ := by
    rw [← Nat.add_one_le_iff, Nat.le_floor_iff (show 0 ≤ 2*v/x by positivity),
      le_div_iff₀ hx]
    constructor <;> intro h <;> linarith
  have hfilter : (Finset.range (jumpCount x)).filter
      (fun k => ((((k+1 : ℕ) : ℝ)*x/2) ≤ v)) = Finset.range ⌊2*v/x⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, he]
    omega
  rw [← hfilter, Finset.sum_filter]

theorem realCarry_eq_quotientCarry {H : ℕ} (hH : 0 < H) (N : ℕ) (t : ℝ) :
    realCarry N (t+Real.log H) = quotientCarry ((N : ℝ)/H) (Real.exp t) := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  have he : 2*(N : ℝ)*Real.exp (-(t+Real.log H)) = 2*((N : ℝ)/H)/Real.exp t := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log hp]
    field_simp
  unfold realCarry quotientCarry
  rw [he, ← Int.natCast_floor_eq_floor (by positivity)]
  simp only [Int.even_coe_nat]

private theorem grid_threshold {H : ℕ} (hH : 0 < H) {v : ℝ} (_hv : 0 ≤ v) (N : ℕ) :
    v ≤ (N : ℝ)/H ↔ ⌈(H : ℝ)*v⌉₊ ≤ N := by
  have hp : (0 : ℝ) < H := by exact_mod_cast hH
  rw [Nat.ceil_le, le_div_iff₀ hp]
  constructor <;> intro h <;> nlinarith

/-- One carry-jump atom lands in exactly its upward-rounded coefficient.
The sum also retains all jumps coinciding with an integer grid boundary. -/
private theorem rounded_jump_atom {H : ℕ} (hH : 0 < H) (tau : ℝ)
    {v : ℝ} (hv : 0 < v) :
    (∑ N ∈ Finset.range (3*H), amplitude tau (((N+1 : ℕ) : ℝ)/H)*
      ((if v ≤ (((N+1 : ℕ) : ℝ)/H) then (1 : ℂ) else 0)-
       (if v ≤ ((N : ℝ)/H) then (1 : ℂ) else 0))) = amplitude tau (roundUp H v) := by
  classical
  let n : ℕ := ⌈(H : ℝ)*v⌉₊
  have hn : 0 < n := Nat.ceil_pos.mpr (by positivity)
  simp_rw [grid_threshold hH hv.le]
  change (∑ N ∈ Finset.range (3*H), amplitude tau (((N+1 : ℕ) : ℝ)/H)*
      ((if n ≤ N+1 then (1 : ℂ) else 0)-(if n ≤ N then (1 : ℂ) else 0))) = _
  by_cases hupper : n ≤ 3*H
  · rw [Finset.sum_eq_single (n-1)]
    · simp [Nat.sub_add_cancel hn, show ¬n ≤ n-1 by omega, roundUp, n]
    · intro N _ hne
      have he : n ≤ N+1 ↔ n ≤ N := by omega
      simp only [he, sub_self, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · have hr : 3 ≤ roundUp H v := by
      rw [roundUp, le_div_iff₀ (show (0 : ℝ) < H by exact_mod_cast hH)]
      exact_mod_cast (show 3*H ≤ n by omega)
    rw [amplitude_zero_of_ge tau hr]
    apply Finset.sum_eq_zero
    intro N hN
    have hn1 : ¬n ≤ N+1 := by have := Finset.mem_range.mp hN; omega
    have hn0 : ¬n ≤ N := by omega
    simp [hn1, hn0]

/-- Exact finite-to-continuum-coordinate bridge, with only a unit phase
from the one-step coefficient sampling. No physical mask is completed. -/
theorem realPacket_eq_roundedProfile {H : ℕ} (hH : 0 < H) (tau t : ℝ) :
    realPacket (Finset.range (H+2*H)) (modulate (coefficient H H) (tau/(H : ℝ)))
      (t+Real.log H) =
        Complex.exp (-(I*(tau/(H : ℝ))))*roundedProfile H tau (Real.exp t) := by
  classical
  unfold realPacket realIncidence
  simp_rw [modulate_eq_amplitude hH, realCarry_eq_quotientCarry hH]
  push_cast
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have he : H+2*H = 3*H := by omega
  rw [he]
  have hrow (N : ℕ) (hN : N ∈ Finset.range (3*H)) :
      (quotientCarry (((N+1 : ℕ) : ℝ)/H) (Real.exp t) : ℂ)-
        (quotientCarry ((N : ℝ)/H) (Real.exp t) : ℂ) =
      ∑ k ∈ Finset.range (jumpCount (Real.exp t)), (-1 : ℂ)^k*
        ((if ((((k+1 : ℕ) : ℝ)*Real.exp t/2) ≤ (((N+1 : ℕ) : ℝ)/H)) then 1 else 0)-
         (if ((((k+1 : ℕ) : ℝ)*Real.exp t/2) ≤ ((N : ℝ)/H)) then 1 else 0)) := by
    have hn := Finset.mem_range.mp hN
    have hp : (0 : ℝ) < H := by exact_mod_cast hH
    rw [quotientCarry_eq_jumps (by positivity)
        (by rw [div_le_iff₀ hp]; exact_mod_cast (show N+1 ≤ 3*H by omega)) (Real.exp_pos t),
      quotientCarry_eq_jumps (by positivity)
        (by rw [div_le_iff₀ hp]; exact_mod_cast (show N ≤ 3*H by omega)) (Real.exp_pos t),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  have hsum := Finset.sum_congr rfl (fun N hN => congrArg
    (fun z => amplitude tau (((N+1 : ℕ) : ℝ)/H)*z) (hrow N hN))
  simp only [Nat.cast_add, Nat.cast_one] at hsum
  rw [hsum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold roundedProfile
  apply Finset.sum_congr rfl
  intro k _
  rw [← rounded_jump_atom hH tau (show 0 < (((k+1 : ℕ) : ℝ)*Real.exp t/2) by positivity),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N _
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The unit phase disappears only after the exact bridge has been proved. -/
theorem realMass_eq_roundedProfile {H : ℕ} (hH : 0 < H) (tau t : ℝ) :
    realMass (Finset.range (H+2*H)) (modulate (coefficient H H) (tau/(H : ℝ)))
      (t+Real.log H) = ‖roundedProfile H tau (Real.exp t)‖^2 := by
  rw [realMass, realPacket_eq_roundedProfile hH, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]

end
end RiemannGaussian.SuzukiCarryMellinLimit
