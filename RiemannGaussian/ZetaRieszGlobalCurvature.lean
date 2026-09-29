/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDivisorPrefix
import RiemannGaussian.ZetaRieszTentSlope
/-!
# A global bound for signed Riesz cutoff crossings

Subtracting the affine response before taking absolute values charges only
divisors near the moving cutoff. Summing their incidence over every cofactor
costs one harmonic factor, independently of prime count or share geometry.
The final inequality retains the two actual signed weighted moments. It does
not assert that these moments or the full source-normalized carrier are small.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszGlobalCurvature
/-- Only a cutoff crossing survives the symmetric second difference. -/
theorem hinge_second_difference {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    max 0 (x+h)-2*max 0 x+max 0 (x-h) = max 0 (h-|x|) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    simp only [max_def]
    split_ifs <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    simp only [max_def]
    split_ifs <;> linarith

/-- This exact signed identity has no prime-count or squarefreeness restriction. -/
theorem riesz_second_difference {h : ℝ} (hh : 0 ≤ h) (D : ℝ) (a : ℕ) :
    VaughanLogAverage.riesz (D+h) a-2*VaughanLogAverage.riesz D a+
      VaughanLogAverage.riesz (D-h) a =
      ∑ d ∈ a.divisors, (μ d : ℝ)*max 0 (h-|D-Real.log d|) := by
  simp only [VaughanLogAverage.riesz,Finset.mul_sum,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hi := hinge_second_difference hh (D-Real.log d)
  rw [show D+h-Real.log d = D-Real.log d+h by ring,
    show D-h-Real.log d = D-Real.log d-h by ring]
  calc
    _ = (μ d : ℝ)*(max 0 (D-Real.log d+h)-2*max 0 (D-Real.log d)+max 0 (D-Real.log d-h)) := by ring
    _ = _ := by rw [hi]

/-- The finite signed cutoff curvature pays only divisors near the cutoff,
not all divisor choices or a bound depending on the prime count. -/
theorem abs_riesz_second_difference {h : ℝ} (hh : 0 ≤ h) (D : ℝ) (a : ℕ) :
    |VaughanLogAverage.riesz (D+h) a-2*VaughanLogAverage.riesz D a+
      VaughanLogAverage.riesz (D-h) a| ≤
      ∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|) := by
  rw [riesz_second_difference hh]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul,abs_of_nonneg (le_max_left 0 (h-|D-Real.log d|))]
  have hm : |(μ d : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  exact (mul_le_mul_of_nonneg_right hm (le_max_left _ _)).trans_eq (one_mul _)

/-- Exact weighted divisor reindexing, before any sign is discarded. -/
theorem weighted_hyperbola (f : ℕ → ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ ab ∈ n.divisorsAntidiagonal, f ab.1 ab.2) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), f a b := by
  let H : Finset (ℕ × ℕ) := ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter
    (fun ab => ab.1 * ab.2 ≤ X)
  have hset : (Finset.Icc 1 X).biUnion Nat.divisorsAntidiagonal = H := by
    ext ⟨a, b⟩
    simp only [Finset.mem_biUnion, Nat.mem_divisorsAntidiagonal, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc, H]
    constructor
    · rintro ⟨n, ⟨hn1, hnX⟩, he, hn0⟩
      have hab0 : a * b ≠ 0 := by rwa [he]
      have ha : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul hab0)
      have hb : 0 < b := Nat.pos_of_ne_zero (right_ne_zero_of_mul hab0)
      refine ⟨⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩, by omega⟩ <;> nlinarith
    · rintro ⟨⟨⟨ha, _haX⟩, ⟨hb, _hbX⟩⟩, hab⟩
      exact ⟨a * b, ⟨by nlinarith, hab⟩, rfl, by positivity⟩
  have hdis : (Finset.Icc 1 X : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
    intro n _hn m _hm hne
    apply Finset.disjoint_left.mpr
    intro ab ha hb
    exact hne ((Nat.mem_divisorsAntidiagonal.mp ha).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hb).1)
  have hf (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      (Finset.Icc 1 X).filter (fun b => a * b ≤ X) = Finset.Icc 1 (X / a) := by
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb, _hbX⟩, hab⟩
      exact ⟨hb, (Nat.le_div_iff_mul_le ha0).mpr (by simpa [mul_comm] using hab)⟩
    · rintro ⟨hb, hab⟩
      exact ⟨⟨hb, hab.trans (Nat.div_le_self X a)⟩,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le ha0).mp hab⟩
  calc
    _ = ∑ ab ∈ H, f ab.1 ab.2 := by rw [← hset, Finset.sum_biUnion hdis]
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        if a * b ≤ X then f a b else 0 := by
      simp only [H, Finset.sum_filter, Finset.sum_product]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter, hf a ha]



/-- Exact harmonic divisor-incidence sum over every integer, with no count bound. -/
theorem weighted_divisor_harmonic (g : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, g d / n) =
      ∑ d ∈ Finset.Icc 1 X, (g d / d) * ∑ b ∈ Finset.Icc 1 (X/d), (b : ℝ)⁻¹ := by
  have hi (n : ℕ) : (∑ d ∈ n.divisors, g d / n) =
      ∑ ab ∈ n.divisorsAntidiagonal, g ab.1 / (ab.1*ab.2 : ℕ) := by
    rw [Nat.sum_divisorsAntidiagonal (fun d b => g d / (d*b : ℕ))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  simp_rw [hi]
  rw [weighted_hyperbola (fun d b => g d / (d*b : ℕ))]
  apply Finset.sum_congr rfl
  intro d _
  simp [Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm, Finset.mul_sum]

/-- The entire weighted divisor incidence costs one harmonic factor. -/
theorem weighted_divisor_harmonic_le {g : ℕ → ℝ} (hg : ∀ d, 0 ≤ g d) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, g d / n) ≤
      (1+Real.log X) * ∑ d ∈ Finset.Icc 1 X, g d / d := by
  have hH (d : ℕ) : (∑ b ∈ Finset.Icc 1 (X/d), (b : ℝ)⁻¹) ≤ 1+Real.log X := by
    apply le_trans ?_ (by simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,
      Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log X)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc_right (Nat.div_le_self X d)
    · intro b _ _; positivity
  rw [weighted_divisor_harmonic,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  calc
    _ ≤ (g d/d)*(1+Real.log X) := mul_le_mul_of_nonneg_left (hH d) (div_nonneg (hg d) (Nat.cast_nonneg d))
    _ = _ := by ring

/-- The number of integers in an arbitrary real interval includes only one endpoint loss. -/
theorem card_real_interval_le {S : Finset ℕ} {l u : ℝ} (hlu : l ≤ u)
    (hS : ∀ d ∈ S, l ≤ d ∧ (d : ℝ) ≤ u) : (S.card : ℝ) ≤ u-l+1 := by
  by_cases hs : S.Nonempty
  · let a := S.min' hs
    let b := S.max' hs
    have ha : a ∈ S := Finset.min'_mem S hs
    have hb : b ∈ S := Finset.max'_mem S hs
    have hab : a ≤ b := Finset.min'_le S b hb
    have hc := Finset.card_le_card (show S ⊆ Finset.Icc a b from fun d hd =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le S d hd,Finset.le_max' S d hd⟩)
    rw [Nat.card_Icc] at hc
    have hr : (S.card : ℝ) ≤ (b : ℝ)+1-a := by
      have hh : (S.card : ℝ) ≤ ((b+1-a : ℕ) : ℝ) := by exact_mod_cast hc
      simpa only [Nat.cast_sub (by omega : a ≤ b+1),Nat.cast_add,Nat.cast_one] using hh
    linarith [(hS a ha).1,(hS b hb).2]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    linarith

/-- A thin logarithmic interval has a reciprocal mass independent of the prime count. -/
theorem log_window_reciprocal_le {h : ℝ} (hh : 0 ≤ h) (D : ℝ) (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d ∧ |D-Real.log d| ≤ h) :
    (∑ d ∈ S, (d : ℝ)⁻¹) ≤ Real.exp (2*h)-1+Real.exp (h-D) := by
  have hb d (hd : d ∈ S) : Real.exp (D-h) ≤ d ∧ (d : ℝ) ≤ Real.exp (D+h) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (hS d hd).1
    have ha := abs_le.mp (hS d hd).2
    constructor
    · rw [← Real.exp_log hdR]
      exact Real.exp_le_exp.mpr (by linarith)
    · exact (Real.log_le_iff_le_exp hdR).mp (by linarith)
  have hc := card_real_interval_le (show Real.exp (D-h) ≤ Real.exp (D+h) from
    Real.exp_le_exp.mpr (by linarith)) hb
  have hi d (hd : d ∈ S) : (d : ℝ)⁻¹ ≤ Real.exp (h-D) := by
    have he := one_div_le_one_div_of_le (Real.exp_pos (D-h)) (hb d hd).1
    simpa only [one_div,← Real.exp_neg,neg_sub] using he
  calc
    _ ≤ ∑ _d ∈ S, Real.exp (h-D) := Finset.sum_le_sum hi
    _ = (S.card : ℝ)*Real.exp (h-D) := by simp
    _ ≤ (Real.exp (D+h)-Real.exp (D-h)+1)*Real.exp (h-D) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = _ := by
      rw [add_mul,sub_mul,← Real.exp_add,← Real.exp_add]
      ring_nf
      simp
      ring

/-- The total divisor-cutoff crossing mass has an explicit count-free thin-window bound. -/
theorem tent_reciprocal_le {h : ℝ} (hh : 0 ≤ h) (D : ℝ) (X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, max 0 (h-|D-Real.log d|) / d) ≤
      h*(Real.exp (2*h)-1+Real.exp (h-D)) := by
  let S : Finset ℕ := (Finset.Icc 1 X).filter (fun d => |D-Real.log (d : ℝ)| ≤ h)
  have he : (∑ d ∈ Finset.Icc 1 X, max 0 (h-|D-Real.log d|) / d) =
      ∑ d ∈ S, max 0 (h-|D-Real.log d|) / d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hn
    have hh' : h ≤ |D-Real.log d| := le_of_lt (lt_of_not_ge (fun hh' => hn (Finset.mem_filter.mpr ⟨hd,hh'⟩)))
    rw [max_eq_left (by linarith),zero_div]
  rw [he]
  calc
    _ ≤ ∑ d ∈ S, h*(d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d _
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg d)
      exact max_le hh (by linarith [abs_nonneg (D-Real.log d)])
    _ = h * ∑ d ∈ S, (d : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (log_window_reciprocal_le hh D S (by
      intro d hd
      exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,(Finset.mem_filter.mp hd).2⟩)) hh

/-- A uniform aggregate bound for all cutoff curvatures, with no prime-count ceiling. -/
theorem curvature_prefix_le {h : ℝ} (hh : 0 ≤ h) (D : ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X,
      |VaughanLogAverage.riesz (D+h) a-2*VaughanLogAverage.riesz D a+
        VaughanLogAverage.riesz (D-h) a| / a) ≤
      (1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-D)) := by
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|)/a := by
      apply Finset.sum_le_sum
      intro a _
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (abs_riesz_second_difference hh D a) (Nat.cast_nonneg a)
    _ ≤ (1+Real.log X)*∑ d ∈ Finset.Icc 1 X, max 0 (h-|D-Real.log d|)/d :=
      weighted_divisor_harmonic_le (fun d => le_max_left _ _) X
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (tent_reciprocal_le hh D X)
        (by linarith [Real.log_natCast_nonneg X])


/-- The exact affine slope of the finite Riesz response at the chosen cutoff. -/
def cutoffSlope (D : ℝ) (a : ℕ) : ℝ :=
  ∑ d ∈ a.divisors, (μ d : ℝ)*(if 0 < D-Real.log d then 1 else 0)

/-- A hinge has no affine error unless the offset crosses its cutoff. -/
theorem hinge_affine_error {h x : ℝ} (hh : 0 ≤ h) (hx : |x| ≤ h) (z : ℝ) :
    |max 0 (z+x)-max 0 z-x*(if 0 < z then 1 else 0)| ≤ max 0 (h-|z|) := by
  have hx' := abs_le.mp hx
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
    simp only [max_def]
    split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hz)]
    simp only [max_def]
    split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

/-- The affine remainder of the actual signed divisor response is localized
at the cutoff. No prime count or squarefreeness assumption is needed. -/
theorem riesz_affine_error {h x : ℝ} (hh : 0 ≤ h) (hx : |x| ≤ h) (D : ℝ) (a : ℕ) :
    |VaughanLogAverage.riesz (D+x) a-VaughanLogAverage.riesz D a-
      x*cutoffSlope D a| ≤ ∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|) := by
  have he : VaughanLogAverage.riesz (D+x) a-VaughanLogAverage.riesz D a-
      x*cutoffSlope D a = ∑ d ∈ a.divisors, (μ d : ℝ)*
      (max 0 (D-Real.log d+x)-max 0 (D-Real.log d)-x*(if 0 < D-Real.log d then 1 else 0)) := by
    simp only [VaughanLogAverage.riesz,cutoffSlope,Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [show D+x-Real.log d = D-Real.log d+x by ring]
    ring
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul]
  have hm : |(μ d : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  exact (mul_le_mul hm (hinge_affine_error hh hx _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- All divisor-cutoff crossings over an arbitrary masked cofactor family
have the same explicit global bound. -/
theorem masked_tent_prefix_le {h : ℝ} (hh : 0 ≤ h) (D : ℝ) (S : Finset ℕ) (X : ℕ)
    (hS : S ⊆ Finset.Icc 1 X) :
    (∑ a ∈ S, (∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|))/a) ≤
      (1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-D)) := by
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 X, (∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|))/a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro a _ _
      positivity
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|)/a := by
      simp only [Finset.sum_div]
    _ ≤ (1+Real.log X)*∑ d ∈ Finset.Icc 1 X, max 0 (h-|D-Real.log d|)/d :=
      weighted_divisor_harmonic_le (fun _ => le_max_left _ _) X
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (tent_reciprocal_le hh D X)
        (by linarith [Real.log_natCast_nonneg X])

/-- The entire signed affine error is bounded simultaneously over all counts
and arbitrary retained weights. The two actual signed moments stay coupled. -/
theorem joint_affine_error_le {ι : Type*} (S : Finset ℕ) (X : ℕ)
    (P : ℕ → Finset ι) (x g : ℕ → ι → ℝ) {h W : ℝ}
    (hh : 0 ≤ h) (hW : 0 ≤ W) (D : ℝ) (hS : S ⊆ Finset.Icc 1 X)
    (hx : ∀ a ∈ S, ∀ p ∈ P a, |x a p| ≤ h)
    (hg : ∀ a ∈ S, (∑ p ∈ P a, |g a p|) ≤ W) :
    |∑ a ∈ S, ((∑ p ∈ P a, g a p*VaughanLogAverage.riesz (D+x a p) a)-
      VaughanLogAverage.riesz D a*(∑ p ∈ P a, g a p)-
      cutoffSlope D a*(∑ p ∈ P a, g a p*x a p))/a| ≤
      W*((1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-D))) := by
  have hi a (ha : a ∈ S) :
      |(∑ p ∈ P a, g a p*VaughanLogAverage.riesz (D+x a p) a)-
        VaughanLogAverage.riesz D a*(∑ p ∈ P a, g a p)-
        cutoffSlope D a*(∑ p ∈ P a, g a p*x a p)| ≤
      W*(∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|)) := by
    have he : (∑ p ∈ P a, g a p*VaughanLogAverage.riesz (D+x a p) a)-
        VaughanLogAverage.riesz D a*(∑ p ∈ P a, g a p)-
        cutoffSlope D a*(∑ p ∈ P a, g a p*x a p) =
        ∑ p ∈ P a, g a p*(VaughanLogAverage.riesz (D+x a p) a-
          VaughanLogAverage.riesz D a-x a p*cutoffSlope D a) := by
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [he]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ P a, |g a p| *(∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|)) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (riesz_affine_error hh (hx a ha p hp) D a) (abs_nonneg _)
      _ = (∑ p ∈ P a, |g a p|)*(∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|)) := by
        rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hg a ha) (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a ∈ S, W*((∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|))/a) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_div,abs_of_nonneg (show (0 : ℝ) ≤ a from Nat.cast_nonneg a),← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hi a ha) (Nat.cast_nonneg a)
    _ = W*(∑ a ∈ S, (∑ d ∈ a.divisors, max 0 (h-|D-Real.log d|))/a) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (masked_tent_prefix_le hh D S X hS) hW

/-- Away from the first divisor, the global crossing cost is quadratic in
the half-period, with an explicit rational constant. -/
theorem crossing_cost_le_quadratic {h D : ℝ} (hh : 0 < h) (hhu : h ≤ 1/16)
    (hD : h-Real.log h ≤ D) (X : ℕ) :
    (1+Real.log X)*h*(Real.exp (2*h)-1+Real.exp (h-D)) ≤
      (23/7 : ℝ)*(1+Real.log X)*h^2 := by
  have hden : 0 < 1-2*h := by linarith
  have he := Real.exp_bound_div_one_sub_of_interval (by linarith : 0 ≤ 2*h)
    (by linarith : 2*h < 1)
  have he' : Real.exp (2*h)-1 ≤ (16/7 : ℝ)*h := by
    have hrat : 1/(1-2*h) ≤ 1+(16/7 : ℝ)*h := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    linarith
  have ht : Real.exp (h-D) ≤ h := by
    calc
      _ ≤ Real.exp (Real.log h) := Real.exp_le_exp.mpr (by linarith)
      _ = h := Real.exp_log hh
  have hb : Real.exp (2*h)-1+Real.exp (h-D) ≤ (23/7 : ℝ)*h := by linarith
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (by linarith [Real.log_natCast_nonneg X] : 0 ≤ 1+Real.log X) hh.le)
  calc
    _ ≤ (1+Real.log X)*h*((23/7 : ℝ)*h) := hm
    _ = _ := by ring

end RiemannGaussian.ZetaRieszGlobalCurvature
