/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSaddleBand

/-!
# Accumulating signed gains on a growing saddle band

The finite sets are disjoint literal arithmetic periods. We sum their signed
inequalities before adjoining the untouched rest, so no whole-sum credit or
global error is counted more than once.
-/
namespace RiemannGaussian.ZetaRieszSaddlePacking
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszMultiPeriodSix (center)

/-- Full phase periods with centers spanning at most half the saddle width. -/
def periodCount (y : ℝ) (N : ℕ) : ℕ := ⌊|y| * Real.sqrt N/(4*Real.pi)⌋₊+1

/-- Each chosen center stays in the uniform square-root band. -/
theorem center_bounds {N : ℕ} (hN : 1 ≤ N) {v y : ℝ}
    (hv : 2*(N : ℝ) ≤ v) (hvu : v ≤ 2*N+1/2)
    {i : ℕ} (hi : i ∈ Finset.range (periodCount y N)) :
    2*(N : ℝ) ≤ center v y i ∧ center v y i ≤ 2*N+Real.sqrt N := by
  have hiN : i ≤ ⌊|y| * Real.sqrt N/(4*Real.pi)⌋₊ := by
    have h := Finset.mem_range.mp hi
    dsimp only [periodCount] at h
    omega
  have hiR : (i : ℝ) ≤ |y| * Real.sqrt N/(4*Real.pi) :=
    (Nat.cast_le.mpr hiN).trans (Nat.floor_le (by positivity))
  have hs : (1 : ℝ) ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr
    (by exact_mod_cast hN)
  have hstep : 0 ≤ 2*Real.pi/|y| := by positivity
  have hu : (i : ℝ)*(2*Real.pi/|y|) ≤ Real.sqrt N/2 := by
    by_cases hy : y = 0
    · simp only [hy,abs_zero,div_zero,mul_zero]; positivity
    · have hy0 : 0 < |y| := abs_pos.mpr hy
      calc
        _ ≤ (|y| * Real.sqrt N/(4*Real.pi))*(2*Real.pi/|y|) :=
          mul_le_mul_of_nonneg_right hiR hstep
        _ = Real.sqrt N/2 := by field_simp; norm_num
  dsimp only [center]
  constructor
  · linarith [mul_nonneg (Nat.cast_nonneg i) hstep]
  · linarith

/-- There are at least this many periods; the number grows as the saddle width. -/
theorem count_lower (y : ℝ) (N : ℕ) :
    |y| * Real.sqrt N/(4*Real.pi) ≤ (periodCount y N : ℝ) := by
  dsimp only [periodCount]
  exact_mod_cast (Nat.lt_floor_add_one (|y| * Real.sqrt N/(4*Real.pi))).le

/-- The old fixed collection is contained in the growing collection. -/
theorem old_count_le {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    ZetaRieszMultiPeriodSix.periodCount y ≤ periodCount y N := by
  have hs : (1 : ℝ) ≤ Real.sqrt N := (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr
    (by exact_mod_cast hN)
  unfold periodCount ZetaRieszMultiPeriodSix.periodCount
  apply Nat.add_le_add_right
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right (by nlinarith [abs_nonneg y]) (by positivity)

/-- A polynomial upper bound suffices to pay all prime-completion errors. -/
theorem eventually_count_le (y : ℝ) :
    ∀ᶠ N : ℕ in atTop, (periodCount y N : ℝ) ≤ (N : ℝ)+1 := by
  have hε : 0 < 1/(|y|/(4*Real.pi)+1) := by positivity
  filter_upwards [ZetaRieszSaddleBand.eventually_sqrt_add_one_le_mul hε] with N hN
  have hb : |y|/(4*Real.pi)*Real.sqrt N ≤ (N : ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0 < |y|/(4*Real.pi)+1)).mp
      (show Real.sqrt N+1 ≤ (N : ℝ)/(|y|/(4*Real.pi)+1) by simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hN)
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hf := Nat.floor_le (show 0 ≤ |y| * Real.sqrt N/(4*Real.pi) by positivity)
  dsimp only [periodCount]
  push_cast
  calc
    _ ≤ |y| * Real.sqrt N/(4*Real.pi)+1 := by linarith only [hf]
    _ ≤ (N : ℝ)+1 := by rw [mul_div_right_comm]; linarith only [hb]

/-- The accumulated net credit is linear in the moment order, rather
than only its square root, even after paying the one global owner debit. -/
theorem margin_lower {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 54 ≤ |y|) :
    (N : ℝ)/16 ≤ (periodCount y N : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot : (N : ℝ) ≤ Real.sqrt N*Real.sqrt ((N : ℝ)+1) := by
    calc
      _ = Real.sqrt N*Real.sqrt N := (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  have hc := mul_le_mul_of_nonneg_right (count_lower y N) (Real.sqrt_nonneg ((N : ℝ)+1))
  have hl : (3 : ℝ)*Real.sqrt N ≤ |y| * Real.sqrt N/(4*Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.pi)).mpr
    have hp : 12*Real.pi ≤ |y| := by linarith only [hy,Real.pi_lt_four]
    nlinarith only [mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (N : ℝ))]
  have hx := mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg ((N : ℝ)+1))
  nlinarith only [hc,hroot,hx,hn]

/-- Polynomially many copies of the existing geometric completion error still decay. -/
theorem tendsto_polynomial_allocation :
    Tendsto (fun N : ℕ => ((N : ℝ)+1)*ZetaRieszTriplePeriod.allocationBound N) atTop (𝓝 0) := by
  have hr := ZetaRieszJointAllocationFloor.Refined.allocationRate_bounds
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hr.1 hr.2
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr.1 hr.2
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr.1 hr.2
  have ht := ((h2.add (h1.const_mul 2)).add h0).const_mul
    (4*ZetaRieszWideOwnerAudit.radiusCeiling*zetaMoebiusLogMajorantMass (1+1/262144))
  convert ht using 1
  · ext N
    simp only [ZetaRieszTriplePeriod.allocationBound,pow_zero,pow_one,one_mul]
    ring
  · norm_num

/-- Half-open full periods have no shared label, irrespective of their masks. -/
theorem disjoint_of_log_support {v y : ℝ} (hy : 0 < |y|) (E : ℕ → Finset ℕ)
    (hs : ∀ i n, n ∈ E i → center v y i-Real.pi/|y| < Real.log n ∧
      Real.log n ≤ center v y i+Real.pi/|y|) :
    Pairwise (fun i j => Disjoint (E i) (E j)) := by
  have hstep : 0 < 2*Real.pi/|y| := by positivity
  have hsep {a b : ℕ} (hab : a < b) :
      center v y a+Real.pi/|y| ≤ center v y b-Real.pi/|y| := by
    have hh : (a : ℝ)+1 ≤ b := by exact_mod_cast hab
    have ht := mul_le_mul_of_nonneg_right hh hstep.le
    dsimp only [center]
    ring_nf at ht ⊢
    linarith
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro n hi hj
  have hni := hs i n hi
  have hnj := hs j n hj
  rcases lt_or_gt_of_ne hij with h | h
  · linarith [hsep h]
  · linarith [hsep h]

/-- Summed disjoint signed floor gains strengthen the same whole finite sum. -/
theorem floor_union (S B : Finset ℕ) (E : ℕ → Finset ℕ) (f : ℕ → ℂ)
    (obs : ℕ → ℝ) {a g e : ℝ}
    (hsub : ∀ i ∈ B, E i ⊆ S)
    (hdisj : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (E i) (E j))
    (hpay : ∀ i ∈ B, a*obs i+g-e ≤ a*(∑ n ∈ E i, f n).re) :
    a*((∑ n ∈ S\B.biUnion E, f n).re+∑ i ∈ B, obs i)+B.card*(g-e) ≤
      a*(∑ n ∈ S, f n).re := by
  have hU : B.biUnion E ⊆ S := by
    intro n hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    exact hsub i hi hn
  have hs := Finset.sum_le_sum hpay
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,nsmul_eq_mul] at hs
  have hsum := Finset.sum_sdiff hU (f := f)
  rw [Finset.sum_biUnion hdisj] at hsum
  have hr := congrArg (fun z : ℂ => a*z.re) hsum
  simp only [Complex.add_re,Complex.re_sum] at hr
  simp only [Complex.re_sum] at hs ⊢
  nlinarith only [hs,hr]

/-- The ceiling gains accumulate on their own disjoint literal populations. -/
theorem ceiling_union (S B : Finset ℕ) (E : ℕ → Finset ℕ) (f : ℕ → ℂ)
    (obs : ℕ → ℝ) {a g e : ℝ}
    (hsub : ∀ i ∈ B, E i ⊆ S)
    (hdisj : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (E i) (E j))
    (hpay : ∀ i ∈ B, a*(∑ n ∈ E i, f n).re ≤ a*obs i-g+e) :
    a*(∑ n ∈ S, f n).re ≤
      a*((∑ n ∈ S\B.biUnion E, f n).re+∑ i ∈ B, obs i)-B.card*(g-e) := by
  have hU : B.biUnion E ⊆ S := by
    intro n hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    exact hsub i hi hn
  have hs := Finset.sum_le_sum hpay
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,nsmul_eq_mul] at hs
  have hsum := Finset.sum_sdiff hU (f := f)
  rw [Finset.sum_biUnion hdisj] at hsum
  have hr := congrArg (fun z : ℂ => a*z.re) hsum
  simp only [Complex.add_re,Complex.re_sum] at hr
  simp only [Complex.re_sum] at hs ⊢
  nlinarith only [hs,hr]

end
end RiemannGaussian.ZetaRieszSaddlePacking
