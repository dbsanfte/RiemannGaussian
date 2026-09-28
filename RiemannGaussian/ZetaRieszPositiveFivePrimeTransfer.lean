/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveCover
import RiemannGaussian.ZetaRieszMacroPrimeWindows

/-!
# Literal prime transfer for the translated positive-five fibre

The weighted least-prime sum is bounded before multiplying it by the
original one-sided phase envelope. Long logarithmic prime intervals use
the proved relative counting budgets. The cap is integrated with its
subtraction retained; no absolute source-scale PNT error is introduced.
-/

namespace RiemannGaussian.ZetaRieszPositiveFivePrimeTransfer
noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows

private theorem weighted_grid (f : ℕ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (M : ℕ) :
    (∑ p ∈ logPrimes a (M*h), f p) =
      ∑ i ∈ Finset.range M, ∑ p ∈ logPrimes (a+i*h) h, f p := by
  induction M with
  | zero =>
    have he : logPrimes a 0 = ∅ := by
      ext p
      simp only [mem_logPrimes_iff,Finset.notMem_empty,iff_false]
      rintro ⟨_,hl,hu⟩
      linarith
    simp [he]
  | succ M ih =>
    rw [Nat.cast_succ,add_mul,one_mul,logPrimes_add a (mul_nonneg (Nat.cast_nonneg _) hh) hh,
      Finset.sum_union (logPrimes_adjacent_disjoint a (M*h) h),Finset.sum_range_succ,ih]

private theorem cell_integral_lower {g : ℝ → ℝ} {a b l w K : ℝ}
    (hc : ContinuousOn g (Set.Icc a b)) (hw : 0 ≤ w)
    (hl : a ≤ l) (hu : l+w ≤ b)
    (hK : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x-g y| ≤ K*|x-y|) :
    (g l+K*w)*w ≤ (∫ x : ℝ in l..l+w, g x)+2*K*w^2 := by
  have hsub : Set.Icc l (l+w) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hl hu
  have hi := intervalIntegral.integral_mono_on (le_add_of_nonneg_right hw)
    (intervalIntegrable_const (μ := volume) (c := g l-K*w))
    ((hc.mono hsub).intervalIntegrable_of_Icc (le_add_of_nonneg_right hw))
    (fun x hx => show g l-K*w ≤ g x from by
      have he := hK l (hsub ⟨le_rfl,by linarith⟩) x (hsub hx)
      rw [abs_of_nonpos (by linarith [hx.1] : l-x ≤ 0)] at he
      have hk : 0 ≤ K ∨ w = 0 := by
        by_cases heq : w = 0
        · exact Or.inr heq
        · left
          have hww : 0 < w := lt_of_le_of_ne hw (Ne.symm heq)
          have hd := hK l (hsub ⟨le_rfl,by linarith⟩) (l+w) (hsub ⟨by linarith,le_rfl⟩)
          rw [show l-(l+w) = -w by ring,abs_neg,abs_of_nonneg hw] at hd
          nlinarith [abs_nonneg (g l-g (l+w))]
      rcases hk with hk | rfl
      · have hd := (le_abs_self (g l-g x)).trans he
        nlinarith [mul_le_mul_of_nonneg_left (show x-l ≤ w by linarith [hx.2]) hk]
      · have hex : x = l := by linarith [hx.1,hx.2]
        simp [hex])
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  nlinarith

/-- A complete finite logarithmic grid transfers a nonnegative weighted
prime fibre to its integral. The error is its explicit mesh variation;
there is no unproved prime-density limit in this statement. -/
theorem eventually_weighted_grid_upper {a b K : ℝ} {g : ℝ → ℝ}
    (ha : 0 < a) (hab : a < b) (hK0 : 0 ≤ K)
    (hc : ContinuousOn g (Set.Icc a b))
    (hg : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hK : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x-g y| ≤ K*|x-y|)
    {M : ℕ} (hM : 0 < M) :
    let w := (b-a)/(M : ℝ)
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (N : ℝ) ≤ t →
      (∑ p ∈ logPrimes (t*a) (t*(b-a)),
        (Real.log p/t)*g (Real.log p/t)/(p : ℝ)) ≤
        (5001/5000 : ℝ)*(1+w/a)*((∫ x : ℝ in a..b, g x)+2*K*w*(b-a)) := by
  let w := (b-a)/(M : ℝ)
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hw : 0 < w := div_pos (sub_pos.mpr hab) hm
  have hMw : (M : ℝ)*w = b-a := mul_div_cancel₀ _ hm.ne'
  filter_upwards [eventually_macro_reciprocal_bounds ha hw,eventually_ge_atTop (1 : ℕ)]
    with N hprime hN t ht
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 < t := by linarith
  let l : ℕ → ℝ := fun i => a+i*w
  have hl (i : ℕ) : a ≤ l i := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hw.le)
  have hu {i : ℕ} (hi : i < M) : l i+w ≤ b := by
    have hir : (i : ℝ)+1 ≤ M := by exact_mod_cast hi
    dsimp [l]
    nlinarith [mul_le_mul_of_nonneg_right hir hw.le]
  have hrow {i : ℕ} (hi : i ∈ Finset.range M) :
      (∑ p ∈ logPrimes (t*l i) (t*w),
        (Real.log p/t)*g (Real.log p/t)/(p : ℝ)) ≤
      (5001/5000 : ℝ)*(1+w/a)*((∫ x : ℝ in l i..l i+w, g x)+2*K*w^2) := by
    have hiM := Finset.mem_range.mp hi
    have hl0 : 0 < l i := ha.trans_le (hl i)
    have hli : l i ∈ Set.Icc a b := ⟨hl i,by linarith [hu hiM]⟩
    have hW : 0 ≤ g (l i)+K*w := add_nonneg (hg _ hli) (mul_nonneg hK0 hw.le)
    have hbound := (hprime (t*l i) (t*w)
      (by nlinarith [mul_le_mul_of_nonneg_left (hl i) ht0.le])
      (by nlinarith)).2
    have hpoint (p : ℕ) (hp : p ∈ logPrimes (t*l i) (t*w)) :
        (Real.log p/t)*g (Real.log p/t)/(p : ℝ) ≤
        ((l i+w)*(g (l i)+K*w))*(p : ℝ)⁻¹ := by
      obtain ⟨_,hpL,hpU⟩ := logPrimes_bounds hp
      have hpLo : l i ≤ Real.log p/t := (le_div_iff₀ ht0).mpr (by nlinarith)
      have hpHi : Real.log p/t ≤ l i+w := (div_le_iff₀ ht0).mpr (by nlinarith)
      have hpI : Real.log p/t ∈ Set.Icc a b := ⟨(hl i).trans hpLo,hpHi.trans (hu hiM)⟩
      have hd := hK (Real.log p/t) hpI (l i) hli
      rw [abs_of_nonneg (sub_nonneg.mpr hpLo)] at hd
      have hgp : g (Real.log p/t) ≤ g (l i)+K*w := by
        have he := (le_abs_self (g (Real.log p/t)-g (l i))).trans hd
        nlinarith [mul_le_mul_of_nonneg_left (show Real.log p/t-l i ≤ w by linarith) hK0]
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpHi hgp (hg _ hpI) (by linarith)) (inv_nonneg.mpr (Nat.cast_nonneg p))
    have hsum := (Finset.sum_le_sum hpoint).trans
      (show (∑ p ∈ logPrimes (t*l i) (t*w),
        ((l i+w)*(g (l i)+K*w))*(p : ℝ)⁻¹) ≤
        ((l i+w)*(g (l i)+K*w))*((5001/5000 : ℝ)*(t*w)/(t*l i)) from by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (by linarith) hW))
    have he : ((l i+w)*(g (l i)+K*w))*((5001/5000 : ℝ)*(t*w)/(t*l i)) =
        (5001/5000 : ℝ)*(1+w/(l i))*((g (l i)+K*w)*w) := by
      field_simp
    rw [he] at hsum
    have hratio : 1+w/(l i) ≤ 1+w/a := add_le_add le_rfl
      (div_le_div_of_nonneg_left hw.le ha (hl i))
    have hi0 : 0 ≤ (g (l i)+K*w)*w := mul_nonneg hW hw.le
    exact hsum.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 5001/5000)) hi0).trans
      (mul_le_mul_of_nonneg_left (cell_integral_lower hc hw.le (hl i) (hu hiM) hK)
        (by positivity)))
  have he : t*(b-a) = (M : ℝ)*(t*w) := by rw [← hMw]; ring
  rw [he,weighted_grid _ (t*a) (mul_nonneg ht0.le hw.le)]
  have hgrid : ∀ i : ℕ, t*a+(i : ℝ)*(t*w) = t*l i := by intro i; dsimp [l]; ring
  simp only [hgrid]
  apply (Finset.sum_le_sum (fun i hi => hrow hi)).trans
  have hint : ∀ i < M, IntervalIntegrable g volume (l i) (l (i+1)) := by
    intro i hi
    have he : l (i+1) = l i+w := by dsimp [l]; push_cast; ring
    rw [he]
    exact (hc.mono (Set.Icc_subset_Icc (hl i) (hu hi))).intervalIntegrable_of_Icc
      (le_add_of_nonneg_right hw.le)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have hstep : ∀ i, l (i+1) = l i+w := by intro i; dsimp [l]; push_cast; ring
  have hfirst : l 0 = a := by simp [l]
  have hlast : l M = b := by dsimp [l]; linarith only [hMw]
  simp only [hstep,hfirst,hlast] at hsum
  rw [← Finset.mul_sum,Finset.sum_add_distrib,hsum]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  apply le_of_eq
  congr 1
  change (∫ x : ℝ in a..b, g x)+(M : ℝ)*(2*K*w^2) =
    (∫ x : ℝ in a..b, g x)+2*K*w*(b-a)
  rw [← hMw]
  ring

/-- Summing the exact prime windows first makes the remaining mesh cost
arbitrarily small. This is a relative weighted counting inequality, not
an absolute error against the growing source envelope. -/
theorem eventually_weighted_integral_upper {a b K ε : ℝ} {g : ℝ → ℝ}
    (ha : 0 < a) (hab : a < b) (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hc : ContinuousOn g (Set.Icc a b))
    (hg : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hK : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x-g y| ≤ K*|x-y|) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (N : ℝ) ≤ t →
      (∑ p ∈ logPrimes (t*a) (t*(b-a)),
        (Real.log p/t)*g (Real.log p/t)/(p : ℝ)) ≤
        (10003/10000 : ℝ)*(∫ x : ℝ in a..b, g x)+ε := by
  have hw : Tendsto (fun M : ℕ => (b-a)/(M : ℝ)) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (b-a)
  let I := ∫ x : ℝ in a..b, g x
  have hi : 0 ≤ I := intervalIntegral.integral_nonneg hab.le hg
  have hlim : Tendsto (fun M : ℕ => (5001/5000 : ℝ)*(1+((b-a)/(M : ℝ))/a)*
      (I+2*K*((b-a)/(M : ℝ))*(b-a))) atTop (nhds ((5001/5000 : ℝ)*I)) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.add (hw.div_const a))).mul
      (tendsto_const_nhds.add ((hw.const_mul (2*K)).mul_const (b-a))) using 1; simp
  have he := hlim.eventually_lt_const
    (show (5001/5000 : ℝ)*I < (10003/10000 : ℝ)*I+ε by nlinarith)
  obtain ⟨M,hbound,hM⟩ := (he.and (eventually_gt_atTop (0 : ℕ))).exists
  filter_upwards [eventually_weighted_grid_upper ha hab hK0 hc hg hK hM] with N hN t ht
  exact (hN t ht).trans hbound.le

private theorem translated_density_lipschitz {a b Q r c : ℝ}
    (ha : 0 < a) (hbQ : b < Q) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |max 0 (min (x-r) c)/(x*(Q-x))-
        max 0 (min (y-r) c)/(y*(Q-y))| ≤ K*|x-y| := by
  let F := fun x : ℝ => max 0 (min (x-r) c)
  let H := fun x : ℝ => (x*(Q-x))⁻¹
  have hsub : LipschitzWith 1 (fun x : ℝ => x-r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  have hF : LipschitzWith 1 F := (hsub.min_const c).const_max 0
  have hH : ContDiffOn ℝ 1 H (Set.Icc a b) := by
    apply (contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id)).inv
    intro x hx
    exact ne_of_gt (mul_pos (ha.trans_le hx.1) (sub_pos.mpr (hx.2.trans_lt hbQ)))
  obtain ⟨K,hK⟩ := hH.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let B := (a*(Q-b))⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFb (x : ℝ) : |F x| ≤ c := by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le hc (min_le_right _ _)
  have hHb {x : ℝ} (hx : x ∈ Set.Icc a b) : |H x| ≤ B := by
    have hp : 0 < x*(Q-x) := mul_pos (ha.trans_le hx.1) (by linarith [hx.2])
    rw [abs_of_pos (inv_pos.mpr hp)]
    exact inv_anti₀ (mul_pos ha (by linarith))
      (mul_le_mul hx.1 (by linarith [hx.2]) (by linarith) (ha.trans_le hx.1).le)
  refine ⟨c*K+B,by positivity,?_⟩
  intro x hx y hy
  have hK' := hK.dist_le_mul x hx y hy
  have hF' := hF.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hK' hF'
  change |F x/(x*(Q-x))-F y/(y*(Q-y))| ≤ _
  simp only [div_eq_mul_inv]
  change |F x*H x-F y*H y| ≤ _
  calc
    _ = |F x*(H x-H y)+(F x-F y)*H y| := by congr 1; ring
    _ ≤ |F x*(H x-H y)|+|(F x-F y)*H y| := abs_add_le _ _
    _ = |F x| *|H x-H y|+|F x-F y| *|H y| := by rw [abs_mul,abs_mul]
    _ ≤ c*((K : ℝ)*|x-y|)+|x-y| *B := by
      exact add_le_add (mul_le_mul (hFb x) hK' (abs_nonneg _) hc)
        (mul_le_mul hF' (hHb hy) (abs_nonneg _) (abs_nonneg _))
    _ = (c*K+B)*|x-y| := by ring

/-- The literal weighted least-prime fibre has a near-sharp upper bound
by the translated harmonic cap. Its subtraction and the exact prime
logarithms are retained; all endpoints are included by half-open windows. -/
theorem eventually_translated_fibre_upper {a b Q r c ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hbQ : b < Q) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (N : ℝ) ≤ t →
      (∑ p ∈ logPrimes (t*a) (t*(b-a)),
        max 0 (min (Real.log p/t-r) c)/((Q-Real.log p/t)*(p : ℝ))) ≤
      (10003/10000 : ℝ)*
        (∫ x : ℝ in a..b, max 0 (min (x-r) c)/(x*(Q-x)))+ε := by
  let g := fun x : ℝ => max 0 (min (x-r) c)/(x*(Q-x))
  obtain ⟨K,hK0,hK⟩ := translated_density_lipschitz ha hbQ hc
  have hcont : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      exact ne_of_gt (mul_pos (ha.trans_le hx.1) (by linarith [hx.2]))
  have hg : ∀ x ∈ Set.Icc a b, 0 ≤ g x := by
    intro x hx
    exact div_nonneg (le_max_left _ _) (mul_nonneg (ha.le.trans hx.1) (by linarith [hx.2]))
  filter_upwards [eventually_weighted_integral_upper ha hab hK0 hε hcont hg hK,
    eventually_ge_atTop (1 : ℕ)] with N hN hpos t ht
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hpos
  have ht0 : 0 < t := by linarith
  convert hN t ht using 1
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨_,hpl,hpu⟩ := logPrimes_bounds hp
  have hx : 0 < Real.log p/t := ha.trans
    ((lt_div_iff₀ ht0).mpr (by nlinarith))
  have hlog : Real.log p ≠ 0 := ne_of_gt ((mul_pos ht0 ha).trans hpl)
  dsimp [g]
  field_simp [hlog]

/-- Extending only the nonnegative harmonic integration interval pays
its lower endpoint; no least-prime label is completed in the arithmetic sum. -/
theorem eventually_translated_full_fibre_upper {a b Q r c ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hbQ : b < Q) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (N : ℝ) ≤ t →
      (∑ p ∈ logPrimes (t*a) (t*(b-a)),
        max 0 (min (Real.log p/t-r) c)/((Q-Real.log p/t)*(p : ℝ))) ≤
      (10003/10000 : ℝ)*
        (∫ x : ℝ in 0..b, max 0 (min (x-r) c)/(x*(Q-x)))+ε := by
  have hi : IntervalIntegrable (fun x : ℝ => max 0 (min (x-r) c)/(x*(Q-x))) volume 0 b := by
    have hbig := ZetaRieszOrderedCapacity.cap_integrable_nonneg le_rfl (ha.le.trans hab.le)
      hbQ (add_nonneg hr hc)
    have hsmall := ZetaRieszOrderedCapacity.cap_integrable_nonneg le_rfl (ha.le.trans hab.le) hbQ hr
    convert hbig.sub hsmall using 1
    funext x
    rw [ZetaRieszPositiveFiveInterior.shifted_cap_eq_cap_sub hc,sub_div]
  have hI : (∫ x : ℝ in a..b, max 0 (min (x-r) c)/(x*(Q-x))) ≤
      ∫ x : ℝ in 0..b, max 0 (min (x-r) c)/(x*(Q-x)) := by
    apply intervalIntegral.integral_mono_interval ha.le hab.le le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_nonneg (le_max_left _ _) (mul_nonneg hx.1.le (by linarith [hx.2]))
    · exact hi
  filter_upwards [eventually_translated_fibre_upper ha hab hbQ hc hε] with N hN t ht
  exact (hN t ht).trans (add_le_add
    (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 10003/10000)) le_rfl)

/-- Two accepted cap certificates now pay a literal weighted prime sum,
including the pair-deficit subtraction. The claimed numerical integral
is not an extra hypothesis of the prime transfer. -/
theorem eventually_checked_cap_difference_upper (c : ZetaRieszCapacityCheck.Cap)
    (r lower upper : ℚ) (hc : ZetaRieszCapacityCheck.check c = true)
    (hs : ZetaRieszCapacityCheck.check {c with height := r,lower := lower,upper := upper} = true)
    (hc0 : c.a = 0) (hrc : r ≤ c.height) {a ε : ℝ}
    (ha : 0 < a) (hab : a < (c.b : ℝ)) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (N : ℝ) ≤ t →
      (∑ p ∈ logPrimes (t*a) (t*((c.b : ℝ)-a)),
        max 0 (min (Real.log p/t-r) ((c.height : ℝ)-r))/
          (((c.total : ℝ)-Real.log p/t)*(p : ℝ))) ≤
      (10003/10000 : ℝ)*((c.upper : ℝ)-lower)+ε := by
  have hg : 0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height := by
    have h := hc
    simp only [ZetaRieszCapacityCheck.check,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  have hr : (0 : ℝ) ≤ r := by
    have h := hs
    simp only [ZetaRieszCapacityCheck.check,Bool.and_eq_true,decide_eq_true_eq] at h
    exact_mod_cast h.1.2.2.2.le
  have hm : (0 : ℝ) ≤ (c.height : ℝ)-r := by exact_mod_cast sub_nonneg.mpr hrc
  have hI := ZetaRieszPositiveFiveInterior.checked_shifted_cap_integral_le c r lower upper hc hs hrc
  rw [hc0,Rat.cast_zero] at hI
  filter_upwards [eventually_translated_full_fibre_upper (Q := (c.total : ℝ)) ha hab (by exact_mod_cast hg.2.2.1)
    hr hm hε] with N hN t ht
  exact (hN t ht).trans (add_le_add
    (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 10003/10000)) le_rfl)

/-- The zero-offset case uses one accepted cap and retains the same
literal prime-window transfer. No inadmissible zero-height checker is used. -/
theorem eventually_checked_cap_upper (c : ZetaRieszCapacityCheck.Cap)
    (hc : ZetaRieszCapacityCheck.check c = true) (hc0 : c.a = 0) {a ε : ℝ}
    (ha : 0 < a) (hab : a < (c.b : ℝ)) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (N : ℝ) ≤ t →
      (∑ p ∈ logPrimes (t*a) (t*((c.b : ℝ)-a)),
        max 0 (min (Real.log p/t) (c.height : ℝ))/
          (((c.total : ℝ)-Real.log p/t)*(p : ℝ))) ≤
      (10003/10000 : ℝ)*(c.upper : ℝ)+ε := by
  have hg : 0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height := by
    have h := hc
    simp only [ZetaRieszCapacityCheck.check,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  have hm : (0 : ℝ) ≤ c.height := by exact_mod_cast hg.2.2.2.le
  have hb : (0 : ℝ) ≤ c.b := ha.le.trans hab.le
  have hI : (∫ x : ℝ in 0..(c.b : ℝ),
      max 0 (min x (c.height : ℝ))/(x*((c.total : ℝ)-x))) ≤ (c.upper : ℝ) := by
    have h := (ZetaRieszCapacityCheck.check_sound hc).2
    rw [hc0,Rat.cast_zero] at h
    convert h using 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    simp only [max_eq_right (le_min hx.1 hm)]
  filter_upwards [eventually_translated_full_fibre_upper (Q := (c.total : ℝ)) ha hab (by exact_mod_cast hg.2.2.1)
    (le_rfl : (0 : ℝ) ≤ 0) hm hε] with N hN t ht
  have hN := hN t ht
  simp only [sub_zero] at hN
  exact hN.trans (add_le_add
    (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 10003/10000)) le_rfl)

private theorem translated_integrable {b Q r c : ℝ}
    (hb : 0 ≤ b) (hbQ : b < Q) (hr : 0 ≤ r) (hc : 0 ≤ c) :
    IntervalIntegrable (fun x : ℝ => max 0 (min (x-r) c)/(x*(Q-x))) volume 0 b := by
  have hbig := ZetaRieszOrderedCapacity.cap_integrable_nonneg le_rfl hb hbQ (add_nonneg hr hc)
  have hsmall := ZetaRieszOrderedCapacity.cap_integrable_nonneg le_rfl hb hbQ hr
  convert hbig.sub hsmall using 1
  funext x
  rw [ZetaRieszPositiveFiveInterior.shifted_cap_eq_cap_sub hc,sub_div]

private theorem translated_density_le_inv {x Q r c : ℝ}
    (hx : 0 ≤ x) (hxQ : x < Q) (hr : 0 ≤ r) :
    max 0 (min (x-r) c)/(x*(Q-x)) ≤ 1/(Q-x) := by
  rcases hx.eq_or_lt with hx | hx
  · rw [← hx] at hxQ ⊢
    simp only [zero_mul,div_zero,sub_zero]
    positivity
  have hF : max 0 (min (x-r) c) ≤ x := max_le hx.le
    ((min_le_left _ _).trans (by linarith))
  calc
    _ ≤ x/(x*(Q-x)) := div_le_div_of_nonneg_right hF (by positivity)
    _ = _ := by field_simp

/-- Enlarging the physical least-prime endpoint and decreasing its
cofactor-dependent denominator have an explicit vanishing relative cost.
This controls the moving total-log cell boundaries before prime transfer. -/
theorem padded_fibre_integral_le {b Q r c η : ℝ}
    (hb : 0 < b) (hbQ : b < Q) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hη : 0 ≤ η) (hηu : η ≤ (Q-b)/4) :
    (∫ x : ℝ in 0..b+η, max 0 (min (x-r) c)/(x*(Q-η-x))) ≤
      (1+2*η/(Q-b))*(∫ x : ℝ in 0..b, max 0 (min (x-r) c)/(x*(Q-x)))+
        2*η/(Q-b) := by
  let F := fun x : ℝ => max 0 (min (x-r) c)
  let D := Q-b
  have hD : 0 < D := sub_pos.mpr hbQ
  have hpad : b+η < Q-η := by dsimp [D] at hD; linarith
  have hbig := translated_integrable (show 0 ≤ b+η by linarith) hpad hr hc
  have hfirst := translated_integrable hb.le (show b < Q-η by linarith) hr hc
  have hbase := translated_integrable hb.le hbQ hr hc
  have hlast : IntervalIntegrable (fun x : ℝ => F x/(x*(Q-η-x))) volume b (b+η) := by
    apply hbig.mono_set
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ b+η by linarith),
      Set.uIcc_of_le (le_add_of_nonneg_right hη)]
    exact Set.Icc_subset_Icc hb.le le_rfl
  have hratio : 0 ≤ 1+2*η/D := by positivity
  have hpoint {x : ℝ} (hx : x ∈ Set.Icc 0 b) :
      F x/(x*(Q-η-x)) ≤ (1+2*η/D)*(F x/(x*(Q-x))) := by
    rcases hx.1.eq_or_lt with hz | hx0
    · rw [← hz]
      simp
    have hden : 0 < Q-η-x := by linarith [hx.2]
    have hgap : D/2 ≤ Q-η-x := by dsimp [D]; linarith [hx.2]
    have hh := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*η/D by positivity)
    have he : (2*η/D)*(D/2) = η := by field_simp
    rw [he] at hh
    have hcomp : Q-x ≤ (1+2*η/D)*(Q-η-x) := by nlinarith
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos hx0 hden) (mul_pos hx0 (by linarith))).mpr
    have hh := mul_le_mul_of_nonneg_left hcomp (mul_nonneg (show 0 ≤ F x from le_max_left _ _) hx0.le)
    change max 0 (min (x-r) c)*x*(Q-x) ≤
      max 0 (min (x-r) c)*x*((1+2*η/D)*(Q-η-x)) at hh
    dsimp [F]
    nlinarith only [hh]
  have hi := intervalIntegral.integral_mono_on hb.le hfirst
    (hbase.const_mul (1+2*η/D)) (fun x hx => hpoint hx)
  rw [intervalIntegral.integral_const_mul] at hi
  have htail : (∫ x : ℝ in b..b+η, F x/(x*(Q-η-x))) ≤ 2*η/D := by
    have he : (∫ x : ℝ in b..b+η, F x/(x*(Q-η-x))) ≤
        ∫ _x : ℝ in b..b+η, 2/D := by
      apply intervalIntegral.integral_mono_on (le_add_of_nonneg_right hη) hlast intervalIntegrable_const
      intro x hx
      have hx0 : 0 ≤ x := hb.le.trans hx.1
      have hxQ : x < Q-η := hx.2.trans_lt hpad
      apply (translated_density_le_inv hx0 hxQ hr).trans
      apply (div_le_div_iff₀ (sub_pos.mpr hxQ) hD).mpr
      dsimp [D]
      linarith [hx.2]
    rw [intervalIntegral.integral_const] at he
    simp only [smul_eq_mul,add_sub_cancel_left] at he
    convert he using 1; first | rfl | ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hlast]
  exact add_le_add hi htail

end
end RiemannGaussian.ZetaRieszPositiveFivePrimeTransfer
