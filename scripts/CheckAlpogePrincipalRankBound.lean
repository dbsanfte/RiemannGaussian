import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV

/-! # A one-sided rank bound for the principal divisibility comparison -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions UpperTheory.Top

/-- The proportionality constant is uniform in the scale and lift of this family. -/
def BoundedLiftRank {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ k : ℕ, ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) j, j ∈ SizeData₂.lifts (Fm.D x i) →
    (Fm.L x i).dZ0 j ≤ k * (Fm.D x i).what₂.D0

theorem boundedLiftRank_of_smallLevelRankEq {ε : ℝ} {Fm : FamP ε}
    (h : SmallLevelRankEq Fm) : BoundedLiftRank Fm := by
  obtain ⟨a, ha⟩ := h
  exact ⟨1, a, fun x hx i j hj => by simp [ha x hx i j hj]⟩

/-- The dimension of the source bounds the range of the theta map even when the map
has a kernel. Thus the family construction can use an upper bound for the source. -/
theorem boundedLiftRank_of_source {ε : ℝ} {Fm : FamP ε} (k : ℕ) (a : ℝ)
    (h : ∀ x ≥ a, ∀ (i : Fm.Ix x) j, j ∈ SizeData₂.lifts (Fm.D x i) →
      Module.finrank ℂ ((Fm.D x i).what₂.Mj j) ≤ k * (Fm.D x i).what₂.D0) :
    BoundedLiftRank Fm := by
  refine ⟨k, a, fun x hx i j hj => ?_⟩
  exact (LinearMap.finrank_range_le ((Fm.D x i).what₂.thetaT (Fm.D x i).what₂.mu0 j)).trans
    (h x hx i j hj)

/-- The images of the isotypic subspaces cover the theta image, and the image of
each type uses at most a fixed number of dimensions per base-level row of that type. -/
def ThetaRowCover {R : Ranks} (D : Rows.Data R) (j k : ℕ) : Prop :=
  let T := D.thetaT D.mu0 j
  (⨆ π, (D.isot j π).map T) = T.range ∧
    ∀ π, Module.finrank ℂ ((D.isot j π).map T) ≤ k * D.nRows0 π

theorem thetaRank_le_of_rowCover {R : Ranks} {D : Rows.Data R} {j k : ℕ}
    (h : ThetaRowCover D j k) :
    Module.finrank ℂ (D.Zj D.mu0 j) ≤ k * D.D0 := by
  classical
  let S := fun π => (D.isot j π).map (D.thetaT D.mu0 j)
  obtain ⟨hspan, hrows⟩ := h
  have hS : (⨆ π, S π) = D.Zj D.mu0 j := hspan
  have htotal : ∑ π, D.nRows0 π = D.D0 := by
    unfold Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.ft0), Fintype.card_fin]
  calc
    Module.finrank ℂ (D.Zj D.mu0 j) = Module.finrank ℂ (LinearMap.range (DirectSum.coeLinearMap S)) := by
      rw [DirectSum.range_coeLinearMap, hS]
    _ ≤ Module.finrank ℂ (DirectSum D.FT fun π => S π) := LinearMap.finrank_range_le _
    _ = ∑ π, Module.finrank ℂ (S π) := Module.finrank_directSum ℂ _
    _ ≤ ∑ π, k * D.nRows0 π := Finset.sum_le_sum fun π _ => hrows π
    _ = k * D.D0 := by rw [← Finset.mul_sum, htotal]

theorem boundedLiftRank_of_rowCover {ε : ℝ} {Fm : FamP ε} (k : ℕ) (a : ℝ)
    (h : ∀ x ≥ a, ∀ (i : Fm.Ix x) j, j ∈ SizeData₂.lifts (Fm.D x i) →
      ThetaRowCover (Fm.D x i).what₂ j k) : BoundedLiftRank Fm :=
  ⟨k, a, fun x hx i j hj => thetaRank_le_of_rowCover (h x hx i j hj)⟩

private theorem divinN_at_of_rank_le {D : D7} (L : SizeData₂ D) (j k : ℕ) (C : ℝ)
    (hN : LinkN_at L j C) (hs : Summable (vvTerm D)) (hb : ∑' l, vvTerm D l ≤ L.sc.b)
    (hr : L.dZ0 j ≤ k * D.what₂.D0) (hlog : Real.log L.sc.x ^ 2 ≤ L.sc.x ^ L.sc.eps) :
    DIVinN_at L j (k * (|C| + 1)) := by
  let y := L.sc.x ^ L.sc.eps
  have hx : 0 < L.sc.x := one_pos.trans L.sc.one_lt_alt
  have hy : 1 ≤ y := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) D.R.two_le_m)
  have hb0 : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hNc : 0 ≤ L.Nc := by
    simp only [SizeData₂.Nc, budgetNc, rankBudget, bSize]
    positivity
  have hB : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * y := rfl
  have hbB : L.sc.b ≤ L.B0 := by
    rw [hB]
    have hfm := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm) hy
    nlinarith only [mul_nonneg (sub_nonneg.mpr hfm) hb0]
  have hB0 : 0 ≤ L.B0 := hb0.trans hbB
  have hP : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L ^ 2 = y * L.B0 := by
    change (D.R.f : ℝ) * D.R.m * L.sc.b * y ^ 2 = y * L.B0
    rw [hB]
    ring
  have hsum : y * L.B0 + Real.log L.sc.x ^ 2 * L.Nc ≤ y * (L.B0 + L.Nc) := by
    rw [mul_add]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hlog hNc) _
  have hscaled := mul_le_mul (le_abs_self C) hsum (by positivity) (abs_nonneg C)
  have hrest : ∑' l, vvTerm D l ≤ y * (L.B0 + L.Nc) :=
    hb.trans (hbB.trans ((le_add_of_nonneg_right hNc).trans
      (le_mul_of_one_le_left (add_nonneg hB0 hNc) hy)))
  have hr' : (L.dZ0 j : ℝ) ≤ (k : ℝ) * D.what₂.D0 := by exact_mod_cast hr
  unfold DIVinN_at
  calc
    etaSum L j ≤ _ := hN hs
    _ ≤ (L.dZ0 j : ℝ) * ((|C| + 1) * y * (L.B0 + L.Nc)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [hP]
      linarith only [hscaled, hrest]
    _ ≤ ((k : ℝ) * D.what₂.D0) * ((|C| + 1) * y * (L.B0 + L.Nc)) :=
      mul_le_mul_of_nonneg_right hr' (by positivity)
    _ = _ := by dsimp [y]; ring

/-- The rank factor changes the multiplicative constant, with no change in the exponent. -/
theorem divinN_of_bounded_rank {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hV : HypV Fm.toFamCore) (hN : LinkN Fm) (hR : BoundedLiftRank Fm) : DIVinN Fm := by
  obtain ⟨a, ha⟩ := hV
  obtain ⟨C, b, hb⟩ := hN
  obtain ⟨k, c, hc⟩ := hR
  obtain ⟨d, hd⟩ := log_sq_le_rpow hε
  refine ⟨k * (|C| + 1), max (max a (max b c)) (max d (Fm.x1 + 1)), fun x hx i j hj => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨ga, gb, gc⟩, gd, gx⟩ := hx
  obtain ⟨hf, hs, hle⟩ := vvRecord _ _ (ha x ga i)
  have hb1 : 1 ≤ (Fm.L x i).sc.b :=
    Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine divinN_at_of_rank_le _ j k C (hb x gb i hf j hj) hs
    (hle.trans (Real.sqrt_le_self_iff.2 (Or.inr hb1))) (hc x gc i j hj) ?_
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i]
  exact hd x gd

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.boundedLiftRank_of_smallLevelRankEq,
      ``RiemannGaussian.AlpogeWindow.boundedLiftRank_of_source,
      ``RiemannGaussian.AlpogeWindow.boundedLiftRank_of_rowCover,
      ``RiemannGaussian.AlpogeWindow.divinN_of_bounded_rank] do
    let axs ← collectAxioms decl
    for ax in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axs}"
