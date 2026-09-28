/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCapacityPhaseBudget
import RiemannGaussian.ZetaPrimeWindowLocalization
import RiemannGaussian.ZetaRieszEulerPrimeHeadDensity

/-!
# Source scale of the signed central-period credit

The actual period can be centered within a bounded distance of `2N`.
Retaining that radial information turns its positive credit into an
explicit growing source-normalized budget. The optional checked arithmetic
transfer applies this budget to the same signed populations and complement.
No independent floor or ceiling for the whole carrier is asserted.
-/

namespace RiemannGaussian.ZetaRieszCentralReserve
noncomputable section
open Filter Topology

/-- A bounded displacement to the right of the literal factorial saddle
loses only a fixed constant, with the same moment order and normalization. -/
theorem saddle_radial_lower {N : ℕ} (hN : 1 ≤ N) {v : ℝ}
    (hv : (2 : ℝ)*N ≤ v) (hvu : v ≤ 2*N+1) :
    Real.exp (-1)*(2 : ℝ)^N/(6*((N : ℝ)+1)) ≤
      Real.exp (-v/2)*v^N/N.factorial := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := PrimeWindow.local_monomial_lower hN (by norm_num : (0 : ℝ) ≤ 2)
  norm_num [PrimeWindow.localGrowth] at hs
  rw [show -(2*(N : ℝ))/2 = -(N : ℝ) by ring] at hs
  have hs' : (2 : ℝ)^N/(6*((N : ℝ)+1)) ≤
      Real.exp (-(N : ℝ))*(2*N)^N/N.factorial :=
    (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)).trans hs
  have he : Real.exp (-1)*Real.exp (-(N : ℝ)) ≤ Real.exp (-v/2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hvu])
  have hp : (2*(N : ℝ))^N ≤ v^N := pow_le_pow_left₀ (by positivity) hv N
  calc
    _ = Real.exp (-1)*((2 : ℝ)^N/(6*((N : ℝ)+1))) := by ring
    _ ≤ Real.exp (-1)*(Real.exp (-(N : ℝ))*(2*N)^N/N.factorial) :=
      mul_le_mul_of_nonneg_left hs' (Real.exp_nonneg _)
    _ = (Real.exp (-1)*Real.exp (-(N : ℝ)))*(2*N)^N/N.factorial := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul he hp (by positivity) (Real.exp_nonneg _)) (by positivity)

/-- The lower radial estimate is carried through the original source
normalization before a signed period credit is compared with its rest. -/
theorem scaled_saddle_margin_lower {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h)
    {N m : ℕ} (hN : 1 ≤ N) {v : ℝ}
    (hv : (2 : ℝ)*N ≤ v) (hvu : v ≤ 2*N+1) :
    ((m : ℝ)*h*u*Real.exp (-1)/6000)*(2*u)^N/((N : ℝ)+1) ≤
      u^(N+1)*((m : ℝ)/1000*(Real.exp (-v/2)*v^N/N.factorial)*h) := by
  have hs := mul_le_mul_of_nonneg_left (saddle_radial_lower hN hv hvu)
    (show 0 ≤ u^(N+1)*(m : ℝ)*h/1000 by positivity)
  calc
    _ = u^(N+1)*(m : ℝ)*h/1000*
        (Real.exp (-1)*(2 : ℝ)^N/(6*((N : ℝ)+1))) := by
      rw [mul_pow,pow_succ]
      field_simp
      ring
    _ ≤ u^(N+1)*(m : ℝ)*h/1000*(Real.exp (-v/2)*v^N/N.factorial) := hs
    _ = _ := by ring

/-- The explicit source-scaled central credit. This is a scalar bound,
not a new carrier or a numerical evaluation of a prime sum. -/
def sourceCredit (u y : ℝ) (N : ℕ) : ℝ :=
  (Real.pi*u*Real.exp (-1)/(24000*|y|))*(2*u)^N/((N : ℝ)+1)

/-- The phase mesh cancels from the source-scaled credit; the original
fixed height remains in the exact positive constant. -/
theorem sourceCredit_le_scaled_margin {u y : ℝ} (hu : 0 ≤ u) (hy : y ≠ 0)
    {N m : ℕ} (hN : 1 ≤ N) (hm : 0 < m) {v : ℝ}
    (hv : (2 : ℝ)*N ≤ v) (hvu : v ≤ 2*N+1) :
    sourceCredit u y N ≤
      u^(N+1)*((m : ℝ)/1000*(Real.exp (-v/2)*v^N/N.factorial)*
        (Real.pi/(4*m*|y|))) := by
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := scaled_saddle_margin_lower hu
    (show 0 ≤ Real.pi/(4*m*|y|) by positivity) hN (m := m) hv hvu
  have he : ((m : ℝ)*(Real.pi/(4*m*|y|))*u*Real.exp (-1)/6000) =
      Real.pi*u*Real.exp (-1)/(24000*|y|) := by
    field_simp
    ring
  simpa only [he,sourceCredit] using hs

/-- A single polynomial denominator cannot suppress the central
superunit source rate, however close the radius is to one half. -/
theorem geometric_over_successor_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto (fun N : ℕ => r^N/((N : ℝ)+1)) atTop atTop := by
  have hr0 : 0 < r := by linarith
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1
    (inv_pos.mpr hr0) (inv_lt_one_of_one_lt₀ hr)
  simp only [pow_one] at ht
  have ht' : Tendsto (fun N : ℕ => ((N : ℝ)+1)*r⁻¹^N) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun N => by
      change 0 < ((N : ℝ)+1)*r⁻¹^N
      positivity)⟩
  have hi := ht'.inv_tendsto_nhdsGT_zero
  change Tendsto (fun N : ℕ => (((N : ℝ)+1)*r⁻¹^N)⁻¹) atTop atTop at hi
  simpa only [mul_inv_rev,inv_pow,inv_inv,div_eq_mul_inv] using hi

/-- The explicit credit tends to positive infinity for every fixed
nonzero height and every radius strictly above one half. -/
theorem sourceCredit_tendsto_atTop {u y : ℝ} (hu : 1/2 < u) (hy : y ≠ 0) :
    Tendsto (sourceCredit u y) atTop atTop := by
  have hu0 : 0 < u := by linarith
  have hy0 : 0 < |y| := abs_pos.mpr hy
  have hc : 0 < Real.pi*u*Real.exp (-1)/(24000*|y|) := by positivity
  have ht := (geometric_over_successor_tendsto (by linarith : 1 < 2*u)).const_mul_atTop hc
  exact ht.congr' (Eventually.of_forall fun N => by dsimp [sourceCredit]; ring)

/-- If the whole normalized carrier has a finite source, the exact rest
in a lower comparison with this growing credit must tend to minus infinity.
This conditional audit forbids treating that rest as a small error. -/
theorem lower_rest_tendsto_atBot_of_finite_source {u y c : ℝ}
    (hu : 1/2 < u) (hy : y ≠ 0) {whole rest : ℕ → ℝ}
    (hsource : Tendsto whole atTop (𝓝 c))
    (hfloor : ∀ᶠ j : ℕ in atTop,
      rest j+sourceCredit u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ≤ whole j) :
    Tendsto rest atTop atBot := by
  have hc := (sourceCredit_tendsto_atTop hu hy).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  refine tendsto_atBot.2 fun b => ?_
  filter_upwards [hfloor,hsource.eventually_le_const (by linarith : c < c+1),
    hc.eventually_ge_atTop (c+1-b)] with j hf hs hb
  dsimp only [Function.comp_def] at hb
  linarith only [hf,hs,hb]

/-- The upper comparison has its own exact rest. A finite whole source
forces that rest to tend to plus infinity; the two rests cannot be silently
identified or their alternative credits added together. -/
theorem upper_rest_tendsto_atTop_of_finite_source {u y c : ℝ}
    (hu : 1/2 < u) (hy : y ≠ 0) {whole rest : ℕ → ℝ}
    (hsource : Tendsto whole atTop (𝓝 c))
    (hceiling : ∀ᶠ j : ℕ in atTop,
      whole j ≤ rest j-sourceCredit u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)) :
    Tendsto rest atTop atTop := by
  have hc := (sourceCredit_tendsto_atTop hu hy).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hceiling,hsource.eventually_const_le (by linarith : c-1 < c),
    hc.eventually_ge_atTop (b-(c-1))] with j hf hs hb
  dsimp only [Function.comp_def] at hb
  linarith only [hf,hs,hb]

end
end RiemannGaussian.ZetaRieszCentralReserve
