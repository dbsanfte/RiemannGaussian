/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourInteriorBudget
import Mathlib.MeasureTheory.Group.Integral

/-!
# A complete angular upper bound for the literal four-prime population

An exact unit-Jacobian change of cofactor coordinates and Fubini identify
the retained capped coefficient with the checked two-dimensional density.
All ordering faces cost one 1/1000000000 angular allowance; the largest-prime
clipping excess costs at most 1/78000000 on the refined original grid.
The resulting eventual floor keeps the original moment, moving length,
allocation, physical masks, full phase and whole signed core complement.
This proves the adverse domain transfer, not the full four/five compensation
or the independent cofinal RH floor. Exhaustive numerical covers remain
optional; their checked application is in CheckRieszFourCapacityTransfer.
-/

namespace RiemannGaussian.ZetaRieszFourAngularDomain
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFourPrimeCells ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget

/-- The exact affine change from cofactor shares `(r,a,q)` to `(p,q,r)`,
where `p=1-r-a-q`. No prime label or carrier is changed by this angular
integration coordinate map. -/
def coordinates : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun x := ![1-x 0-x 1-x 2,x 2,x 0]
  invFun x := ![x 2,1-x 0-x 1-x 2,x 1]
  left_inv x := by ext i; fin_cases i <;> simp; ring
  right_inv x := by ext i; fin_cases i <;> simp; ring
  measurable_toFun := by
    change Measurable (fun x : Fin 3 → ℝ => ![1-x 0-x 1-x 2,x 2,x 0])
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin 3 → ℝ => ![x 2,1-x 0-x 1-x 2,x 1])
    fun_prop

/-- The angular coordinate change has unit absolute Jacobian. -/
theorem coordinates_preserving : MeasurePreserving coordinates := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    if i = 0 then -1 else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0
  have hdet : M.det = -1 := by
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    rw [Matrix.det_fin_three]
    norm_num [M,h20,h21,h02,h12]
  have hlin : MeasurePreserving (Matrix.toLin' M) := by
    refine ⟨(LinearMap.continuous_on_pi _).measurable,?_⟩
    have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) (by rw [hdet]; norm_num)
    simpa only [hdet,inv_neg,inv_one,abs_neg,abs_one,ENNReal.ofReal_one,one_smul] using hm
  have he := (measurePreserving_add_left (volume : Measure (Fin 3 → ℝ)) ![1,0,0]).comp hlin
  have hf : ((fun x : Fin 3 → ℝ => ![1,0,0]+x) ∘ Matrix.toLin' M) = coordinates := by
    funext x
    change ![1,0,0]+Matrix.toLin' M x = ![1-x 0-x 1-x 2,x 2,x 0]
    rw [Matrix.toLin'_apply]
    ext i
    fin_cases i <;> simp [M,Matrix.mulVec,dotProduct,Fin.sum_univ_three]; ring
  rw [hf] at he
  exact he

/-- A largest-share slab has volume at most its thickness. The two
retained cofactor coordinates range over unit intervals; the affine map
has unit absolute Jacobian and retains both exterior boundaries. -/
theorem volume_largest_slab_le (S : Set (Fin 3 → ℝ)) (P w : ℝ)
    (hS : ∀ x ∈ S, 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ 1 ∧
      P ≤ 1-∑ i, x i ∧ 1-∑ i, x i ≤ P+w) :
    volume S ≤ ENNReal.ofReal w := by
  let B := Set.Icc (fun i : Fin 3 => if i = 0 then P else 0)
    (fun i : Fin 3 => if i = 0 then P+w else 1)
  have hsub : S ⊆ coordinates ⁻¹' B := by
    intro x hx
    have hg := hS x hx
    simp only [Fin.sum_univ_three] at hg
    constructor <;> intro i <;> fin_cases i <;>
      simp [coordinates] <;> linarith
  have hB : volume B = ENNReal.ofReal w := by
    rw [Real.volume_Icc_pi]
    simp [Fin.prod_univ_three]
  calc
    volume S ≤ volume (coordinates ⁻¹' B) := measure_mono hsub
    _ = volume B := coordinates_preserving.measure_preimage_equiv B
    _ = _ := hB

/-- The least-prime cap cancels its harmonic singularity before taking
the boundary norm. The remaining density is uniformly below 800 on the
literal active-cell chamber. -/
theorem density_bounds {lam : ℝ} {x : Fin 3 → ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hx : ∀ i, 0 < x i)
    (ha : (1/25 : ℝ) ≤ x 1) (hq : (13/100 : ℝ) ≤ x 2)
    (hp : (9/25 : ℝ) ≤ 1-∑ i, x i) :
    0 ≤ ZetaRieszFourInteriorBudget.density lam x ∧
      ZetaRieszFourInteriorBudget.density lam x ≤ 800 := by
  let p := 1-∑ i, x i
  have hL0 : 0 < lam := by linarith
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hprod : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx i)
  have hc : 0 ≤ boxCap lam 1 0 x x := boxCap_nonneg _ _ _ (hx 0).le
  have hcap : boxCap lam 1 0 x x ≤ x 0 := min_le_left _ _
  have hden : (17/25 : ℝ)*(9/25)*(1/25)*(13/100) ≤ lam*p*x 1*x 2 := by
    have h₁ := mul_le_mul hL hp (by norm_num) hL0.le
    have h₂ := mul_le_mul h₁ ha (by norm_num) (mul_nonneg hL0.le hp0.le)
    exact mul_le_mul h₂ hq (by norm_num) (by positivity)
  refine ⟨div_nonneg hc (by positivity),?_⟩
  calc
    ZetaRieszFourInteriorBudget.density lam x ≤ x 0/(lam*p*(∏ i, x i)) :=
      div_le_div_of_nonneg_right hcap (by positivity)
    _ = 1/(lam*p*x 1*x 2) := by
      rw [Fin.prod_univ_three]
      field_simp [(hx 0).ne']
    _ ≤ 1/((17/25 : ℝ)*(9/25)*(1/25)*(13/100)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    _ ≤ _ := by norm_num

/-- The exact angular coefficient on a largest-share excess of width w
costs at most 800*w. This is an integral bound on the actual covering
domain, not an unproved proxy for a boundary population. -/
theorem norm_integral_largest_slab_le (S : Set (Fin 3 → ℝ))
    (hSmeas : MeasurableSet S) {lam P w : ℝ} (hw : 0 ≤ w)
    (hL : (17/25 : ℝ) ≤ lam)
    (hS : ∀ x ∈ S, (∀ i, 0 < x i) ∧ x 0 ≤ 1 ∧ x 2 ≤ 1 ∧
      (1/25 : ℝ) ≤ x 1 ∧ (13/100 : ℝ) ≤ x 2 ∧
      (9/25 : ℝ) ≤ 1-∑ i, x i ∧ P ≤ 1-∑ i, x i ∧ 1-∑ i, x i ≤ P+w) :
    ‖∫ x in S, ZetaRieszFourInteriorBudget.density lam x‖ ≤ 800*w := by
  have hv := volume_largest_slab_le S P w (fun x hx =>
    ⟨(hS x hx).1 0 |>.le,(hS x hx).2.1,(hS x hx).1 2 |>.le,
      (hS x hx).2.2.1,(hS x hx).2.2.2.2.2.2⟩)
  have hfinite : volume S < ⊤ := hv.trans_lt ENNReal.ofReal_lt_top
  have he := norm_setIntegral_le_of_norm_le_const_ae (f := ZetaRieszFourInteriorBudget.density lam)
    hfinite (show ∀ᵐ x ∂volume.restrict S, ‖ZetaRieszFourInteriorBudget.density lam x‖ ≤ (800 : ℝ) by
      filter_upwards [ae_restrict_mem hSmeas] with x hx
      have hg := hS x hx
      have hb := density_bounds hL hg.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1
      simpa only [Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2)
  have hr : volume.real S ≤ w := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv).trans_eq (ENNReal.toReal_ofReal hw)
  exact he.trans (mul_le_mul_of_nonneg_left hr (by norm_num))

/-- Literal largest-prime clipping is retained by the angular cover up
to at most four normalized cell widths. This follows from the selected
integer itself, including its exact moving total logarithm. -/
theorem active_largest_upper (S : Finset ℕ) {L t h y b : ℝ} {lo x : Fin 3 → ℝ}
    (ht : 0 < t) (hhb : h/t ≤ b)
    (hne : (boundaryCell (clippedSupport S) L t h y
      (fun i => t*lo i) (fun _ => t*b)).Nonempty)
    (hx : x ∈ ZetaRieszFourInteriorBudget.cell lo b) :
    1-∑ i, x i ≤ (601/1000 : ℝ)+4*b := by
  obtain ⟨n,hn⟩ := hne
  obtain ⟨m,hm,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hp' := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
  have hclip := (Finset.mem_filter.mp hp'.2.1).2
  have hpB := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hp'.1
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  have hv' := Finset.mem_filter.mp hv
  have hb' (i : Fin 3) := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds
    (Fintype.mem_piFinset.mp hv'.1 i)
  have hm0 : (∏ i, v i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hb' i).1.ne_zero)
  have hT := ZetaRieszCoupledWindow.product_log_bounds hm0 hp'.1
  have hP := hclip.2 p (Nat.mem_primeFactors.mpr
    ⟨hpB.1,Nat.dvd_mul_left _ _,mul_ne_zero hm0 hpB.1.ne_zero⟩)
  have hl : Real.log ((∏ i, v i)*p : ℕ) = (∑ i, Real.log (v i))+Real.log p := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hm0) (by exact_mod_cast hpB.1.ne_zero),
      Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hb' i).1.ne_zero)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hb' i).2.2)
  have hxl (i : Fin 3) : lo i < x i := ((Set.mem_pi.mp hx) i (Set.mem_univ i)).1
  have hsx := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hxl i).le)) ht.le
  have hwidth := (div_le_iff₀ ht).mp hhb
  simp only [Fin.sum_univ_three] at hl hsum hsx ⊢
  nlinarith [hT.2.1,hT.2.2]

/-- Split `(p,q,r)` into the two certificate coordinates and the least
share. This is only the product measure's standard coordinate split. -/
def splitCoordinates : (Fin 3 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    MeasurableEquiv.prodComm

private theorem splitCoordinates_apply (x : Fin 3 → ℝ) :
    splitCoordinates x = (![x 0,x 1],x 2) := by
  change ((fun i => x ((2 : Fin 3).succAbove i)),x 2) = _
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · rfl

private theorem splitCoordinates_symm_apply (x : (Fin 2 → ℝ) × ℝ) :
    splitCoordinates.symm x = ![x.1 0,x.1 1,x.2] := by
  apply splitCoordinates.injective
  rw [MeasurableEquiv.apply_symm_apply,splitCoordinates_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · rfl

private theorem splitCoordinates_preserving : MeasurePreserving splitCoordinates :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans Measure.measurePreserving_swap

/-- Exact cofactor-to-certificate coordinates with the least share kept
as the fibre variable. -/
def toFibres : (Fin 3 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × ℝ) := coordinates.trans splitCoordinates

private theorem toFibres_preserving : MeasurePreserving toFibres :=
  coordinates_preserving.trans splitCoordinates_preserving

private theorem toFibres_symm_apply (v : (Fin 2 → ℝ) × ℝ) :
    toFibres.symm v = ![v.2,1-v.1 0-v.1 1-v.2,v.1 1] := by
  change coordinates.symm (splitCoordinates.symm v) = _
  rw [splitCoordinates_symm_apply]
  rfl

/-- The original exact cap in the two outer certificate coordinates and
its least-share fibre. -/
def fibre (lam : ℝ) (v : (Fin 2 → ℝ) × ℝ) : ℝ :=
  min v.2 (max 0 (min (lam-v.1 0) (min (1-lam-v.1 1) (1+v.1 0-2*lam)))) /
    (v.2*(1-v.1 0-v.1 1-v.2))/(lam*v.1 0*v.1 1)

private theorem fibre_eq_density (lam : ℝ) (v : (Fin 2 → ℝ) × ℝ) :
    fibre lam v = ZetaRieszFourInteriorBudget.density lam (toFibres.symm v) := by
  rw [toFibres_symm_apply,ZetaRieszFourInteriorBudget.density_eq_ordered]
  have he : 1-v.2-(1-v.1 0-v.1 1-v.2)-v.1 1 = v.1 0 := by ring
  rw [he]
  dsimp [fibre]
  rw [div_div]
  congr 1
  ring

private theorem density_eq_fibre (lam : ℝ) (x : Fin 3 → ℝ) :
    ZetaRieszFourInteriorBudget.density lam x = fibre lam (toFibres x) := by
  rw [fibre_eq_density,MeasurableEquiv.symm_apply_apply]

/-- The certificate's complete ordered fibres above its outer box. -/
def fibreRegion (B : ZetaRieszCapacityCover.Box) : Set ((Fin 2 → ℝ) × ℝ) :=
  {v | v.1 ∈ ZetaRieszCapacityCover.region B ∧
    max 0 (1-v.1 0-v.1 1-v.1 1) < v.2 ∧ v.2 ≤ (1-v.1 0-v.1 1)/2}

private theorem region_measurable (B : ZetaRieszCapacityCover.Box) :
    MeasurableSet (ZetaRieszCapacityCover.region B) :=
  (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

private theorem fibreRegion_measurable (B : ZetaRieszCapacityCover.Box) :
    MeasurableSet (fibreRegion B) := by
  apply MeasurableSet.inter ((region_measurable B).preimage measurable_fst)
  exact (measurableSet_lt (by fun_prop) measurable_snd).inter
    (measurableSet_le measurable_snd (by fun_prop))

private theorem measurable_fibre (lam : ℝ) : Measurable (fibre lam) := by
  unfold fibre
  fun_prop

private theorem fibre_bounds {lam : ℝ} {v : (Fin 2 → ℝ) × ℝ}
    (hL : (693/1015 : ℝ) ≤ lam)
    (hp : (9/25 : ℝ) ≤ v.1 0) (hpU : v.1 0 ≤ (601/1000 : ℝ))
    (hq : (13/100 : ℝ) ≤ v.1 1)
    (hr : max 0 (1-v.1 0-v.1 1-v.1 1) < v.2)
    (hrU : v.2 ≤ (1-v.1 0-v.1 1)/2) :
    0 ≤ fibre lam v ∧ fibre lam v ≤ 800 := by
  have hL0 : 0 < lam := by linarith
  have hp0 : 0 < v.1 0 := by linarith
  have hq0 : 0 < v.1 1 := by linarith
  have hr0 : 0 < v.2 := (le_max_left _ _).trans_lt hr
  have ha0 : 0 < 1-v.1 0-v.1 1-v.2 := by linarith
  have hcap := ZetaRieszOrderedCapacity.four_cap_density_le (q := v.1 1) hr0
    (by linarith) hpU (by norm_num : (601/1000 : ℝ) < 693/1015) hL
  have hden : (693/1015 : ℝ)*(9/25)*(13/100) ≤ lam*v.1 0*v.1 1 := by
    exact mul_le_mul (mul_le_mul hL hp (by norm_num) hL0.le) hq (by norm_num) (by positivity)
  have hm : 0 ≤ min v.2 (max 0 (min (lam-v.1 0) (min (1-lam-v.1 1) (1+v.1 0-2*lam)))) :=
    le_min hr0.le (le_max_left _ _)
  refine ⟨by exact div_nonneg (div_nonneg hm (by positivity)) (by positivity),?_⟩
  calc
    fibre lam v ≤ (2/((693/1015 : ℝ)-601/1000))/(lam*v.1 0*v.1 1) :=
      div_le_div_of_nonneg_right hcap (by positivity)
    _ ≤ (2/((693/1015 : ℝ)-601/1000))/((693/1015)*(9/25)*(13/100)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    _ ≤ _ := by norm_num

private theorem integrable_fibre_indicator (B : ZetaRieszCapacityCover.Box) {lam : ℝ}
    (hL : (693/1015 : ℝ) ≤ lam)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B,
      (9/25 : ℝ) ≤ x 0 ∧ x 0 ≤ (601/1000 : ℝ) ∧ (13/100 : ℝ) ≤ x 1) :
    Integrable ((fibreRegion B).indicator (fibre lam)) := by
  have hsub : fibreRegion B ⊆ (ZetaRieszCapacityCover.region B) ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro v hv
    have hg := hB v.1 hv.1
    refine ⟨hv.1,⟨(le_max_left _ _).trans hv.2.1.le,?_⟩⟩
    linarith [hv.2.2]
  have hBfin : volume (ZetaRieszCapacityCover.region B) ≠ ⊤ := by
    rw [ZetaRieszCapacityCover.region,Real.volume_pi_Ioc]
    exact ne_of_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))
  have hfin : volume (fibreRegion B) ≠ ⊤ := by
    apply ne_of_lt ((measure_mono hsub).trans_lt ?_)
    rw [Measure.volume_eq_prod,Measure.prod_prod]
    exact ENNReal.mul_lt_top (lt_of_le_of_ne le_top hBfin) (by simp)
  have hi : IntegrableOn (fibre lam) (fibreRegion B) := by
    apply Measure.integrableOn_of_bounded (M := (800 : ℝ)) hfin (measurable_fibre lam).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (fibreRegion_measurable B)] with v hv
    have hg := hB v.1 hv.1
    have hf := fibre_bounds hL hg.1 hg.2.1 hg.2.2 hv.2.1 hv.2.2
    simpa only [Real.norm_eq_abs,abs_of_nonneg hf.1] using hf.2
  exact hi.integrable_indicator (fibreRegion_measurable B)

/-- Fubini identifies the complete ordered three-share cap integral with
the exact two-dimensional density used by the checked angular cover. -/
theorem ordered_integral_eq (B : ZetaRieszCapacityCover.Box) {lam : ℝ}
    (hL : (693/1015 : ℝ) ≤ lam)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B,
      (9/25 : ℝ) ≤ x 0 ∧ x 0 ≤ (601/1000 : ℝ) ∧ (13/100 : ℝ) ≤ x 1) :
    (∫ x in toFibres ⁻¹' fibreRegion B, ZetaRieszFourInteriorBudget.density lam x) =
      ∫ x in ZetaRieszCapacityCover.region B, ZetaRieszFourCapacityCover.density lam x := by
  simp_rw [density_eq_fibre]
  rw [toFibres_preserving.setIntegral_preimage_emb toFibres.measurableEmbedding]
  rw [← integral_indicator (fibreRegion_measurable B)]
  have hi := integrable_fibre_indicator B hL hB
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi,← integral_indicator (region_measurable B)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ ZetaRieszCapacityCover.region B
  · rw [Set.indicator_of_mem hx]
    have he : (fun r : ℝ => (fibreRegion B).indicator (fibre lam) (x,r)) =
        (Set.Ioc (max 0 (1-x 0-x 1-x 1)) ((1-x 0-x 1)/2)).indicator (fun r => fibre lam (x,r)) := by
      funext r
      simp [fibreRegion,Set.indicator,hx]
    rw [he,integral_indicator measurableSet_Ioc]
    dsimp [ZetaRieszFourCapacityCover.density,fibre]
    rw [integral_div]
  · rw [Set.indicator_of_notMem hx]
    have he : (fun r : ℝ => (fibreRegion B).indicator (fibre lam) (x,r)) = fun _ => 0 := by
      funext r
      simp [fibreRegion,Set.indicator,hx]
    rw [he,integral_zero]

/-- The exact outer rectangle used by the whole-region upper certificate.
The largest-share clipping remains fixed at 601/1000. -/
def outerBox (lo : ℚ) : ZetaRieszCapacityCover.Box :=
  ![(2*lo-1,601/1000),((1-601/1000)/3,1-lo)]

private theorem outerBox_geometry {lo : ℚ} (hlo : (17/25 : ℝ) ≤ lo)
    {v : Fin 2 → ℝ} (hv : v ∈ ZetaRieszCapacityCover.region (outerBox lo)) :
    (9/25 : ℝ) ≤ v 0 ∧ v 0 ≤ (601/1000 : ℝ) ∧ (13/100 : ℝ) ≤ v 1 := by
  have h0 := (Set.mem_pi.mp hv) 0 (Set.mem_univ 0)
  have h1 := (Set.mem_pi.mp hv) 1 (Set.mem_univ 1)
  norm_num [outerBox] at h0 h1
  exact ⟨by linarith,h0.2,by linarith⟩

private theorem toFibres_apply (x : Fin 3 → ℝ) :
    toFibres x = (![1-x 0-x 1-x 2,x 2],x 0) := by
  change splitCoordinates (coordinates x) = _
  rw [splitCoordinates_apply]
  rfl

/-- Inside ordered cells, every nonzero capped coefficient with the
literal largest-share mask belongs to the complete certificate domain.
The positive cap itself supplies the remaining outer boundaries. -/
theorem ordered_mem_fibres {lo : ℚ} {lam : ℝ} {x : Fin 3 → ℝ}
    (hlam : (lo : ℝ) ≤ lam) (hx : ∀ i, 0 < x i)
    (hra : x 0 < x 1) (haq : x 1 < x 2)
    (hp : 1-∑ i, x i ≤ (601/1000 : ℝ))
    (hn : ZetaRieszFourInteriorBudget.density lam x ≠ 0) :
    x ∈ toFibres ⁻¹' fibreRegion (outerBox lo) := by
  have hc : boxCap lam 1 0 x x ≠ 0 := fun he => by
    apply hn
    change boxCap lam 1 0 x x / _ = 0
    rw [he,zero_div]
  have hc0 := boxCap_nonneg lam 1 0 (lo := x) (hx 0).le
  have hcap : 0 < boxCap lam 1 0 x x := lt_of_le_of_ne hc0 (Ne.symm hc)
  simp only [boxCap,Fin.sum_univ_three,mul_zero,mul_one,add_zero,
    lt_min_iff,lt_max_iff,lt_self_iff_false,false_or] at hcap
  simp only [Fin.sum_univ_three] at hp
  change toFibres x ∈ fibreRegion (outerBox lo)
  rw [toFibres_apply]
  refine ⟨?_,?_,?_⟩
  · apply Set.mem_pi.mpr
    intro i _
    fin_cases i <;> norm_num [outerBox] <;> constructor <;> linarith [hcap.2.1,hcap.2.2.1,hcap.2.2.2]
  · simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    exact max_lt (hx 0) (by linarith)
  · simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    linarith

/-- An arbitrary measurable ordered angular region costs no more than
the checked complete domain plus its explicitly paid largest-share slab.
The only enlargement is at most four cell widths. -/
theorem ordered_integral_le {lo : ℚ} {lam b : ℝ} {Ω : Set (Fin 3 → ℝ)}
    (hΩ : MeasurableSet Ω) (hb : 0 ≤ b)
    (hlo : (17/25 : ℝ) ≤ lo) (hlam : (lo : ℝ) ≤ lam)
    (hL : (693/1015 : ℝ) ≤ lam)
    (hg : ∀ x ∈ Ω, (∀ i, 0 < x i) ∧ x 0 < x 1 ∧ x 1 < x 2 ∧
      (1/25 : ℝ) ≤ x 1 ∧ (13/100 : ℝ) ≤ x 2 ∧
      (9/25 : ℝ) ≤ 1-∑ i, x i ∧ 1-∑ i, x i ≤ (601/1000 : ℝ)+4*b) :
    (∫ x in Ω, ZetaRieszFourInteriorBudget.density lam x) ≤
      (∫ v in ZetaRieszCapacityCover.region (outerBox lo), ZetaRieszFourCapacityCover.density lam v)+3200*b := by
  let D := ZetaRieszFourInteriorBudget.density lam
  let F := toFibres ⁻¹' fibreRegion (outerBox lo)
  let E := Ω ∩ {x | (601/1000 : ℝ) < 1-∑ i, x i}
  have hL' : (17/25 : ℝ) ≤ lam := hlo.trans hlam
  have hF : MeasurableSet F := (fibreRegion_measurable _).preimage toFibres.measurable
  have hE : MeasurableSet E := hΩ.inter (measurableSet_lt measurable_const (by fun_prop))
  have hunit : Ω ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
    intro x hx
    have g := hg x hx
    refine ⟨fun i => (g.1 i).le,fun i => ?_⟩
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (g.1 j).le) (Finset.mem_univ i)
    linarith [g.2.2.2.2.2.1]
  have hfinite : volume Ω ≠ ⊤ := by
    apply ne_of_lt ((measure_mono hunit).trans_lt ?_)
    simp [Real.volume_Icc_pi]
  have hiΩ : IntegrableOn D Ω := by
    apply Measure.integrableOn_of_bounded (M := (800 : ℝ)) hfinite ?_ ?_
    · change AEStronglyMeasurable (ZetaRieszFourInteriorBudget.density lam) _
      apply Measurable.aestronglyMeasurable
      unfold ZetaRieszFourInteriorBudget.density boxCap
      fun_prop
    · filter_upwards [ae_restrict_mem hΩ] with x hx
      have g := hg x hx
      have he := density_bounds hL' g.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1
      exact (Real.norm_of_nonneg he.1).trans_le he.2
  have hiF : IntegrableOn D F := by
    have hi' : IntegrableOn (fibre lam) (fibreRegion (outerBox lo)) :=
      (integrable_indicator_iff (fibreRegion_measurable _)).mp
        (integrable_fibre_indicator (outerBox lo) hL (fun _ => outerBox_geometry hlo))
    have ht := (toFibres_preserving.integrableOn_comp_preimage toFibres.measurableEmbedding).mpr hi'
    have he : D = fibre lam ∘ toFibres := funext (density_eq_fibre lam)
    rw [he]
    exact ht
  have hslab := norm_integral_largest_slab_le E hE (P := 601/1000) (w := 4*b)
    (by positivity) hL' (by
      intro x hx
      have g := hg x hx.1
      refine ⟨g.1,(hunit hx.1).2 0,(hunit hx.1).2 2,g.2.2.2.1,g.2.2.2.2.1,
        g.2.2.2.2.2.1,hx.2.le,g.2.2.2.2.2.2⟩)
  have hsplit : (∫ x in Ω, D x) = (∫ x in Ω ∩ F, D x)+(∫ x in E, D x) := by
    have hz : ∫ x in Ω \ (F ∪ E), D x = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      by_contra hn
      have g := hg x hx.1
      have hp : 1-∑ i, x i ≤ (601/1000 : ℝ) := by
        by_contra hp
        exact hx.2 (Or.inr ⟨hx.1,lt_of_not_ge hp⟩)
      exact hx.2 (Or.inl (ordered_mem_fibres hlam g.1 g.2.1 g.2.2.1 hp hn))
    have hdis : Disjoint (Ω ∩ F) E := by
      apply Set.disjoint_left.mpr
      intro x hx hxE
      have hp := ((Set.mem_pi.mp hx.2.1) 0 (Set.mem_univ 0)).2
      rw [toFibres_apply] at hp
      norm_num [outerBox] at hp
      have hxe : (601/1000 : ℝ) < 1-∑ i, x i := hxE.2
      simp only [Fin.sum_univ_three] at hxe
      linarith
    have he : Ω = ((Ω ∩ F) ∪ E) ∪ (Ω \ (F ∪ E)) := by
      ext x
      change (x ∈ Ω ↔ (x ∈ Ω ∧ x ∈ F ∨ x ∈ E) ∨ x ∈ Ω ∧ ¬(x ∈ F ∨ x ∈ E))
      have he : x ∈ E → x ∈ Ω := fun hx => hx.1
      tauto
    have hu := setIntegral_union hdis hE (hiΩ.mono_set Set.inter_subset_left)
      (hiΩ.mono_set Set.inter_subset_left)
    have hd : Disjoint ((Ω ∩ F) ∪ E) (Ω \ (F ∪ E)) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hy.2 (hx.elim (fun h => Or.inl h.2) Or.inr)
    have hsub : (Ω ∩ F) ∪ E ⊆ Ω := fun _ hx => hx.elim (fun h => h.1) (fun h => h.1)
    have hh := setIntegral_union hd (hΩ.diff (hF.union hE)) (hiΩ.mono_set hsub)
      (hiΩ.mono_set Set.sdiff_subset)
    rw [← he,hz,add_zero,hu] at hh
    exact hh
  have hm : (∫ x in Ω ∩ F, D x) ≤ ∫ x in F, D x := by
    apply setIntegral_mono_set hiF ?_ (Filter.Eventually.of_forall Set.inter_subset_right)
    filter_upwards [ae_restrict_mem hF] with x hx
    change 0 ≤ ZetaRieszFourInteriorBudget.density lam x
    rw [density_eq_fibre]
    have hp := outerBox_geometry hlo hx.1
    exact (fibre_bounds hL hp.1 hp.2.1 hp.2.2 hx.2.1 hx.2.2).1
  have hid := ordered_integral_eq (outerBox lo) hL (fun _ => outerBox_geometry hlo)
  change (∫ x in F, D x) = _ at hid
  rw [hsplit]
  have hEbound : (∫ x in E, D x) ≤ 3200*b := by
    have hn := le_abs_self (∫ x in E, D x)
    simp only [Real.norm_eq_abs] at hslab
    dsimp only [D] at hn ⊢
    linarith
  linarith

private theorem mem_cell {lo x : Fin 3 → ℝ} {b : ℝ} :
    x ∈ ZetaRieszFourInteriorBudget.cell lo b ↔ ∀ i, lo i < x i ∧ x i ≤ lo i+b := by
  simp [ZetaRieszFourInteriorBudget.cell]

private theorem measurable_cell (lo : Fin 3 → ℝ) (b : ℝ) :
    MeasurableSet (ZetaRieszFourInteriorBudget.cell lo b) :=
  (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

private theorem grid_cells_disjoint {M : ℕ} {a b : ℝ} (hb : 0 < b)
    {v w : Fin 3 → Fin M} (hne : v ≠ w) :
    Disjoint (ZetaRieszFourInteriorBudget.cell (gridLo a b v) b)
      (ZetaRieszFourInteriorBudget.cell (gridLo a b w) b) := by
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ w i := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  have hn : (v i : ℕ) ≠ (w i : ℕ) := fun h => hi (Fin.ext h)
  apply Set.disjoint_left.mpr
  intro x hv hw
  have hv := mem_cell.mp hv i
  have hw := mem_cell.mp hw i
  dsimp [gridLo] at hv hw
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hh : (v i : ℝ)+1 ≤ (w i : ℝ) := by exact_mod_cast hlt
    nlinarith
  · have hh : (w i : ℝ)+1 ≤ (v i : ℝ) := by exact_mod_cast hgt
    nlinarith

private theorem integral_cell_le {lam b : ℝ} {lo : Fin 3 → ℝ}
    (hb : 0 ≤ b) (hL : (17/25 : ℝ) ≤ lam) (hlo : ∀ i, 0 < lo i)
    (ha : (1/25 : ℝ) ≤ lo 1) (hq : (13/100 : ℝ) ≤ lo 2)
    (hp : (9/25 : ℝ) ≤ 1-∑ i, (lo i+b)) :
    (∫ x in ZetaRieszFourInteriorBudget.cell lo b,
      ZetaRieszFourInteriorBudget.density lam x) ≤ 800*b^3 := by
  have hf : volume (ZetaRieszFourInteriorBudget.cell lo b) ≠ ⊤ := by
    rw [ZetaRieszFourInteriorBudget.cell,Real.volume_pi_Ioc]
    exact ne_of_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))
  have hi := ZetaRieszFourInteriorBudget.integrableOn_density
    (by linarith : 0 < lam) hlo (by linarith : 0 < 1-∑ i, (lo i+b))
  have hm := setIntegral_mono_on hi (integrableOn_const hf) (measurable_cell lo b)
    (fun x hx => (density_bounds hL (fun i => (hlo i).trans (mem_cell.mp hx i).1)
      (ha.trans (mem_cell.mp hx 1).1.le) (hq.trans (mem_cell.mp hx 2).1.le)
      (hp.trans (sub_le_sub_left (Finset.sum_le_sum (fun i _ => (mem_cell.mp hx i).2)) _))).2)
  have hv : volume.real (ZetaRieszFourInteriorBudget.cell lo b) = b^3 := by
    rw [Measure.real,ZetaRieszFourInteriorBudget.cell,
      Real.volume_pi_Ioc_toReal (fun _ => le_add_of_nonneg_right hb)]
    simp only [add_sub_cancel_left,Fin.prod_univ_three]
    ring
  simpa only [setIntegral_const,hv,smul_eq_mul,mul_comm] using hm

/-- The refined mesh spends at most one billionth on both ordering
faces together. The exact repeated-index count is retained. -/
theorem fine_face_budget {b : ℝ} (hb : 0 < b) (hbu : b ≤ 1/249600000000) :
    (2*(⌈1/(3*b)⌉₊ : ℝ)^2)*(800*b^3) ≤ 1/1000000000 := by
  have hceil := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1/(3*b) by positivity)).le
  have hscaled : (⌈1/(3*b)⌉₊ : ℝ)*b ≤ 1/3+b := by
    have hh := mul_le_mul_of_nonneg_right hceil hb.le
    have he : (1/(3*b)+1)*b = 1/3+b := by field_simp
    rwa [he] at hh
  calc
    _ = 1600*((⌈1/(3*b)⌉₊ : ℝ)*b)^2*b := by ring
    _ ≤ 1600*(1/3+b)^2*b := by gcongr
    _ ≤ 1600*(1/3+(1/249600000000 : ℝ))^2*(1/249600000000) := by gcongr
    _ ≤ _ := by norm_num

/-- The complete nonempty ordered-index grid fits the certificate domain
with all ordering faces and largest-share excess paid. The additive
1/1000000000 is a single family budget; 3200*b retains the moving radial boundary. -/
theorem grid_integral_le {M : ℕ} (I : Finset (Fin 3 → Fin M)) {lo : ℚ} {lam a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hbT : b ≤ 1/249600000000)
    (hlo : (17/25 : ℝ) ≤ lo) (hlam : (lo : ℝ) ≤ lam) (hL : (693/1015 : ℝ) ≤ lam)
    (hI : ∀ v ∈ I, v 0 ≤ v 1 ∧ v 1 ≤ v 2)
    (hg : ∀ v ∈ I, (∀ i, 0 < gridLo a b v i) ∧
      (1/25 : ℝ) ≤ gridLo a b v 1 ∧ (13/100 : ℝ) ≤ gridLo a b v 2 ∧
      (9/25 : ℝ) ≤ 1-∑ i, (gridLo a b v i+b) ∧ gridLo a b v 2 < 1/3 ∧
      (∀ x ∈ ZetaRieszFourInteriorBudget.cell (gridLo a b v) b,
        1-∑ i, x i ≤ (601/1000 : ℝ)+4*b)) :
    (∫ x in ⋃ v ∈ I, ZetaRieszFourInteriorBudget.cell (gridLo a b v) b,
      ZetaRieszFourInteriorBudget.density lam x) ≤
      (∫ x in ZetaRieszCapacityCover.region (outerBox lo), ZetaRieszFourCapacityCover.density lam x)+
        1/1000000000+3200*b := by
  let C := fun v : Fin 3 → Fin M => ZetaRieszFourInteriorBudget.cell (gridLo a b v) b
  let D := ZetaRieszFourInteriorBudget.density lam
  let J := I.filter (fun v => v 0 < v 1 ∧ v 1 < v 2)
  let E := I.filter (fun v => ¬(v 0 < v 1 ∧ v 1 < v 2))
  have hJ : J ⊆ I := Finset.filter_subset _ _
  have hE : E ⊆ I := Finset.filter_subset _ _
  have hfinite (v : Fin 3 → Fin M) (hv : v ∈ I) : IntegrableOn D (C v) :=
    ZetaRieszFourInteriorBudget.integrableOn_density (by linarith : 0 < lam)
      (hg v hv).1 (by linarith [(hg v hv).2.2.2.1])
  have hdis : Set.Pairwise (I : Set (Fin 3 → Fin M)) (fun v w => Disjoint (C v) (C w)) :=
    fun _ _ _ _ he => grid_cells_disjoint hb he
  have hi := integral_biUnion_finset I (fun v _ => measurable_cell (gridLo a b v) b) hdis hfinite
  have hj := integral_biUnion_finset J (fun v _ => measurable_cell (gridLo a b v) b)
    (fun v hv w hw hne => hdis (hJ hv) (hJ hw) hne) (fun v hv => hfinite v (hJ hv))
  have hordered : (∫ x in ⋃ v ∈ J, C v, D x) ≤
      (∫ x in ZetaRieszCapacityCover.region (outerBox lo), ZetaRieszFourCapacityCover.density lam x)+3200*b := by
    apply ordered_integral_le (MeasurableSet.biUnion (Finset.countable_toSet J)
      (fun v _ => measurable_cell (gridLo a b v) b)) hb.le hlo hlam hL
    intro x hx
    obtain ⟨v,hv,hx⟩ := Set.mem_iUnion.mp hx |>.imp (fun _ h => Set.mem_iUnion.mp h)
    have g := hg v (hJ hv)
    have hh := mem_cell.mp hx
    have ho := (Finset.mem_filter.mp hv).2
    have h01 : gridLo a b v 0+b ≤ gridLo a b v 1 := by
      have he : (v 0 : ℝ)+1 ≤ (v 1 : ℝ) := by exact_mod_cast ho.1
      dsimp [gridLo]; nlinarith
    have h12 : gridLo a b v 1+b ≤ gridLo a b v 2 := by
      have he : (v 1 : ℝ)+1 ≤ (v 2 : ℝ) := by exact_mod_cast ho.2
      dsimp [gridLo]; nlinarith
    exact ⟨fun i => (g.1 i).trans (hh i).1,
      (hh 0).2.trans_lt (h01.trans_lt (hh 1).1),(hh 1).2.trans_lt (h12.trans_lt (hh 2).1),
      g.2.1.trans (hh 1).1.le,g.2.2.1.trans (hh 2).1.le,
      g.2.2.2.1.trans (sub_le_sub_left (Finset.sum_le_sum (fun i _ => (hh i).2)) _),
      g.2.2.2.2.2 x hx⟩
  have hc : E.card ≤ 2*(⌈1/(3*b)⌉₊)^2 := by
    apply repeated_index_card
    intro v hv
    have hgrid := hI v (hE hv)
    have g := hg v (hE hv)
    refine ⟨hgrid.1,hgrid.2,?_,?_⟩
    · apply Nat.lt_ceil.mpr
      apply (lt_div_iff₀ (show (0 : ℝ) < 3*b by positivity)).mpr
      dsimp [gridLo] at g
      nlinarith [g.2.2.2.2.1]
    · have hn := (Finset.mem_filter.mp hv).2
      by_contra hn'
      push Not at hn'
      exact hn ⟨lt_of_le_of_ne hgrid.1 hn'.1,lt_of_le_of_ne hgrid.2 hn'.2⟩
  have he : (∑ v ∈ E, ∫ x in C v, D x) ≤ 1/1000000000 := by
    have hs := Finset.sum_le_sum (fun v hv => integral_cell_le hb.le (hlo.trans hlam)
      (hg v (hE hv)).1 (hg v (hE hv)).2.1 (hg v (hE hv)).2.2.1 (hg v (hE hv)).2.2.2.1)
    have hcR : (E.card : ℝ) ≤ 2*(⌈1/(3*b)⌉₊ : ℝ)^2 := by exact_mod_cast hc
    have hn := fine_face_budget hb hbT
    have htotal := mul_le_mul_of_nonneg_right hcR (show 0 ≤ 800*b^3 by positivity)
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    exact (hs.trans htotal).trans hn
  have hsplit := Finset.sum_filter_add_sum_filter_not I (fun v => v 0 < v 1 ∧ v 1 < v 2)
    (fun v => ∫ x in C v, D x)
  change _ = (∑ v ∈ J, ∫ x in C v, D x) at hj
  change (∑ v ∈ J, ∫ x in C v, D x)+(∑ v ∈ E, ∫ x in C v, D x) = _ at hsplit
  change (∫ x in ⋃ v ∈ I, C v, D x) ≤ _
  rw [hi,← hsplit,← hj]
  linarith

/-- Actual nonempty cells discharge every geometric assumption of the
certificate comparison. No continuum support condition is assumed for
prime labels, and the moving total-log boundary is retained. -/
theorem active_grid_integral_le (S : Finset ℕ) (M : ℕ) {lo : ℚ} {L t h y a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) (hhb : h/t ≤ b) (hbT : b ≤ 1/249600000000)
    (hL : (693/1015 : ℝ)*t ≤ L) (hLt : L ≤ t)
    (hlo : (17/25 : ℝ) ≤ lo) (hlam : (lo : ℝ) ≤ L/t) :
    let I := (gridCover M (t*a) (t*b) t).filter (fun v =>
      (boundaryCell (clippedSupport S) L t h y
        (fun i => t*gridLo a b v i) (fun _ => t*b)).Nonempty)
    (∫ x in ⋃ v ∈ I, ZetaRieszFourInteriorBudget.cell (gridLo a b v) b,
      ZetaRieszFourInteriorBudget.density (L/t) x) ≤
      (∫ x in ZetaRieszCapacityCover.region (outerBox lo), ZetaRieszFourCapacityCover.density (L/t) x)+
        1/1000000000+3200*b := by
  dsimp only
  apply grid_integral_le _ ha.le hb hbT hlo hlam ((le_div_iff₀ ht).mpr hL)
  · intro v hv
    have hg := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
    exact ⟨hg.1,hg.2.1⟩
  · intro v hv
    have hn := (Finset.mem_filter.mp hv).2
    have hwidth : h ≤ t*b := by simpa only [mul_comm] using (div_le_iff₀ ht).mp hhb
    have g := active_cell_geometry S hwidth (by nlinarith : t*b ≤ t/249600) hL hLt hn
    refine ⟨fun i => ha.trans_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb.le)),
      ?_,?_,?_,?_,fun x hx => active_largest_upper S ht hhb hn hx⟩
    all_goals simp only [Fin.sum_univ_three] at g ⊢
    all_goals nlinarith [g.1,g.2.1,g.2.2.1,g.2.2.2]

/-- Signed arithmetic transfer of the complete angular upper certificate.
The literal adverse population, original factorial/phase factor and every
mask stay unchanged. The entire covering excess is explicitly paid. -/
theorem eventually_population_capacity_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (M : ℕ) (L t y a b : ℝ) (lo : ℚ),
      0 < t → 0 < a → 0 < b → h/t ≤ b → b ≤ 1/249600000000 →
      1000000000*b ≤ a → (693/1015 : ℝ)*(t+h) ≤ L → L ≤ t →
      2*(t+h) ≤ 3*L → α*N ≤ t*a → β*N ≤ t*b → α*N ≤ t/4 →
      t+h ≤ t*a+M*(t*b) → (17/25 : ℝ) ≤ lo → (lo : ℝ) ≤ L/t →
      -(((1003/1000 : ℝ)*
          ((∫ x in ZetaRieszCapacityCover.region (outerBox lo),
            ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+3200*b)+1/100000)*
        ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (∑ n ∈ adversePopulation (clippedSupport S) L t h y (t*a),
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [ZetaRieszFourInteriorBudget.eventually_complete_integral_floor hh hhu hα hβ]
    with N hN S A M L t y a b lo ht ha hb hhb hbT hab hL hLt hTc hlogs hwidth hmin hcover hlo hlam
  have hf := hN S A M L t y a b ht ha hb hhb (by linarith : b ≤ 1/249600) hab hL hLt hTc hlogs hwidth hmin hcover
  have hg := active_grid_integral_le S M (y := y) ht ha hb hhb hbT (by linarith : (693/1015 : ℝ)*t ≤ L)
    hLt hlo hlam
  dsimp only at hf hg
  have hE : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (-Real.cos (y*t))+|y| * h)*h := by positivity
  have hbnd := mul_le_mul_of_nonneg_right
    (add_le_add_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 1003/1000)) (1/100000)) hE
  simpa only [add_comm] using
    (neg_le_neg hbnd).trans (by simpa only [add_comm] using hf)

/-- The exact capacity-domain floor on the original dyadic core. Every
clipped adverse four-prime label above log p>delta*N is paid by the complete
angular integral, one ordering allowance and an explicit tiny largest-share
excess. The full original signed complement remains in the same inequality. -/
theorem eventually_core_capacity_floor {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ (t y : ℝ) (lo : ℚ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let P := clippedSupport S
      let Q := adversePopulation P L t h y (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (17/25 : ℝ) ≤ lo → (lo : ℝ) ≤ L/t →
      (∑ n ∈ S\Q, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (((1003/1000 : ℝ)*
          ((∫ x in ZetaRieszCapacityCover.region (outerBox lo),
            ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  let β := δ/1000000000
  let M := ⌈3000000000/δ⌉₊
  have hβ : 0 < β := by dsimp [β]; positivity
  have hM : (3 : ℝ) ≤ M*β := by
    have he := Nat.le_ceil (3000000000/δ)
    have hm := mul_le_mul_of_nonneg_right he hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at hm
    dsimp [M,β]
    nlinarith
  have hwidth : ∀ᶠ N : ℕ in atTop, h ≤ β*N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hβ).eventually_ge_atTop h
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_population_capacity_floor hh hhu hδ hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU (h := h)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hwidth,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hN hch hratio hwidth hj t y lo
  dsimp only
  intro htlo hthi hlo hlam
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let a := δ*N/t
  let b := β*N/t
  let P := clippedSupport S
  let Q := adversePopulation P L t h y (δ*N)
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hj
  have ht : 0 < t := by nlinarith
  have hn0 : (0 : ℝ) ≤ N := by positivity
  have hδN := mul_le_mul_of_nonneg_right hδu hn0
  have hta : t*a = δ*N := mul_div_cancel₀ _ ht.ne'
  have htb : t*b = β*N := mul_div_cancel₀ _ ht.ne'
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hsmall : b ≤ 1/249600000000 := by
    apply (div_le_iff₀ ht).mpr
    dsimp [β]
    nlinarith
  have hmesh : 1000000000*b ≤ a := by dsimp [a,b,β]; ring_nf; rfl
  have hch' := hch t htlo hthi
  have hcut := (le_div_iff₀ (show 0 < t+h by linarith)).mp
    (hratio (t+h) (by linarith) hthi).1
  have hcover := mul_le_mul_of_nonneg_right hM hn0
  have hf := hN S A M L t y a b lo ht ha hb
    (by exact div_le_div_of_nonneg_right hwidth ht.le) hsmall hmesh hcut hch'.1 hch'.2
    (by rw [hta]) (by rw [htb]) (by nlinarith)
    (by rw [hta,htb]; nlinarith [mul_nonneg hδ.le hn0]) hlo hlam
  have hsmall_cost : 3200*b ≤ (1/78000000 : ℝ) := by
    change 3200*(β*N/t) ≤ _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ ht).mpr
    dsimp [β]
    nlinarith
  have hE : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (-Real.cos (y*t))+|y| * h)*h := by positivity
  have hbnd := mul_le_mul_of_nonneg_right
    (add_le_add_right (mul_le_mul_of_nonneg_left
      (add_le_add_left hsmall_cost
        ((∫ x in ZetaRieszCapacityCover.region (outerBox lo), ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000))
      (by norm_num : (0 : ℝ) ≤ 1003/1000)) (1/100000)) hE
  have hf := (neg_le_neg hbnd).trans (by simpa only [add_comm] using hf)
  rw [hta,add_comm (Complex.I*(y : ℂ)) (3/2)] at hf
  have hQS : Q ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hQS)
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  change _ ≤ (∑ n ∈ Q, f n).re at hf
  linarith


end
end RiemannGaussian.ZetaRieszFourAngularDomain
