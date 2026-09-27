/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveAngularIncidence
import RiemannGaussian.ZetaRieszFiveCapacityCover
import RiemannGaussian.ZetaRieszFourAngularDomain

/-!
# Exact five-prime certificate transfer to the literal signed carrier

The six-incidence budget is identified with the two-dimensional certificate
by a unit-Jacobian coordinate change and two genuine Fubini exchanges.
Every curved boundary and the one-half multiplicity factor remain exact.
The resulting literal prime-sum floor keeps its original radial/phase
factor, allocation and all complementary labels. Exhaustive numerical
assemblies stay optional and outside the ordinary root.
-/

namespace RiemannGaussian.ZetaRieszFiveAngularDomain
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFiveAngularIncidence ZetaRieszFiveCapacityCover

/-- Every certificate fibre lies inside the same unordered padded chamber. -/
theorem fibre_mem_unordered {lo hi v z r a : ℝ}
    (hz : z ≤ 1/2) (hA : admissible lo hi v z)
    (hr : max (1/100 : ℝ) (max (1-v-z-z) (1-v-z-v/2)) ≤ r ∧ r ≤ (1-v-z)/2)
    (ha : max (1-v-z-r) (max (1-lo-z) (v-1/2)) ≤ a ∧
      a ≤ v-max (1-v-z-r) (max (1-lo-z) (v-1/2))) :
    ![r,1-v-z-r,a,v-a] ∈ unorderedRegion lo hi := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉,h₁₀,h₁₁⟩ := pair_geometry hA hr ha
  change (1/100 : ℝ) ≤ r ∧ r ≤ 1-v-z-r ∧
    1-v-z-r ≤ a ∧ 1-v-z-r ≤ v-a ∧
    1-v-z-r ≤ 1-r-(1-v-z-r)-a-(v-a) ∧
    a ≤ 1/2 ∧ v-a ≤ 1/2 ∧ 1-r-(1-v-z-r)-a-(v-a) ≤ 1/2 ∧
    1-a-(v-a) ≤ lo ∧ 1-a-(1-r-(1-v-z-r)-a-(v-a)) ≤ lo ∧
    1-(v-a)-(1-r-(1-v-z-r)-a-(v-a)) ≤ lo ∧ hi ≤ 1-(1-v-z-r)-r
  exact ⟨h₁,h₂,h₃,h₄,by linarith,h₆,h₇,by linarith,by linarith,
    by linarith,by linarith,by linarith⟩

/-- The certificate coordinates preserve the exact cap and five-share denominator. -/
theorem fibre_pairDensity (lo hi v z r a : ℝ) :
    pairDensity lo hi ![r,1-v-z-r,a,v-a] =
      min r (max 0 (min (lo-v) (1-hi-z)))/(hi*z*r*(1-v-z-r)*a*(v-a)) := by
  have hp : owner ![r,1-v-z-r,a,v-a] = z := by dsimp [owner]; ring
  unfold pairDensity
  rw [hp]
  have hc : cap lo hi ![r,1-v-z-r,a,v-a] z =
      min r (max 0 (min (lo-v) (1-hi-z))) := by
    dsimp [cap]
    congr 2
    congr 1
    ring
  rw [hc]
  congr 1
  dsimp [denominator,owner]
  ring


/-- The affine map from four cofactor shares to pair sum, third large share, least share and pair coordinate. -/
def coordinates : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) where
  toFun x := ![x 2+x 3,owner x,x 0,x 2]
  invFun y := ![y 2,1-y 0-y 1-y 2,y 3,y 0-y 3]
  left_inv x := by
    ext i
    fin_cases i
    · rfl
    · change 1-(x 2+x 3)-owner x-x 0 = x 1
      dsimp [owner]; ring
    · rfl
    · change x 2+x 3-x 2 = x 3
      ring
  right_inv x := by
    ext i
    fin_cases i
    · change x 3+(x 0-x 3) = x 0
      ring
    · change owner ![x 2,1-x 0-x 1-x 2,x 3,x 0-x 3] = x 1
      dsimp [owner]; ring
    · rfl
    · rfl
  measurable_toFun := by
    change Measurable (fun x : Fin 4 → ℝ => ![x 2+x 3,owner x,x 0,x 2])
    unfold owner
    fun_prop
  measurable_invFun := by
    change Measurable (fun y : Fin 4 → ℝ => ![y 2,1-y 0-y 1-y 2,y 3,y 0-y 3])
    fun_prop

/-- The affine certificate coordinate change has determinant minus one and preserves volume. -/
theorem coordinates_preserving : MeasurePreserving coordinates := by
  let M : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,1,1; -1,-1,-1,-1; 1,0,0,0; 0,0,1,0]
  have hdet : M.det = -1 := by
    have hcol (i : Fin 4) : M i 1 = if i = 1 then -1 else 0 := by
      fin_cases i <;> norm_num [M,Fin.ext_iff]
    have hminor : M.submatrix (1 : Fin 4).succAbove (1 : Fin 4).succAbove =
        !![0,1,1; 1,0,0; 0,1,0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.det_succ_column M 1]
    simp_rw [hcol,mul_ite,ite_mul,mul_zero,zero_mul]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [hminor,Matrix.det_fin_three]
    change (-1 : ℝ)^(1+1)*(-1)*(0*0*0-0*0*1-1*1*0+1*0*0+1*1*1-1*0*0) = -1
    norm_num

  have hlin : MeasurePreserving (Matrix.toLin' M) := by
    refine ⟨(LinearMap.continuous_on_pi _).measurable,?_⟩
    simpa only [hdet,inv_neg,inv_one,abs_neg,abs_one,ENNReal.ofReal_one,one_smul] using
      Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) (by rw [hdet]; norm_num)
  have he := (measurePreserving_add_left (volume : Measure (Fin 4 → ℝ)) ![0,1,0,0]).comp hlin
  have hf : ((fun x : Fin 4 → ℝ => ![0,1,0,0]+x) ∘ Matrix.toLin' M) = coordinates := by
    funext x
    change ![0,1,0,0]+Matrix.toLin' M x = ![x 2+x 3,owner x,x 0,x 2]
    rw [Matrix.toLin'_apply]
    ext i
    fin_cases i <;> simp [M,dotProduct,Fin.sum_univ_four,owner]; ring
  rw [hf] at he
  exact he

/-- Split the four certificate coordinates into the two outer variables and two scalar fibres. -/
def splitCoordinates : (Fin 4 → ℝ) ≃ᵐ (((Fin 2 → ℝ) × ℝ) × ℝ) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 3).trans
    MeasurableEquiv.prodComm).trans
      (ZetaRieszFourAngularDomain.splitCoordinates.prodCongr (MeasurableEquiv.refl ℝ))

/-- The product-coordinate split retains each labelled share exactly. -/
theorem splitCoordinates_apply (x : Fin 4 → ℝ) :
    splitCoordinates x = ((![x 0,x 1],x 2),x 3) := by
  change (((fun i => x ((3 : Fin 4).succAbove ((2 : Fin 3).succAbove i))),
    x ((3 : Fin 4).succAbove 2)),x 3) = _
  congr 1
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · rfl

/-- The ordinary product-coordinate split preserves volume. -/
theorem splitCoordinates_preserving : MeasurePreserving splitCoordinates := by
  have h3 : MeasurePreserving ZetaRieszFourAngularDomain.splitCoordinates :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans Measure.measurePreserving_swap
  have hp := h3.prod (MeasurePreserving.id (volume : Measure ℝ))
  exact ((volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 3).trans
    Measure.measurePreserving_swap).trans hp

/-- The exact affine and product change of variables for the certificate integral. -/
def toFibres : (Fin 4 → ℝ) ≃ᵐ (((Fin 2 → ℝ) × ℝ) × ℝ) :=
  coordinates.trans splitCoordinates

/-- The complete cofactor-to-fibre map has unit absolute Jacobian. -/
theorem toFibres_preserving : MeasurePreserving toFibres :=
  coordinates_preserving.trans splitCoordinates_preserving

/-- The inverse recovers every original cofactor share, including its complement. -/
theorem toFibres_symm_apply (v : ((Fin 2 → ℝ) × ℝ) × ℝ) :
    toFibres.symm v = ![v.1.2,1-v.1.1 0-v.1.1 1-v.1.2,v.2,v.1.1 0-v.2] := by
  apply toFibres.injective
  rw [MeasurableEquiv.apply_symm_apply]
  change v = splitCoordinates (coordinates _)
  rw [splitCoordinates_apply]
  apply Prod.ext
  · apply Prod.ext
    · ext i
      fin_cases i
      · change v.1.1 0 = v.2+(v.1.1 0-v.2)
        ring
      · change v.1.1 1 = owner ![v.1.2,1-v.1.1 0-v.1.1 1-v.1.2,v.2,v.1.1 0-v.2]
        dsimp [owner]; ring
    · rfl
  · rfl


/-- The literal one-pair angular credit before its two scalar integrations. -/
def pairFibre (lo hi : ℝ) (v : ((Fin 2 → ℝ) × ℝ) × ℝ) : ℝ :=
  min v.1.2 (max 0 (min (lo-v.1.1 0) (1-hi-v.1.1 1)))/
    (hi*v.1.1 1*v.1.2*(1-v.1.1 0-v.1.1 1-v.1.2)*v.2*(v.1.1 0-v.2))

/-- The transformed integrand equals the original pair density exactly. -/
theorem pairFibre_eq_density (lo hi : ℝ) (v : ((Fin 2 → ℝ) × ℝ) × ℝ) :
    pairFibre lo hi v = pairDensity lo hi (toFibres.symm v) := by
  rw [toFibres_symm_apply,fibre_pairDensity]
  rfl

/-- The certificate domain with both half-open scalar fibres and its admissibility guard retained. -/
def fibreRegion (B : ZetaRieszCapacityCover.Box) (lo hi : ℝ) :
    Set (((Fin 2 → ℝ) × ℝ) × ℝ) := {v |
  v.1.1 ∈ ZetaRieszCapacityCover.region B ∧ admissible lo hi (v.1.1 0) (v.1.1 1) ∧
  max (1/100 : ℝ) (max (1-v.1.1 0-v.1.1 1-v.1.1 1)
    (1-v.1.1 0-v.1.1 1-v.1.1 0/2)) < v.1.2 ∧
  v.1.2 ≤ (1-v.1.1 0-v.1.1 1)/2 ∧
  max (1-v.1.1 0-v.1.1 1-v.1.2) (max (1-lo-v.1.1 1) (v.1.1 0-1/2)) < v.2 ∧
  v.2 ≤ v.1.1 0-max (1-v.1.1 0-v.1.1 1-v.1.2) (max (1-lo-v.1.1 1) (v.1.1 0-1/2))}

/-- All curved fibre endpoints and the outer box form a measurable domain. -/
theorem fibreRegion_measurable (B : ZetaRieszCapacityCover.Box) (lo hi : ℝ) :
    MeasurableSet (fibreRegion B lo hi) := by
  have hB : MeasurableSet (ZetaRieszCapacityCover.region B) :=
    (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))
  unfold fibreRegion admissible
  simp only [Set.ofPred_and]
  refine ((hB.preimage (measurable_fst.comp measurable_fst)).inter ?_)
  measurability

/-- Each complete fibre remains inside the incidence comparison chamber. -/
theorem fibreRegion_mem_unordered (B : ZetaRieszCapacityCover.Box) {lo hi : ℝ}
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 1 ≤ (1/2 : ℝ))
    {v : ((Fin 2 → ℝ) × ℝ) × ℝ} (hv : v ∈ fibreRegion B lo hi) :
    toFibres.symm v ∈ unorderedRegion lo hi := by
  rw [toFibres_symm_apply]
  exact fibre_mem_unordered (hB v.1.1 hv.1) hv.2.1
    ⟨hv.2.2.1.le,hv.2.2.2.1⟩ ⟨hv.2.2.2.2.1.le,hv.2.2.2.2.2⟩

/-- A fixed positive least share bounds the exact density, independently of the moment or phase. -/
theorem pairFibre_bounds {lo hi : ℝ} {v : ((Fin 2 → ℝ) × ℝ) × ℝ}
    (hhi : (17/25 : ℝ) ≤ hi)
    (hA : admissible lo hi (v.1.1 0) (v.1.1 1))
    (hr : max (1/100 : ℝ) (max (1-v.1.1 0-v.1.1 1-v.1.1 1)
        (1-v.1.1 0-v.1.1 1-v.1.1 0/2)) ≤ v.1.2 ∧ v.1.2 ≤ (1-v.1.1 0-v.1.1 1)/2)
    (ha : max (1-v.1.1 0-v.1.1 1-v.1.2) (max (1-lo-v.1.1 1) (v.1.1 0-1/2)) ≤ v.2 ∧
      v.2 ≤ v.1.1 0-max (1-v.1.1 0-v.1.1 1-v.1.2) (max (1-lo-v.1.1 1) (v.1.1 0-1/2))) :
    0 ≤ pairFibre lo hi v ∧ pairFibre lo hi v ≤ 1000000000000 := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,_h₈,_h₉,_h₁₀,_h₁₁⟩ := pair_geometry hA hr ha
  have hb : (1/100 : ℝ) ≤ 1-v.1.1 0-v.1.1 1-v.1.2 := h₁.trans h₂
  have hr0 : 0 ≤ v.1.2 := by linarith
  have hr1 : v.1.2 ≤ 1 := by linarith
  have hz0 : 0 ≤ v.1.1 1 := by linarith
  have ha0 : 0 ≤ v.2 := by linarith
  have hq0 : 0 ≤ v.1.1 0-v.2 := by linarith
  have hb0 : 0 ≤ 1-v.1.1 0-v.1.1 1-v.1.2 := by linarith
  have hd : (17/25 : ℝ)*(1/100)^5 ≤
      hi*v.1.1 1*v.1.2*(1-v.1.1 0-v.1.1 1-v.1.2)*v.2*(v.1.1 0-v.2) := by
    have h1 := mul_le_mul hhi (hb.trans h₅) (by norm_num) (by linarith)
    have h2 := mul_le_mul h1 h₁ (by norm_num) (by positivity)
    have h3 := mul_le_mul h2 hb (by norm_num) (by positivity)
    have h4 := mul_le_mul h3 (hb.trans h₃) (by norm_num) (by positivity)
    have h5 := mul_le_mul h4 (hb.trans h₄) (by norm_num) (by positivity)
    norm_num at h5 ⊢
    exact h5
  have hd0 : 0 < hi*v.1.1 1*v.1.2*(1-v.1.1 0-v.1.1 1-v.1.2)*v.2*(v.1.1 0-v.2) := by
    linarith
  constructor
  · exact div_nonneg (le_min hr0 (le_max_left _ _)) hd0.le
  · apply (div_le_iff₀ hd0).mpr
    have hc := min_le_left (v.1.2) (max 0 (min (lo-v.1.1 0) (1-hi-v.1.1 1)))
    nlinarith


/-- The bounded density and finite product volume justify both Fubini exchanges. -/
theorem integrable_fibre_indicator (B : ZetaRieszCapacityCover.Box) {lo hi : ℝ}
    (hhi : (17/25 : ℝ) ≤ hi) :
    Integrable ((fibreRegion B lo hi).indicator (pairFibre lo hi)) := by
  have hsub : fibreRegion B lo hi ⊆
      (ZetaRieszCapacityCover.region B ×ˢ Set.Icc (0 : ℝ) 1) ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro v hv
    have hg := pair_geometry hv.2.1
      ⟨hv.2.2.1.le,hv.2.2.2.1⟩ ⟨hv.2.2.2.2.1.le,hv.2.2.2.2.2⟩
    refine ⟨⟨hv.1,⟨?_,?_⟩⟩,⟨?_,?_⟩⟩
    · linarith [hg.1]
    · linarith [hg.2.1,hg.2.2.1,hg.2.2.2.2.2.1]
    · linarith [hg.1,hg.2.1,hg.2.2.1]
    · linarith [hg.2.2.2.2.2.1]
  have hBfin : volume (ZetaRieszCapacityCover.region B) < ⊤ := by
    rw [ZetaRieszCapacityCover.region,Real.volume_pi_Ioc]
    exact ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)
  have hfin : volume (fibreRegion B lo hi) ≠ ⊤ := by
    apply ne_of_lt ((measure_mono hsub).trans_lt ?_)
    rw [Measure.volume_eq_prod,Measure.prod_prod,Measure.volume_eq_prod,Measure.prod_prod]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hBfin (by simp)) (by simp)
  have hI : IntegrableOn (pairFibre lo hi) (fibreRegion B lo hi) := by
    apply Measure.integrableOn_of_bounded (M := (1000000000000 : ℝ)) hfin
    · apply Measurable.aestronglyMeasurable
      unfold pairFibre
      fun_prop
    · filter_upwards [ae_restrict_mem (fibreRegion_measurable B lo hi)] with v hv
      have hb := pairFibre_bounds hhi hv.2.1
        ⟨hv.2.2.1.le,hv.2.2.2.1⟩ ⟨hv.2.2.2.2.1.le,hv.2.2.2.2.2⟩
      exact (Real.norm_of_nonneg hb.1).trans_le hb.2
  exact hI.integrable_indicator (fibreRegion_measurable B lo hi)

/-- The complete certificate fibre budget fits inside the ordered three-cap supply. -/
theorem half_integral_fibre_le (B : ZetaRieszCapacityCover.Box) {lam lo hi : ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hlo : lo ≤ lam) (hhi : lam ≤ hi)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 1 ≤ (1/2 : ℝ)) :
    (1/2 : ℝ)*(∫ v in fibreRegion B lo hi, pairFibre lo hi v) ≤
      ∫ x in ZetaRieszFiveAngularBoundary.orderedRegion lo hi,
        ZetaRieszFiveInteriorBudget.density lam x := by
  have hE := (fibreRegion_measurable B lo hi).preimage toFibres.measurable
  have hsub : toFibres ⁻¹' fibreRegion B lo hi ⊆ unorderedRegion lo hi := by
    intro x hx
    simpa only [MeasurableEquiv.symm_apply_apply] using fibreRegion_mem_unordered B hB hx
  have hf := half_integral_pairDensity_le hL hlo hhi
    (toFibres ⁻¹' fibreRegion B lo hi) hE hsub
  have he := toFibres_preserving.setIntegral_preimage_emb toFibres.measurableEmbedding
    (pairFibre lo hi) (fibreRegion B lo hi)
  simp only [pairFibre_eq_density,MeasurableEquiv.symm_apply_apply] at he
  rw [he] at hf
  simpa only [pairFibre_eq_density] using hf


/-- The exact one-half incidence factor cancels the symmetric pair integral, with both endpoints retained. -/
theorem inner_fibre_integral (B : ZetaRieszCapacityCover.Box) {lo hi : ℝ}
    {x : Fin 2 → ℝ} {r : ℝ} (hx : x ∈ ZetaRieszCapacityCover.region B)
    (hv : x 0 ≤ 1) (hA : admissible lo hi (x 0) (x 1))
    (hr : r ∈ Set.Ioc (max (1/100 : ℝ) (max (1-x 0-x 1-x 1) (1-x 0-x 1-x 0/2)))
      ((1-x 0-x 1)/2)) :
    (1/2 : ℝ)*(∫ a : ℝ, (fibreRegion B lo hi).indicator (pairFibre lo hi) ((x,r),a)) =
      fibre lo hi (x 0) (x 1) r/(hi*x 0*x 1) := by
  let d := max (1-x 0-x 1-r) (max (1-lo-x 1) (x 0-1/2))
  have he : (fun a : ℝ => (fibreRegion B lo hi).indicator (pairFibre lo hi) ((x,r),a)) =
      (Set.Ioc d (x 0-d)).indicator (fun a => pairFibre lo hi ((x,r),a)) := by
    funext a
    simp only [fibreRegion,Set.indicator,Set.mem_ofPred_eq,Set.mem_Ioc,
      hx,hA,hr.1,hr.2,true_and,d]
  rw [he,integral_indicator measurableSet_Ioc]
  have hd := pair_boundary_bounds hv hA ⟨hr.1.le,hr.2⟩
  have hle : d ≤ x 0-d := by dsimp [d]; linarith [hd.2]
  rw [← intervalIntegral.integral_of_le hle]
  exact (fibre_eq_half_pair_integral (by norm_num : (0 : ℝ) < 1/100) hv hA
    ⟨hr.1.le,hr.2⟩).symm


/-- Two justified Fubini exchanges identify the pair budget with the actual two-dimensional certificate integral. -/
theorem half_integral_fibre_eq (B : ZetaRieszCapacityCover.Box) {lo hi : ℝ}
    (hhi : (17/25 : ℝ) ≤ hi)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 0 ≤ (1 : ℝ)) :
    (1/2 : ℝ)*(∫ v in fibreRegion B lo hi, pairFibre lo hi v) =
      ∫ x in ZetaRieszCapacityCover.region B,
        ZetaRieszFiveCapacityCover.density lo hi (1/100) x := by
  let f := (fibreRegion B lo hi).indicator (pairFibre lo hi)
  have houter (x : Fin 2 → ℝ) :
      (∫ r : ℝ, (1/2 : ℝ)*(∫ a : ℝ, f ((x,r),a))) =
      (ZetaRieszCapacityCover.region B).indicator
        (ZetaRieszFiveCapacityCover.density lo hi (1/100)) x := by
    by_cases hx : x ∈ ZetaRieszCapacityCover.region B
    · rw [Set.indicator_of_mem hx]
      by_cases hA : admissible lo hi (x 0) (x 1)
      · let I := Set.Ioc (max (1/100 : ℝ) (max (1-x 0-x 1-x 1) (1-x 0-x 1-x 0/2)))
          ((1-x 0-x 1)/2)
        have he : (fun r : ℝ => (1/2 : ℝ)*(∫ a : ℝ, f ((x,r),a))) =
            I.indicator (fun r => fibre lo hi (x 0) (x 1) r/(hi*x 0*x 1)) := by
          funext r
          by_cases hr : r ∈ I
          · rw [Set.indicator_of_mem hr]
            exact inner_fibre_integral B hx (hB x hx) hA hr
          · rw [Set.indicator_of_notMem hr]
            have hz (a : ℝ) : f ((x,r),a) = 0 :=
              Set.indicator_of_notMem (fun hv => hr ⟨hv.2.2.1,hv.2.2.2.1⟩) _
            simp_rw [hz,integral_zero,mul_zero]
        rw [he,integral_indicator measurableSet_Ioc,integral_div]
        exact (if_pos hA).symm
      · have hz (r a : ℝ) : f ((x,r),a) = 0 :=
          Set.indicator_of_notMem (fun hv => hA hv.2.1) _
        simp_rw [hz,integral_zero,mul_zero]
        rw [integral_zero]
        exact (if_neg hA).symm
    · rw [Set.indicator_of_notMem hx]
      have hz (r a : ℝ) : f ((x,r),a) = 0 :=
        Set.indicator_of_notMem (fun hv => hx hv.1) _
      simp_rw [hz,integral_zero,mul_zero]
      rw [integral_zero]
  have hI := integrable_fibre_indicator (lo := lo) B hhi
  rw [← integral_indicator (fibreRegion_measurable B lo hi)]
  change (1/2 : ℝ)*(∫ v, f v) = _
  rw [Measure.volume_eq_prod] at hI ⊢
  rw [integral_prod _ hI]
  have hI2 := hI.integral_prod_left
  rw [Measure.volume_eq_prod] at hI2 ⊢
  rw [integral_prod _ hI2,← integral_const_mul]
  have hBmeas : MeasurableSet (ZetaRieszCapacityCover.region B) :=
    (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))
  rw [← integral_indicator hBmeas]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  exact houter x


/-- The exact integral in the optional certificate is a lower bound on
the full ordered favorable density at every cutoff in the padded bin. -/
theorem supply_integral_le_ordered (B : ZetaRieszCapacityCover.Box) {lam lo hi : ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hlo : lo ≤ lam) (hhi : lam ≤ hi)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ)) :
    (∫ x in ZetaRieszCapacityCover.region B,
      ZetaRieszFiveCapacityCover.density lo hi (1/100) x) ≤
      ∫ x in ZetaRieszFiveAngularBoundary.orderedRegion lo hi,
        ZetaRieszFiveInteriorBudget.density lam x := by
  rw [← half_integral_fibre_eq B (hL.trans hhi) (fun x hx => (hB x hx).1)]
  exact half_integral_fibre_le B hL hlo hhi (fun x hx => (hB x hx).2)

/-- The actual two-dimensional certificate integral supplies a literal
five-prime core credit after the already paid 1/50000 angular cost.
No extra loss is charged for incidence, domain transport or Fubini.
The original signed complement and every arithmetic mask are retained. -/
theorem eventually_core_capacity_floor (B : ZetaRieszCapacityCover.Box) {u h b lo hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b)
    (hlo : (17/25 : ℝ) ≤ lo)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ)) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N → lo ≤ L/t → L/t ≤ hi →
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (((996/1000 : ℝ)*(∫ x in ZetaRieszCapacityCover.region B,
          ZetaRieszFiveCapacityCover.density lo hi (1/100) x)-1/50000)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [ZetaRieszFiveAngularBoundary.eventually_ordered_region_core_floor
    (lo := lo) (hi := hi) hu hU hh hhu hb hsmall hcover] with j hJ t y
  dsimp only
  intro htlo hthi hlt htl
  have hf := hJ t y htlo hthi hlt htl
  have hc := supply_integral_le_ordered B (hlo.trans hlt) hlt htl hB
  have ht : 0 ≤ t := (show 0 ≤ (39/20 : ℝ)*
    ZetaRieszPrimeCountFrequency.dyadicMomentOrder j by positivity).trans htlo
  have hnum := sub_le_sub_right (mul_le_mul_of_nonneg_left hc
    (by norm_num : (0 : ℝ) ≤ 996/1000)) (1/50000)
  have hmul := mul_le_mul_of_nonneg_right hnum
    (show 0 ≤ (Real.exp (-(t+h)/2)*t^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*
        max 0 (-Real.cos (y*t)-|y| * h)*h by positivity)
  linarith only [hmul,hf]


end
end RiemannGaussian.ZetaRieszFiveAngularDomain
