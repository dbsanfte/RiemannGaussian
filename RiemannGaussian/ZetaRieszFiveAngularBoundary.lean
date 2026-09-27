/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveInteriorBudget
import Mathlib.MeasureTheory.Group.Integral

/-!
# Boundary budgets for the favorable five-prime angular transfer

The fixed least-prime cutoff separates every denominator from zero.
Explicit affine slab estimates pay the ordering and saturation faces of
the disjoint literal prime-cell family, within one angular error budget.
-/

namespace RiemannGaussian.ZetaRieszFiveAngularBoundary
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFivePrimeCells ZetaRieszFiveInteriorBudget

/-- Replacing one coordinate by an affine functional with unit coefficient
in that coordinate gives a slab of volume at most its width in the unit
cube. This will pay all literal ordering and saturation boundaries. -/
theorem volume_affine_slab_le (S : Set (Fin 4 → ℝ)) (a : Fin 4 → ℝ)
    (i : Fin 4) (c l w : ℝ) (ha : |a i| = 1)
    (hS : ∀ x ∈ S, (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
      l ≤ c+∑ j, a j*x j ∧ c+∑ j, a j*x j ≤ l+w) :
    volume S ≤ ENNReal.ofReal w := by
  let M : Matrix (Fin 4) (Fin 4) ℝ := (1 : Matrix (Fin 4) (Fin 4) ℝ).updateRow i a
  have hrow : (∑ k, (a k) • (1 : Matrix (Fin 4) (Fin 4) ℝ) k) = a := by
    ext j
    simp [Matrix.one_apply]
  have hdet : M.det = a i := by
    have he := Matrix.det_updateRow_sum (1 : Matrix (Fin 4) (Fin 4) ℝ) i a
    rw [hrow,Matrix.det_one,smul_eq_mul,mul_one] at he
    exact he
  have hne : M.det ≠ 0 := by
    intro hz
    rw [hdet] at hz
    rw [hz,abs_zero] at ha
    norm_num at ha
  have hlin : MeasurePreserving (Matrix.toLin' M) := by
    refine ⟨(LinearMap.continuous_on_pi _).measurable,?_⟩
    simpa only [hdet,abs_inv,ha,inv_one,ENNReal.ofReal_one,one_smul] using
      Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) hne
  let v : Fin 4 → ℝ := fun j => if j = i then c else 0
  let f : (Fin 4 → ℝ) → (Fin 4 → ℝ) := (fun x => v+x) ∘ Matrix.toLin' M
  have hf : MeasurePreserving f := (measurePreserving_add_left volume v).comp hlin
  have hmap (x : Fin 4 → ℝ) (j : Fin 4) :
      f x j = if j = i then c+∑ k, a k*x k else x j := by
    by_cases hj : j = i
    · subst j
      simp [f,v,M,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Matrix.updateRow_self]
    · simp [f,v,M,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,hj,Matrix.one_apply]
  let B := Set.Icc (fun j : Fin 4 => if j = i then l else 0)
    (fun j => if j = i then l+w else 1)
  have hsub : S ⊆ f ⁻¹' B := by
    intro x hx
    have hg := hS x hx
    constructor <;> intro j <;> rw [hmap] <;> by_cases hj : j = i
    · simp only [hj,if_true]
      exact hg.2.1
    · simp only [hj,if_false]
      exact (hg.1 j).1
    · simp only [hj,if_true]
      exact hg.2.2
    · simp only [hj,if_false]
      exact (hg.1 j).2
  have hB : volume B = ENNReal.ofReal w := by
    rw [Real.volume_Icc_pi]
    fin_cases i <;> simp [Fin.prod_univ_four]
  calc
    volume S ≤ volume (f ⁻¹' B) := measure_mono hsub
    _ = volume B := hf.measure_preimage measurableSet_Icc.nullMeasurableSet
    _ = _ := hB

/-- A deliberately coarse density bound on the positive-share chamber.
Its constant is independent of the moving moment and phase. -/
theorem density_bounds {lam : ℝ} {x : Fin 4 → ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hx : ∀ i, (1/200 : ℝ) ≤ x i)
    (hx0 : x 0 ≤ 1) (hp : (1/10 : ℝ) ≤ 1-∑ i, x i) :
    0 ≤ density lam x ∧ density lam x ≤ 1000000000000 := by
  have hL0 : 0 < lam := by linarith
  have hxp (i : Fin 4) : 0 < x i := by linarith [hx i]
  have hprod : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hxp i)
  have hp0 : 0 < 1-∑ i, x i := by linarith
  have hc0 := boxCap_nonneg lam 1 0 (lo := x) (hi := x) (hxp 0).le
  have hc : boxCap lam 1 0 x x ≤ 3 := by
    unfold boxCap
    have h₁ := min_le_left (x 0) (max 0 (min (lam-1-0+x 2+x 1+x 0) (1-lam-x 2)))
    have h₂ := min_le_left (x 0) (max 0 (min (lam-1-0+x 3+x 1+x 0) (1-lam-x 3)))
    have h₃ := min_le_left (x 0) (max 0 (min (lam-x 3-x 2) (x 3+x 2+x 1+x 0-lam)))
    linarith
  have hden : (17/25 : ℝ)*(1/10)*(1/200)^4 ≤ lam*(1-∑ i, x i)*(∏ i, x i) := by
    have he := mul_le_mul (mul_le_mul hL hp (by norm_num) hL0.le)
      (Finset.prod_le_prod (s := Finset.univ)
        (fun _ _ => (by norm_num : (0 : ℝ) ≤ 1/200)) (fun i _ => hx i))
      (by positivity) (by positivity)
    norm_num [Fin.prod_univ_four] at he ⊢
    exact he
  constructor
  · exact div_nonneg hc0 (by positivity)
  · apply (div_le_iff₀ (show 0 < lam*(1-∑ i, x i)*(∏ i, x i) by positivity)).mpr
    nlinarith

/-- The entire ordered three-large/two-small chamber at a padded cutoff
bin. Every large share is at most one half, leaving a fixed margin for
the literal allocation and physical masks. -/
def orderedRegion (lo hi : ℝ) : Set (Fin 4 → ℝ) := {x |
  (∀ i, (1/100 : ℝ) ≤ x i) ∧ x 0 ≤ x 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ x 3 ∧
  x 3 ≤ 1-∑ i, x i ∧ 1-∑ i, x i ≤ 1/2 ∧
  1-x 3-x 2 ≤ lo ∧ hi ≤ 1-x 1-x 0}

theorem orderedRegion_measurable (lo hi : ℝ) : MeasurableSet (orderedRegion lo hi) := by
  unfold orderedRegion
  simp only [Set.ofPred_and,Set.ofPred_forall]
  measurability

/-- Ordering supplies a lower owner share of one fifth and bounds the
whole region inside the unit cube. -/
theorem orderedRegion_geometry {lo hi : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ orderedRegion lo hi) :
    (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ (1/5 : ℝ) ≤ 1-∑ i, x i := by
  obtain ⟨hmin,h01,h12,h23,h3p,hpmax,_hsat,_htri⟩ := hx
  have hxp (i : Fin 4) : x i ≤ 1-∑ j, x j := by
    fin_cases i
    · exact ((h01.trans h12).trans h23).trans h3p
    · exact (h12.trans h23).trans h3p
    · exact h23.trans h3p
    · exact h3p
  refine ⟨fun i => ⟨by linarith [hmin i],by linarith [hxp i]⟩,?_⟩
  have he := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hxp i)
  simp only [Fin.sum_univ_four] at he ⊢
  linarith

private theorem integrableOn_orderedRegion {lam lo hi : ℝ} (hL : (17/25 : ℝ) ≤ lam) :
    IntegrableOn (density lam) (orderedRegion lo hi) := by
  have hsub : orderedRegion lo hi ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
    intro x hx
    exact ⟨fun i => (orderedRegion_geometry hx).1 i |>.1,
      fun i => (orderedRegion_geometry hx).1 i |>.2⟩
  have hfinite : volume (orderedRegion lo hi) ≠ ⊤ := by
    apply ne_of_lt ((measure_mono hsub).trans_lt ?_)
    simp [Real.volume_Icc_pi]
  apply Measure.integrableOn_of_bounded (M := (1000000000000 : ℝ)) hfinite
  · apply Measurable.aestronglyMeasurable
    unfold density boxCap
    fun_prop
  · filter_upwards [ae_restrict_mem (orderedRegion_measurable lo hi)] with x hx
    have hg := orderedRegion_geometry hx
    have he := density_bounds hL (fun i => by linarith [hx.1 i]) (hg.1 0).2 (by linarith [hg.2])
    exact (Real.norm_of_nonneg he.1).trans_le he.2

/-- Six affine gaps are precisely the ordering and saturation faces at
which a fixed-width prime cell can fail to remain in this chamber. -/
def face (lo hi : ℝ) (x : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![x 1-x 0,x 2-x 1,x 3-x 2,1-(∑ i, x i)-x 3,
    lo-1+x 3+x 2,1-x 1-x 0-hi]

private def faceCoefficients : Fin 6 → Fin 4 → ℝ :=
  ![![-1,1,0,0],![0,-1,1,0],![0,0,-1,1],![-1,-1,-1,-2],![0,0,1,1],![-1,-1,0,0]]

private def faceAxis : Fin 6 → Fin 4 := ![1,2,3,0,2,0]

private def faceConstant (lo hi : ℝ) : Fin 6 → ℝ := ![0,0,0,1,lo-1,1-hi]

private theorem face_affine (lo hi : ℝ) (x : Fin 4 → ℝ) (j : Fin 6) :
    face lo hi x j = faceConstant lo hi j+∑ i, faceCoefficients j i*x i := by
  fin_cases j <;> simp [face,faceConstant,faceCoefficients,Fin.sum_univ_four] <;> ring

private theorem face_axis_unit (j : Fin 6) : |faceCoefficients j (faceAxis j)| = 1 := by
  fin_cases j <;> norm_num [faceCoefficients,faceAxis,Matrix.cons_val_two,Matrix.cons_val_three]

private theorem face_nonneg {lo hi : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ orderedRegion lo hi) (j : Fin 6) : 0 ≤ face lo hi x j := by
  obtain ⟨_hmin,h01,h12,h23,h3p,_hmax,hsat,htri⟩ := hx
  fin_cases j <;> dsimp [face] <;> linarith

/-- All six strips together have volume at most 60 mesh widths. This
includes the owner-ordering face and both moving-cutoff saturation faces. -/
theorem volume_boundary_le {lo hi b : ℝ} :
    volume {x ∈ orderedRegion lo hi | ∃ j, face lo hi x j ≤ 10*b} ≤
      ENNReal.ofReal (60*b) := by
  let E := fun j : Fin 6 => {x ∈ orderedRegion lo hi | face lo hi x j ≤ 10*b}
  have he : {x ∈ orderedRegion lo hi | ∃ j, face lo hi x j ≤ 10*b} = ⋃ j, E j := by
    ext x
    constructor
    · rintro ⟨hx,j,hj⟩
      exact Set.mem_iUnion.mpr ⟨j,hx,hj⟩
    · intro hx
      obtain ⟨j,hD,hj⟩ := Set.mem_iUnion.mp hx
      exact ⟨hD,j,hj⟩
  have hv (j : Fin 6) : volume (E j) ≤ ENNReal.ofReal (10*b) := by
    apply volume_affine_slab_le (E j) (faceCoefficients j) (faceAxis j)
      (faceConstant lo hi j) 0 (10*b) (face_axis_unit j)
    intro x hx
    refine ⟨(orderedRegion_geometry hx.1).1,?_,?_⟩
    · rw [← face_affine]
      exact face_nonneg hx.1 j
    · simpa only [← face_affine,zero_add] using hx.2
  rw [he]
  calc
    volume (⋃ j, E j) ≤ ∑' j, volume (E j) := measure_iUnion_le _
    _ ≤ ∑' _j : Fin 6, ENNReal.ofReal (10*b) := ENNReal.tsum_le_tsum hv
    _ = ENNReal.ofReal (60*b) := by
      simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast]
      norm_num only [Nat.cast_ofNat]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      congr 1
      ring

/-- Every omitted face, together, costs at most 1/100000 in angular units
on the chosen fine mesh. No phase or prime sum is changed. -/
theorem norm_boundary_integral_le {lam lo hi b : ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hb : 0 ≤ b) (hsmall : b ≤ 1/100000000000000000000)
    (E : Set (Fin 4 → ℝ)) (hE : MeasurableSet E)
    (hsub : E ⊆ {x ∈ orderedRegion lo hi | ∃ j, face lo hi x j ≤ 10*b}) :
    ‖∫ x in E, density lam x‖ ≤ (1/100000 : ℝ) := by
  have hv := (measure_mono hsub).trans (volume_boundary_le (lo := lo) (hi := hi) (b := b))
  have hf : volume E < ⊤ := hv.trans_lt ENNReal.ofReal_lt_top
  have he := norm_setIntegral_le_of_norm_le_const_ae (f := density lam) hf
    (show ∀ᵐ x ∂volume.restrict E, ‖density lam x‖ ≤ (1000000000000 : ℝ) by
      filter_upwards [ae_restrict_mem hE] with x hx
      have hx' := (hsub hx).1
      have hg := orderedRegion_geometry hx'
      have hd := density_bounds hL (fun i => by linarith [hx'.1 i])
        (hg.1 0).2 (by linarith [hg.2])
      exact (Real.norm_of_nonneg hd.1).trans_le hd.2)
  have hr : volume.real E ≤ 60*b :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hv).trans_eq (ENNReal.toReal_ofReal (by positivity))
  nlinarith

/-- Select only grid cells that satisfy the original five-prime geometry
throughout the entire total-log window. The cutoff endpoints remain padded. -/
def interiorFamily (M : ℕ) (lo hi e b : ℝ) : Finset (Fin 4 → Fin M) :=
  Finset.univ.filter (fun v =>
    let g := gridLo 0 b v
    (∀ i, (1/200 : ℝ) ≤ g i) ∧
    (∀ i k, i < k → g i+b ≤ g k) ∧
    (1/10 : ℝ) ≤ 1-∑ i, (g i+b) ∧ g 3+b ≤ 1-∑ i, (g i+b) ∧
    1-(∑ i, g i)+e ≤ 9/16 ∧ 1-g 3-g 2+e ≤ lo ∧ hi ≤ 1-(g 1+b)-(g 0+b))

/-- Every point farther than ten cell widths from the six exact faces is
covered by a cell satisfying all literal arithmetic transfer conditions. -/
theorem covered_of_away_faces {M : ℕ} {lo hi e b : ℝ} {x : Fin 4 → ℝ}
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000)
    (he : e ≤ b) (hcover : (1 : ℝ) ≤ M*b)
    (hx : x ∈ orderedRegion lo hi) (hfaces : ∀ j, 10*b < face lo hi x j) :
    x ∈ ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b := by
  have hg := orderedRegion_geometry hx
  have hindex (i : Fin 4) : ∃ k : Fin M,
      0+(k : ℕ)*b < x i ∧ x i ≤ 0+((k : ℕ)+1)*b :=
    ZetaRieszFourBoundaryCover.exists_grid_index M
      (by linarith [hx.1 i]) (by simpa only [zero_add] using (hg.1 i).2.trans hcover)
  choose v hv using hindex
  let g := gridLo 0 b v
  have hcell (i : Fin 4) : g i < x i ∧ x i ≤ g i+b := by
    simpa only [g,gridLo,add_mul,one_mul,add_assoc] using hv i
  have h0 := hcell 0
  have h1 := hcell 1
  have h2 := hcell 2
  have h3 := hcell 3
  have hf0 := hfaces 0
  have hf1 := hfaces 1
  have hf2 := hfaces 2
  have hf3 := hfaces 3
  have hf4 := hfaces 4
  have hf5 := hfaces 5
  change 10*b < x 1-x 0 at hf0
  change 10*b < x 2-x 1 at hf1
  change 10*b < x 3-x 2 at hf2
  change 10*b < 1-(∑ i, x i)-x 3 at hf3
  change 10*b < lo-1+x 3+x 2 at hf4
  change 10*b < 1-x 1-x 0-hi at hf5
  have hp := hg.2
  have hmax := hx.2.2.2.2.2.1
  simp only [Fin.sum_univ_four] at hf3 hp hmax
  have hmember : v ∈ interiorFamily M lo hi e b := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (∀ i, (1/200 : ℝ) ≤ g i) ∧
      (∀ i k, i < k → g i+b ≤ g k) ∧
      (1/10 : ℝ) ≤ 1-∑ i, (g i+b) ∧ g 3+b ≤ 1-∑ i, (g i+b) ∧
      1-(∑ i, g i)+e ≤ 9/16 ∧ 1-g 3-g 2+e ≤ lo ∧ hi ≤ 1-(g 1+b)-(g 0+b)
    refine ⟨fun i => by linarith [hx.1 i,hcell i],?_,?_,?_,?_,?_,?_⟩
    · intro i k hik
      fin_cases i <;> fin_cases k <;> norm_num at hik <;> linarith!
    · simp only [Fin.sum_univ_four]
      linarith
    · simp only [Fin.sum_univ_four]
      linarith
    · simp only [Fin.sum_univ_four]
      linarith
    · linarith
    · linarith
  refine Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hmember,?_⟩⟩
  apply Set.mem_pi.mpr
  intro i _
  exact hcell i

/-- No interior favorable mass is silently omitted. The full complement
of the literal grid is contained in the six explicitly bounded strips. -/
theorem uncovered_subset_boundary {M : ℕ} {lo hi e b : ℝ}
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000)
    (he : e ≤ b) (hcover : (1 : ℝ) ≤ M*b) :
    orderedRegion lo hi \ (⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b) ⊆
      {x ∈ orderedRegion lo hi | ∃ j, face lo hi x j ≤ 10*b} := by
  intro x hx
  refine ⟨hx.1,?_⟩
  by_contra hn
  push Not at hn
  exact hx.2 (covered_of_away_faces hb hsmall he hcover hx.1 hn)

/-- The complete ordered favorable integral fits inside the literal
disjoint cell family after one explicit 1/100000 boundary budget. -/
theorem ordered_integral_le_cells {M : ℕ} {lam lo hi e b : ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hb : 0 < b)
    (hsmall : b ≤ 1/100000000000000000000) (he : e ≤ b) (hcover : (1 : ℝ) ≤ M*b) :
    (∫ x in orderedRegion lo hi, density lam x)-1/100000 ≤
      ∫ x in ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b, density lam x := by
  let I := interiorFamily M lo hi e b
  let Ω := ⋃ v ∈ I, cell (gridLo 0 b v) b
  have hcell (v : Fin 4 → Fin M) : MeasurableSet (cell (gridLo 0 b v) b) := by
    apply (measurableSet_pi (Set.to_countable _)).mpr
    exact Or.inl (fun _ _ => measurableSet_Ioc)
  have hΩ : MeasurableSet Ω := by
    apply MeasurableSet.iUnion
    intro v
    apply MeasurableSet.iUnion
    intro _hv
    exact hcell v
  have hiΩ : IntegrableOn (density lam) Ω := by
    apply integrableOn_finset_iUnion.mpr
    intro v hv
    have hg := (Finset.mem_filter.mp hv).2
    dsimp only at hg
    exact integrableOn_density (lo := gridLo 0 b v) (b := b) (by linarith)
      (fun i => by linarith [hg.1 i]) (by linarith [hg.2.2.1])
  have hpos : ∀ x ∈ Ω, 0 ≤ density lam x := by
    intro x hx
    obtain ⟨v,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hv,hx⟩ := Set.mem_iUnion.mp hx
    have hg := (Finset.mem_filter.mp hv).2
    dsimp only at hg
    have hx' (i : Fin 4) : gridLo 0 b v i < x i ∧ x i ≤ gridLo 0 b v i+b :=
      (Set.mem_pi.mp hx) i (Set.mem_univ i)
    have hx0 (i : Fin 4) : 0 < x i := by linarith [hg.1 i,hx' i]
    have hp : 0 < 1-∑ i, x i := by
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hx' i).2)
      linarith [hg.2.2.1]
    have hp' : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx0 i)
    have hL0 : 0 < lam := by linarith
    exact div_nonneg (boxCap_nonneg _ _ _ (hx0 0).le) (by positivity)
  have hiD := integrableOn_orderedRegion (lo := lo) (hi := hi) hL
  have hsplit := integral_inter_add_sdiff hΩ hiD
  have hbound := norm_boundary_integral_le hL hb.le hsmall
    (orderedRegion lo hi \ Ω) ((orderedRegion_measurable lo hi).diff hΩ)
    (uncovered_subset_boundary hb hsmall he hcover)
  have hrest : (∫ x in orderedRegion lo hi \ Ω, density lam x) ≤ 1/100000 :=
    (le_abs_self _).trans hbound
  have hinc : (∫ x in orderedRegion lo hi ∩ Ω, density lam x) ≤ ∫ x in Ω, density lam x := by
    apply setIntegral_mono_set hiΩ ?_ (Filter.Eventually.of_forall Set.inter_subset_right)
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hpos x hx
  change (∫ x in orderedRegion lo hi, density lam x)-1/100000 ≤ ∫ x in Ω, density lam x
  linarith

/-- The entire ordered favorable region supplies an independent literal
core credit, including every ordering/saturation boundary loss. The total
angular error is 1/50000 and the full remaining carrier stays signed. -/
theorem eventually_ordered_region_core_floor {u h b lo hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let I := interiorFamily M lo hi (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N → lo ≤ L/t → L/t ≤ hi →
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (((996/1000 : ℝ)*(∫ x in orderedRegion lo hi, density (L/t) x)-1/50000)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hwidth : ∀ᶠ N : ℕ in atTop, h ≤ b*N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hb).eventually_ge_atTop h
  filter_upwards [eventually_family_core_floor (a := 0) (M := M) hu hU hh hhu hb
      (by linarith : b ≤ 1/1000000000000000000),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hwidth,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hratio hwidth hj t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let I := interiorFamily M lo hi (h/t) b
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hj
  have ht : 0 < t := by nlinarith
  have hhb : h/t ≤ b := (div_le_iff₀ ht).mpr (by nlinarith)
  have hlow := (hratio (t+h) (by linarith) hthi).1
  have hL : (17/25 : ℝ) ≤ L/t := by
    have he := (le_div_iff₀ (show 0 < t+h by linarith)).mp hlow
    apply (le_div_iff₀ ht).mpr
    dsimp [L]
    nlinarith
  have hf := hJ I t y htlo hthi (by
    intro v hv
    have hg := (Finset.mem_filter.mp hv).2
    dsimp only at hg
    exact ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,
      hg.2.2.2.2.2.1.trans hlo,hhi.trans hg.2.2.2.2.2.2⟩)
  have hang := ordered_integral_le_cells (lo := lo) (hi := hi) hL hb hsmall hhb hcover
  have hnum : (996/1000 : ℝ)*(∫ x in orderedRegion lo hi, density (L/t) x)-1/50000 ≤
      (996/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo 0 b v) b, density (L/t) x)-1/100000 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hnum
    (show 0 ≤ (Real.exp (-(t+h)/2)*t^N/N.factorial)*
      max 0 (-Real.cos (y*t)-|y| * h)*h by positivity)
  linarith

end
end RiemannGaussian.ZetaRieszFiveAngularBoundary
