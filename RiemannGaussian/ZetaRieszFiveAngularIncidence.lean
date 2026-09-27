/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveAngularBoundary

/-!
# The signed supply budget under the six large-prime incidences

The one-half incidence factor is retained before angular integration.
The six volume-preserving relabellings of the three large shares compare
the certificate's pair density with the literal ordered three-cap density.
These coordinates are used only to prove that numerical supply inequality.
-/

namespace RiemannGaussian.ZetaRieszFiveAngularIncidence
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFiveAngularBoundary

/-- The remaining largest-share coordinate before ordering. -/
def owner (x : Fin 4 → ℝ) : ℝ := 1-x 0-x 1-x 2-x 3

/-- The symmetric product of all five shares. -/
def denominator (x : Fin 4 → ℝ) : ℝ := x 0*x 1*x 2*x 3*owner x

/-- Exchange the two displayed large shares. -/
def swapPair : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) where
  toFun x := ![x 0,x 1,x 3,x 2]
  invFun x := ![x 0,x 1,x 3,x 2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  measurable_toFun := by
    change Measurable (fun x : Fin 4 → ℝ => ![x 0,x 1,x 3,x 2])
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin 4 → ℝ => ![x 0,x 1,x 3,x 2])
    fun_prop

private theorem swapPair_preserving : MeasurePreserving swapPair := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
    (Equiv.swap (2 : Fin 4) 3)
  have he : (swapPair : (Fin 4 → ℝ) → (Fin 4 → ℝ)) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) (Equiv.swap (2 : Fin 4) 3) := by
    funext x i
    have he := MeasurableEquiv.piCongrLeft_apply_apply
      (Equiv.swap (2 : Fin 4) 3) (β := fun _ => ℝ) x ((Equiv.swap (2 : Fin 4) 3) i)
    simp only [Equiv.swap_apply_self] at he
    rw [he]
    fin_cases i <;> norm_num [swapPair,Equiv.swap_apply_def,Fin.ext_iff]
  rw [he]
  exact h

/-- Exchange the first displayed large share and its complementary owner.
The small shares and total logarithm are unchanged. -/
def swapOwner : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) where
  toFun x := ![x 0,x 1,owner x,x 3]
  invFun x := ![x 0,x 1,owner x,x 3]
  left_inv x := by ext i; fin_cases i <;> simp [owner]; ring
  right_inv x := by ext i; fin_cases i <;> simp [owner]; ring
  measurable_toFun := by
    change Measurable (fun x : Fin 4 → ℝ => ![x 0,x 1,owner x,x 3])
    unfold owner
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin 4 → ℝ => ![x 0,x 1,owner x,x 3])
    unfold owner
    fun_prop

private theorem swapOwner_preserving : MeasurePreserving swapOwner := by
  let a : Fin 4 → ℝ := fun _ => -1
  let M : Matrix (Fin 4) (Fin 4) ℝ := (1 : Matrix (Fin 4) (Fin 4) ℝ).updateRow 2 a
  have hrow : (∑ k, (a k) • (1 : Matrix (Fin 4) (Fin 4) ℝ) k) = a := by
    ext j
    simp [Matrix.one_apply]
  have hdet : M.det = -1 := by
    have he := Matrix.det_updateRow_sum (1 : Matrix (Fin 4) (Fin 4) ℝ) 2 a
    rw [hrow,Matrix.det_one,smul_eq_mul,mul_one] at he
    exact he
  have hlin : MeasurePreserving (Matrix.toLin' M) := by
    refine ⟨(LinearMap.continuous_on_pi _).measurable,?_⟩
    simpa only [hdet,inv_neg,inv_one,abs_neg,abs_one,ENNReal.ofReal_one,one_smul] using
      Real.map_matrix_volume_pi_eq_smul_volume_pi (M := M) (by rw [hdet]; norm_num)
  have he := (measurePreserving_add_left (volume : Measure (Fin 4 → ℝ)) ![0,0,1,0]).comp hlin
  have hmap (x : Fin 4 → ℝ) (i : Fin 4) :
      Matrix.toLin' M x i = if i = 2 then -∑ j, x j else x i := by
    by_cases hi : i = 2
    · subst i
      simp [M,a,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Matrix.updateRow_self]
    · simp [M,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,hi,Matrix.one_apply]
  have hf : ((fun x : Fin 4 → ℝ => ![0,0,1,0]+x) ∘ Matrix.toLin' M) = swapOwner := by
    funext x
    change ![0,0,1,0]+Matrix.toLin' M x = ![x 0,x 1,owner x,x 3]
    ext i
    change (![0,0,1,0] : Fin 4 → ℝ) i+Matrix.toLin' M x i =
      (![x 0,x 1,owner x,x 3] : Fin 4 → ℝ) i
    rw [hmap]
    fin_cases i <;> norm_num [owner,Fin.sum_univ_four,Fin.ext_iff] <;> first | rfl | ring
  rw [hf] at he
  exact he

/-- All six labelled incidences of the three large shares, including
coincident share values. Indices, rather than real values, are distinct. -/
def relabel (i : Fin 6) : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) :=
  ![MeasurableEquiv.refl _,swapPair,swapOwner,swapOwner.trans swapPair,
    swapPair.trans swapOwner,(swapPair.trans swapOwner).trans swapPair] i

/-- Each incidence has unit absolute Jacobian. -/
theorem relabel_preserving (i : Fin 6) : MeasurePreserving (relabel i) := by
  fin_cases i
  · exact MeasurePreserving.id _
  · exact swapPair_preserving
  · exact swapOwner_preserving
  · exact swapOwner_preserving.trans swapPair_preserving
  · exact swapPair_preserving.trans swapOwner_preserving
  · exact (swapPair_preserving.trans swapOwner_preserving).trans swapPair_preserving

private theorem relabel_symm_small (i : Fin 6) (x : Fin 4 → ℝ) :
    (relabel i).symm x 0 = x 0 ∧ (relabel i).symm x 1 = x 1 := by
  fin_cases i <;> constructor <;> rfl

private theorem denominator_relabel_symm (i : Fin 6) (x : Fin 4 → ℝ) :
    denominator ((relabel i).symm x) = denominator x := by
  fin_cases i
  · rfl
  · change denominator ![x 0,x 1,x 3,x 2] = denominator x
    dsimp [denominator,owner]; ring
  · change denominator ![x 0,x 1,owner x,x 3] = denominator x
    dsimp [denominator,owner]; ring
  · change denominator ![x 0,x 1,owner ![x 0,x 1,x 3,x 2],x 2] = denominator x
    dsimp [denominator,owner]; ring
  · change denominator ![x 0,x 1,x 3,owner x] = denominator x
    dsimp [denominator,owner]; ring
  · change denominator ![x 0,x 1,x 2,owner ![x 0,x 1,x 3,x 2]] = denominator x
    dsimp [denominator,owner]; ring

private theorem owner_relabel_symm (x : Fin 4 → ℝ) :
    (fun i : Fin 6 => owner ((relabel i).symm x)) =
      ![owner x,owner x,x 2,x 3,x 2,x 3] := by
  ext i
  fin_cases i
  · rfl
  · change owner ![x 0,x 1,x 3,x 2] = owner x
    dsimp [owner]; ring
  · change owner ![x 0,x 1,owner x,x 3] = x 2
    dsimp [owner]; ring
  · change owner ![x 0,x 1,owner ![x 0,x 1,x 3,x 2],x 2] = x 3
    dsimp [owner]; ring
  · change owner ![x 0,x 1,x 3,owner x] = x 2
    dsimp [owner]; ring
  · change owner ![x 0,x 1,x 2,owner ![x 0,x 1,x 3,x 2]] = x 3
    dsimp [owner]; ring

/-- One pair cap written by its complementary large share. The padded
endpoints are independent of the actual moving cutoff. -/
def cap (lo hi : ℝ) (x : Fin 4 → ℝ) (z : ℝ) : ℝ :=
  min (x 0) (max 0 (min (lo-(1-x 0-x 1-z)) (1-hi-z)))

/-- The pair density which is integrated in the optional certificate. -/
def pairDensity (lo hi : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  cap lo hi x (owner x)/(hi*denominator x)

private theorem pairDensity_relabel_symm (lo hi : ℝ) (i : Fin 6) (x : Fin 4 → ℝ) :
    pairDensity lo hi ((relabel i).symm x) =
      cap lo hi x (owner ((relabel i).symm x))/(hi*denominator x) := by
  simp only [pairDensity,denominator_relabel_symm,cap,
    (relabel_symm_small i x).1,(relabel_symm_small i x).2]

/-- The six angular incidences count each of the three caps exactly twice,
also on equality faces. No boundary term is silently removed. -/
theorem sum_pairDensity (lo hi : ℝ) (x : Fin 4 → ℝ) :
    (∑ i : Fin 6, pairDensity lo hi ((relabel i).symm x)) =
      2*(cap lo hi x (x 2)+cap lo hi x (x 3)+cap lo hi x (owner x)) /
        (hi*denominator x) := by
  simp_rw [pairDensity_relabel_symm]
  rw [← Finset.sum_div]
  congr 1
  have he (i : Fin 6) : owner ((relabel i).symm x) =
      (![owner x,owner x,x 2,x 3,x 2,x 3] : Fin 6 → ℝ) i :=
    congrFun (owner_relabel_symm x) i
  simp_rw [he]
  simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]
  change cap lo hi x (owner x)+(cap lo hi x (owner x)+(cap lo hi x (x 2)+
    (cap lo hi x (x 3)+(cap lo hi x (x 2)+(cap lo hi x (x 3)+0))))) = _
  ring

/-- Padded pair caps are lower bounds for the exact moving three-cap
coefficient. The full one-half incidence sum is paid pointwise. -/
theorem half_sum_pairDensity_le {lam lo hi : ℝ} {x : Fin 4 → ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hlo : lo ≤ lam) (hhi : lam ≤ hi)
    (hx : x ∈ orderedRegion lo hi) :
    (1/2 : ℝ)*(∑ i : Fin 6, pairDensity lo hi ((relabel i).symm x)) ≤
      ZetaRieszFiveInteriorBudget.density lam x := by
  have hxp (i : Fin 4) : 0 < x i := by linarith [hx.1 i]
  have hp : 0 < owner x := by
    have hg := (orderedRegion_geometry hx).2
    simp only [Fin.sum_univ_four] at hg
    dsimp [owner]
    linarith
  have hden : 0 < denominator x :=
    mul_pos (mul_pos (mul_pos (mul_pos (hxp 0) (hxp 1)) (hxp 2)) (hxp 3)) hp
  have hL0 : 0 < lam := by linarith
  have hc (z : ℝ) : cap lo hi x z ≤ cap lam lam x z := by
    apply min_le_min le_rfl
    apply max_le_max le_rfl
    apply min_le_min <;> linarith
  have hcap : cap lam lam x (x 2)+cap lam lam x (x 3)+cap lam lam x (owner x) =
      ZetaRieszFivePrimeCells.boxCap lam 1 0 x x := by
    dsimp [cap,owner,ZetaRieszFivePrimeCells.boxCap]
    congr 1
    · congr 1
      · congr 2
        congr 1
        ring
      · congr 2
        congr 1
        ring
    · congr 2
      congr 1 <;> ring
  have hnonneg : 0 ≤ cap lo hi x (x 2)+cap lo hi x (x 3)+cap lo hi x (owner x) := by
    have hz (z : ℝ) : 0 ≤ cap lo hi x z := le_min (hxp 0).le (le_max_left _ _)
    exact add_nonneg (add_nonneg (hz _) (hz _)) (hz _)
  have he := (div_le_div_of_nonneg_left hnonneg
    (mul_pos hL0 hden) (mul_le_mul_of_nonneg_right hhi hden.le)).trans
      (div_le_div_of_nonneg_right (add_le_add (add_le_add (hc _) (hc _)) (hc _))
        (mul_nonneg hL0.le hden.le))
  rw [hcap] at he
  rw [sum_pairDensity]
  calc
    _ = (cap lo hi x (x 2)+cap lo hi x (x 3)+cap lo hi x (owner x))/(hi*denominator x) := by ring
    _ ≤ ZetaRieszFivePrimeCells.boxCap lam 1 0 x x/(lam*denominator x) := he
    _ = _ := by
      unfold ZetaRieszFiveInteriorBudget.density denominator owner
      simp only [Fin.sum_univ_four,Fin.prod_univ_four]
      congr 1
      ring


/-- The same two-small/three-large chamber before ordering its three
large shares. Both padded saturation conditions are imposed on every
incidence, so none is gained by choosing a different owner. -/
def unorderedRegion (lo hi : ℝ) : Set (Fin 4 → ℝ) := {x |
  (1/100 : ℝ) ≤ x 0 ∧ x 0 ≤ x 1 ∧
  x 1 ≤ x 2 ∧ x 1 ≤ x 3 ∧ x 1 ≤ owner x ∧
  x 2 ≤ 1/2 ∧ x 3 ≤ 1/2 ∧ owner x ≤ 1/2 ∧
  1-x 2-x 3 ≤ lo ∧ 1-x 2-owner x ≤ lo ∧ 1-x 3-owner x ≤ lo ∧
  hi ≤ 1-x 1-x 0}

/-- Sorting the three large shares uses exactly one of the six labelled
incidences. Equality cases are covered, without deleting a null set. -/
theorem unorderedRegion_covered {lo hi : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ unorderedRegion lo hi) :
    ∃ i : Fin 6, relabel i x ∈ orderedRegion lo hi := by
  obtain ⟨hr,hrb,hba,hbq,hbp,ha,hq,hp,hpq,hpa,hqa,htri⟩ := hx
  have make (a q : ℝ) (hba : x 1 ≤ a) (haq : a ≤ q)
      (hqp : q ≤ 1-x 0-x 1-a-q) (hp : 1-x 0-x 1-a-q ≤ 1/2)
      (hs : 1-q-a ≤ lo) :
      ![x 0,x 1,a,q] ∈ orderedRegion lo hi := by
    refine ⟨?_,hrb,hba,haq,?_,?_,hs,htri⟩
    · intro i
      fin_cases i <;> dsimp <;> linarith
    · simp only [Fin.sum_univ_four]
      change q ≤ 1-(x 0+x 1+a+q)
      linarith
    · simp only [Fin.sum_univ_four]
      change 1-(x 0+x 1+a+q) ≤ 1/2
      linarith
  have hpdef : owner x = 1-x 0-x 1-x 2-x 3 := rfl
  rcases le_total (x 2) (x 3) with haq | hqa'
  · rcases le_total (x 3) (owner x) with hqp | hpq
    · refine ⟨0,?_⟩
      change x ∈ orderedRegion lo hi
      convert make (x 2) (x 3) hba haq (by linarith) (by linarith) (by linarith) using 1
      ext i; fin_cases i <;> rfl
    · rcases le_total (x 2) (owner x) with hap | hpa'
      · refine ⟨5,?_⟩
        change ![x 0,x 1,x 2,owner ![x 0,x 1,x 3,x 2]] ∈ orderedRegion lo hi
        have he : owner ![x 0,x 1,x 3,x 2] = owner x := by dsimp [owner]; ring
        rw [he]
        exact make (x 2) (owner x) hba hap (by linarith) (by linarith) (by linarith)
      · refine ⟨4,?_⟩
        change ![x 0,x 1,owner ![x 0,x 1,x 3,x 2],x 2] ∈ orderedRegion lo hi
        have he : owner ![x 0,x 1,x 3,x 2] = owner x := by dsimp [owner]; ring
        rw [he]
        exact make (owner x) (x 2) hbp hpa' (by linarith) (by linarith) (by linarith)
  · rcases le_total (x 2) (owner x) with hap | hpa'
    · refine ⟨1,?_⟩
      change ![x 0,x 1,x 3,x 2] ∈ orderedRegion lo hi
      exact make (x 3) (x 2) hbq hqa' (by linarith) (by linarith) (by linarith)
    · rcases le_total (x 3) (owner x) with hqp | hpq
      · refine ⟨3,?_⟩
        change ![x 0,x 1,x 3,owner x] ∈ orderedRegion lo hi
        exact make (x 3) (owner x) hbq hqp (by linarith) (by linarith) (by linarith)
      · refine ⟨2,?_⟩
        change ![x 0,x 1,owner x,x 3] ∈ orderedRegion lo hi
        exact make (owner x) (x 3) hbp hpq (by linarith) (by linarith) (by linarith)

private theorem denominator_pos {lo hi : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ orderedRegion lo hi) : 0 < denominator x := by
  have hxp (i : Fin 4) : 0 < x i := by linarith [hx.1 i]
  have hp : 0 < owner x := by
    have he := (orderedRegion_geometry hx).2
    simp only [Fin.sum_univ_four] at he
    dsimp [owner]
    linarith
  exact mul_pos (mul_pos (mul_pos (mul_pos (hxp 0) (hxp 1)) (hxp 2)) (hxp 3)) hp

private theorem pairDensity_relabel_nonneg {lo hi : ℝ} {x : Fin 4 → ℝ}
    (hhi : 0 ≤ hi) (hx : x ∈ orderedRegion lo hi) (i : Fin 6) :
    0 ≤ pairDensity lo hi ((relabel i).symm x) := by
  rw [pairDensity_relabel_symm]
  exact div_nonneg (le_min (by linarith [hx.1 0]) (le_max_left _ _))
    (mul_nonneg hhi (denominator_pos hx).le)

private theorem integrableOn_ordered {g : (Fin 4 → ℝ) → ℝ} {lo hi C : ℝ}
    (hg : Measurable g) (hbound : ∀ x ∈ orderedRegion lo hi, ‖g x‖ ≤ C) :
    IntegrableOn g (orderedRegion lo hi) := by
  have hsub : orderedRegion lo hi ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
    intro x hx
    exact ⟨fun i => (orderedRegion_geometry hx).1 i |>.1,
      fun i => (orderedRegion_geometry hx).1 i |>.2⟩
  have hfinite : volume (orderedRegion lo hi) ≠ ⊤ := by
    apply ne_of_lt ((measure_mono hsub).trans_lt ?_)
    simp [Real.volume_Icc_pi]
  apply Measure.integrableOn_of_bounded hfinite hg.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (orderedRegion_measurable lo hi)] with x hx
  exact hbound x hx

private theorem integrableOn_pairDensity_relabel {lam lo hi : ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hlo : lo ≤ lam) (hhi : lam ≤ hi) (i : Fin 6) :
    IntegrableOn (fun x => pairDensity lo hi ((relabel i).symm x))
      (orderedRegion lo hi) := by
  have hH : 0 ≤ hi := by linarith
  apply integrableOn_ordered (C := 2000000000000)
  · unfold pairDensity cap denominator owner
    fun_prop
  · intro x hx
    rw [Real.norm_of_nonneg (pairDensity_relabel_nonneg hH hx i)]
    have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 6)))
      (f := fun i => pairDensity lo hi ((relabel i).symm x))
      (fun j _ => pairDensity_relabel_nonneg hH hx j) (Finset.mem_univ i)
    have hc := half_sum_pairDensity_le hL hlo hhi hx
    have hg := orderedRegion_geometry hx
    have hb := ZetaRieszFiveAngularBoundary.density_bounds hL
      (fun j => show (1/200 : ℝ) ≤ x j by linarith [hx.1 j])
      (hg.1 0).2 (by linarith [hg.2])
    linarith [hb.2]

/-- The one-half pair integral on any measurable subset of the unordered
chamber fits inside the exact ordered three-cap supply. Six incidences
are integrated with their unit Jacobians before applying the pointwise
inequality. Ordering ties are covered, not discarded. -/
theorem half_integral_pairDensity_le {lam lo hi : ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hlo : lo ≤ lam) (hhi : lam ≤ hi)
    (E : Set (Fin 4 → ℝ)) (hE : MeasurableSet E)
    (hsub : E ⊆ unorderedRegion lo hi) :
    (1/2 : ℝ)*(∫ x in E, pairDensity lo hi x) ≤
      ∫ x in orderedRegion lo hi, ZetaRieszFiveInteriorBudget.density lam x := by
  let D (i : Fin 6) := relabel i ⁻¹' orderedRegion lo hi
  have hD (i : Fin 6) : MeasurableSet (D i) :=
    (orderedRegion_measurable lo hi).preimage (relabel i).measurable
  have hI (i : Fin 6) := integrableOn_pairDensity_relabel hL hlo hhi i
  have hID (i : Fin 6) : IntegrableOn (pairDensity lo hi) (D i) := by
    have he := ((relabel_preserving i).integrableOn_comp_preimage
      (relabel i).measurableEmbedding).mpr (hI i)
    simpa only [Function.comp_def,MeasurableEquiv.symm_apply_apply] using he
  have hcov : E ⊆ ⋃ i, D i := by
    intro x hx
    obtain ⟨i,hi⟩ := unorderedRegion_covered (hsub hx)
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  have hIE : IntegrableOn (pairDensity lo hi) E :=
    (integrableOn_finite_iUnion.mpr hID).mono_set hcov
  have hH : 0 ≤ hi := by linarith
  have hnonneg (i : Fin 6) (x : Fin 4 → ℝ) (hx : x ∈ D i) :
      0 ≤ pairDensity lo hi x := by
    simpa only [MeasurableEquiv.symm_apply_apply] using
      pairDensity_relabel_nonneg hH hx i
  have hpoint (x : Fin 4 → ℝ) : E.indicator (pairDensity lo hi) x ≤
      ∑ i : Fin 6, (D i).indicator (pairDensity lo hi) x := by
    have hn (i : Fin 6) : 0 ≤ (D i).indicator (pairDensity lo hi) x := by
      by_cases hx : x ∈ D i
      · simpa only [Set.indicator_of_mem hx] using hnonneg i x hx
      · simp only [Set.indicator_of_notMem hx,le_refl]
    by_cases hx : x ∈ E
    · obtain ⟨i,hDi⟩ := Set.mem_iUnion.mp (hcov hx)
      rw [Set.indicator_of_mem hx]
      calc
        _ = (D i).indicator (pairDensity lo hi) x := (Set.indicator_of_mem hDi _).symm
        _ ≤ _ := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    · simp only [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i _ => hn i)
  have hcomp : (∫ x in E, pairDensity lo hi x) ≤
      ∑ i : Fin 6, ∫ x in orderedRegion lo hi, pairDensity lo hi ((relabel i).symm x) := by
    have he := integral_mono (hIE.integrable_indicator hE)
      (integrable_finsetSum _ (fun i _ => (hID i).integrable_indicator (hD i))) hpoint
    rw [integral_indicator hE,integral_finsetSum _
      (fun i _ => (hID i).integrable_indicator (hD i))] at he
    have heq (i : Fin 6) : (∫ x in D i, pairDensity lo hi x) =
        ∫ x in orderedRegion lo hi, pairDensity lo hi ((relabel i).symm x) := by
      simpa only [MeasurableEquiv.symm_apply_apply] using
        (relabel_preserving i).setIntegral_preimage_emb (relabel i).measurableEmbedding
          (fun x => pairDensity lo hi ((relabel i).symm x)) (orderedRegion lo hi)
    simpa only [integral_indicator (hD _),heq] using he
  have hR : IntegrableOn (ZetaRieszFiveInteriorBudget.density lam) (orderedRegion lo hi) := by
    apply integrableOn_ordered (C := 1000000000000)
    · unfold ZetaRieszFiveInteriorBudget.density ZetaRieszFivePrimeCells.boxCap
      fun_prop
    · intro x hx
      have hg := orderedRegion_geometry hx
      have hb := ZetaRieszFiveAngularBoundary.density_bounds hL
        (fun j => show (1/200 : ℝ) ≤ x j by linarith [hx.1 j])
        (hg.1 0).2 (by linarith [hg.2])
      exact (Real.norm_of_nonneg hb.1).trans_le hb.2
  calc
    _ ≤ (1/2 : ℝ)*(∑ i : Fin 6, ∫ x in orderedRegion lo hi,
        pairDensity lo hi ((relabel i).symm x)) := mul_le_mul_of_nonneg_left hcomp (by norm_num)
    _ = ∫ x in orderedRegion lo hi, (1/2 : ℝ)*
        (∑ i : Fin 6, pairDensity lo hi ((relabel i).symm x)) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hI i)]
    _ ≤ _ := setIntegral_mono_on ((integrable_finsetSum _ (fun i _ => hI i)).const_mul _) hR
      (orderedRegion_measurable lo hi) (fun x hx => half_sum_pairDensity_le hL hlo hhi hx)


/-- The exact one-half incidence budget is now available in the literal
finite-prime floor. All original arithmetic weights, masks and phase,
as well as the complete signed complement, stay unchanged. Substituting
the optional two-dimensional certificate still requires its Fubini bridge. -/
theorem eventually_pair_integral_core_floor {u h b lo hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b)
    (hlo : (17/25 : ℝ) ≤ lo)
    (E : Set (Fin 4 → ℝ)) (hE : MeasurableSet E) (hsub : E ⊆ unorderedRegion lo hi) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let I := interiorFamily M lo hi (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N → lo ≤ L/t → L/t ≤ hi →
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (((996/1000 : ℝ)*((1/2 : ℝ)*(∫ x in E, pairDensity lo hi x))-1/50000)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_ordered_region_core_floor
    (lo := lo) (hi := hi) hu hU hh hhu hb hsmall hcover] with j hJ t y
  dsimp only
  intro htlo hthi hlt htl
  have hf := hJ t y htlo hthi hlt htl
  have hc := half_integral_pairDensity_le (hlo.trans hlt) hlt htl E hE hsub
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
end RiemannGaussian.ZetaRieszFiveAngularIncidence
