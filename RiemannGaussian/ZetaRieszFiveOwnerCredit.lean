/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointCapacityCeiling

/-!
# Extra signed credit inside the existing five-prime population

The literal interior family already permits owner shares above one half.
The previous integral certificate only spends the region below one half.
Disjoint rational cofactor boxes give an additional lower bound for that
same population, with no extra copy of the prime supply. The entire signed
complement, moving length, phase and allocation are unchanged.
-/

namespace RiemannGaussian.ZetaRieszFiveOwnerCredit
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFivePrimeCells ZetaRieszFiveInteriorBudget ZetaRieszFiveAngularBoundary

/-- A rational lower cap uses the two ends of the cutoff bin before any
norm or integration. Every one of the three signed hinge caps is retained. -/
def lowerCap (l u : ℝ) (a b : Fin 4 → ℝ) : ℝ :=
  min (a 0) (max 0 (min (l-1+a 2+a 1+a 0) (1-u-b 2))) +
  min (a 0) (max 0 (min (l-1+a 3+a 1+a 0) (1-u-b 3))) +
  min (a 0) (max 0 (min (l-b 3-b 2) (a 3+a 2+a 1+a 0-u)))

/-- Exact monotonicity pays the full cutoff bin and all cofactor edges. -/
theorem lowerCap_le {l u lam : ℝ} {a b x : Fin 4 → ℝ}
    (hl : l ≤ lam) (hu : lam ≤ u) (hx : ∀ i, a i ≤ x i ∧ x i ≤ b i) :
    lowerCap l u a b ≤ boxCap lam 1 0 x x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have hA := min_le_min h0.1 (max_le_max (le_refl (0 : ℝ))
    (min_le_min (by linarith : l-1+a 2+a 1+a 0 ≤ lam-1-0+x 2+x 1+x 0)
      (by linarith : 1-u-b 2 ≤ 1-lam-x 2)))
  have hB := min_le_min h0.1 (max_le_max (le_refl (0 : ℝ))
    (min_le_min (by linarith : l-1+a 3+a 1+a 0 ≤ lam-1-0+x 3+x 1+x 0)
      (by linarith : 1-u-b 3 ≤ 1-lam-x 3)))
  have hC := min_le_min h0.1 (max_le_max (le_refl (0 : ℝ))
    (min_le_min (by linarith : l-b 3-b 2 ≤ lam-x 3-x 2)
      (by linarith : a 3+a 2+a 1+a 0-u ≤ x 3+x 2+x 1+x 0-lam)))
  exact add_le_add (add_le_add hA hB) hC

/-- The explicit box density is a lower bound for the actual cap density. -/
theorem density_lower {l u lam : ℝ} {a b x : Fin 4 → ℝ}
    (hl : l ≤ lam) (hu : lam ≤ u) (hL : 0 < lam)
    (ha : ∀ i, 0 < a i) (hp : 0 < 1-∑ i, b i)
    (hx : ∀ i, a i ≤ x i ∧ x i ≤ b i) :
    lowerCap l u a b/(u*(1-∑ i, a i)*∏ i, b i) ≤ density lam x := by
  have hx0 (i : Fin 4) : 0 < x i := (ha i).trans_le (hx i).1
  have hxp : 0 < 1-∑ i, x i := hp.trans_le
    (sub_le_sub_left (Finset.sum_le_sum (fun i _ => (hx i).2)) _)
  have hxa : 1-∑ i, x i ≤ 1-∑ i, a i :=
    sub_le_sub_left (Finset.sum_le_sum (fun i _ => (hx i).1)) _
  have hcap : 0 ≤ lowerCap l u a b := by
    unfold lowerCap
    exact add_nonneg (add_nonneg (le_min (ha 0).le (le_max_left _ _))
      (le_min (ha 0).le (le_max_left _ _))) (le_min (ha 0).le (le_max_left _ _))
  have hden : lam*(1-∑ i, x i)*(∏ i, x i) ≤ u*(1-∑ i, a i)*(∏ i, b i) :=
    mul_le_mul (mul_le_mul hu hxa hxp.le (hL.le.trans hu))
      (Finset.prod_le_prod (fun i _ => (hx0 i).le) (fun i _ => (hx i).2))
      (Finset.prod_nonneg (fun i _ => (hx0 i).le))
      (mul_nonneg (hL.le.trans hu) (hxp.le.trans hxa))
  have hd0 : 0 < lam*(1-∑ i, x i)*(∏ i, x i) :=
    mul_pos (mul_pos hL hxp) (Finset.prod_pos (fun i _ => hx0 i))
  exact (div_le_div_of_nonneg_left hcap hd0 hden).trans
    (div_le_div_of_nonneg_right (lowerCap_le hl hu hx) hd0.le)

/-- A whole cofactor cube has this explicit rational-volume credit. -/
theorem cube_integral_lower {l u lam w : ℝ} {a : Fin 4 → ℝ}
    (hl : l ≤ lam) (hu : lam ≤ u) (hL : 0 < lam) (hw : 0 ≤ w)
    (ha : ∀ i, 0 < a i) (hp : 0 < 1-∑ i, (a i+w)) :
    w^4*(lowerCap l u a (fun i => a i+w)/
      (u*(1-∑ i, a i)*∏ i, (a i+w))) ≤ ∫ x in cell a w, density lam x := by
  have hf := integrableOn_density hL ha hp
  have hfinite : volume (cell a w) ≠ ⊤ := by
    rw [cell,Real.volume_pi_Ioc]
    exact ne_of_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))
  have hmeas : MeasurableSet (cell a w) :=
    (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))
  have he := setIntegral_mono_on (integrableOn_const hfinite) hf hmeas
    (fun x hx => density_lower hl hu hL ha hp
      (fun i => ⟨((Set.mem_pi.mp hx) i (Set.mem_univ i)).1.le,
        ((Set.mem_pi.mp hx) i (Set.mem_univ i)).2⟩))
  have hv : volume.real (cell a w) = w^4 := by
    change (volume (cell a w)).toReal = _
    rw [cell,Real.volume_pi_Ioc_toReal (fun _ => le_add_of_nonneg_right hw)]
    simp only [add_sub_cancel_left,Fin.prod_univ_four]
    ring
  simpa only [setIntegral_const,hv,smul_eq_mul] using he

/-- A fixed rational margin places a point in the EXISTING literal fine
grid. Owner shares may exceed one half but never reach its 9/16 boundary. -/
theorem covered_of_strict_geometry {M : ℕ} {lo hi e b : ℝ} {x : Fin 4 → ℝ}
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000)
    (he : e ≤ b) (hcover : (1 : ℝ) ≤ M*b)
    (hx : ∀ i, (1/100 : ℝ) ≤ x i ∧ x i ≤ 1)
    (ho : ∀ i k, i < k → x i+1/1000000 ≤ x k)
    (hmin : (1/10 : ℝ)+1/1000000 ≤ 1-∑ i, x i)
    (howner : x 3+1/1000000 ≤ 1-∑ i, x i)
    (hmax : 1-(∑ i, x i)+1/1000000 ≤ (9/16 : ℝ))
    (hsat : 1-x 3-x 2+1/1000000 ≤ lo)
    (htri : hi+1/1000000 ≤ 1-x 1-x 0) :
    x ∈ ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b := by
  have hindex (i : Fin 4) : ∃ k : Fin M,
      0+(k : ℕ)*b < x i ∧ x i ≤ 0+((k : ℕ)+1)*b :=
    ZetaRieszFourBoundaryCover.exists_grid_index M
      (by linarith [hx i]) (by simpa only [zero_add] using (hx i).2.trans hcover)
  choose v hv using hindex
  let g := gridLo 0 b v
  have hg (i : Fin 4) : g i < x i ∧ x i ≤ g i+b := by
    simpa only [g,gridLo,add_mul,one_mul,add_assoc] using hv i
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have hmember : v ∈ interiorFamily M lo hi e b := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (∀ i, (1/200 : ℝ) ≤ g i) ∧
      (∀ i k, i < k → g i+b ≤ g k) ∧
      (1/10 : ℝ) ≤ 1-∑ i, (g i+b) ∧ g 3+b ≤ 1-∑ i, (g i+b) ∧
      1-(∑ i, g i)+e ≤ 9/16 ∧ 1-g 3-g 2+e ≤ lo ∧ hi ≤ 1-(g 1+b)-(g 0+b)
    refine ⟨fun i => by linarith [hx i,hg i],?_,?_,?_,?_,?_,?_⟩
    · intro i k hik
      linarith [ho i k hik,hg i,hg k]
    · simp only [Fin.sum_univ_four] at hmin ⊢
      linarith
    · simp only [Fin.sum_univ_four] at howner ⊢
      linarith
    · simp only [Fin.sum_univ_four] at hmax ⊢
      linarith
    · linarith
    · linarith
  exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hmember,
    Set.mem_pi.mpr (fun i _ => hg i)⟩⟩

private theorem interior_integrable {M : ℕ} {lo hi e b lam : ℝ} (hL : 0 < lam) :
    IntegrableOn (density lam)
      (⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b) := by
  apply integrableOn_finset_iUnion.mpr
  intro v hv
  have hg := (Finset.mem_filter.mp hv).2
  dsimp only at hg
  exact integrableOn_density (lo := gridLo 0 b v) (b := b) hL
    (fun i => by linarith [hg.1 i]) (by linarith [hg.2.2.1])

private theorem interior_measurable (M : ℕ) (lo hi e b : ℝ) :
    MeasurableSet (⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b) := by
  apply MeasurableSet.iUnion
  intro v
  apply MeasurableSet.iUnion
  intro _hv
  exact (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

private theorem interior_nonneg {M : ℕ} {lo hi e b lam : ℝ} (hL : 0 < lam)
    {x : Fin 4 → ℝ}
    (hx : x ∈ ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b) :
    0 ≤ density lam x := by
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
  exact div_nonneg (boxCap_nonneg _ _ _ (hx0 0).le) (by positivity)

private theorem ordered_integrable {lam lo hi : ℝ} (hL : (17/25 : ℝ) ≤ lam) :
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
    have hd := density_bounds hL (fun i => by linarith [hx.1 i]) (hg.1 0).2 (by linarith [hg.2])
    exact (Real.norm_of_nonneg hd.1).trans_le hd.2

/-- Extra owner mass is added at the INTEGRAL level inside one literal
population. Disjointness is from the old credited region, not from a
second overlapping copy of the prime population. The old boundary budget
is paid once. -/
theorem ordered_plus_extra_le_cells {M : ℕ} {lam lo hi e b C : ℝ}
    (hL : (17/25 : ℝ) ≤ lam) (hb : 0 < b)
    (hsmall : b ≤ 1/100000000000000000000) (he : e ≤ b) (hcover : (1 : ℝ) ≤ M*b)
    (E : Set (Fin 4 → ℝ)) (hE : MeasurableSet E)
    (hsub : E ⊆ ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b)
    (hdis : Disjoint E (orderedRegion lo hi))
    (hcredit : C ≤ ∫ x in E, density lam x) :
    (∫ x in orderedRegion lo hi, density lam x)+C-1/100000 ≤
      ∫ x in ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b, density lam x := by
  let Ω := ⋃ v ∈ interiorFamily M lo hi e b, cell (gridLo 0 b v) b
  let D := orderedRegion lo hi
  have hΩ := interior_measurable M lo hi e b
  have hiΩ := interior_integrable (lo := lo) (hi := hi) (e := e) (b := b) (M := M)
    (by linarith : 0 < lam)
  have hiD := ordered_integrable (lo := lo) (hi := hi) hL
  have hsplit := integral_inter_add_sdiff hΩ hiD
  have hbound := norm_boundary_integral_le hL hb.le hsmall (D\Ω)
    ((orderedRegion_measurable lo hi).diff hΩ) (uncovered_subset_boundary hb hsmall he hcover)
  have hrest : (∫ x in D\Ω, density lam x) ≤ 1/100000 := (le_abs_self _).trans hbound
  have hdis' : Disjoint (D ∩ Ω) E :=
    (hdis.symm.mono_left Set.inter_subset_left)
  have hiE := hiΩ.mono_set hsub
  have hiI := hiΩ.mono_set (Set.inter_subset_right (s := D) (t := Ω))
  have hu := setIntegral_union hdis' hE hiI hiE
  have hinc : (∫ x in (D ∩ Ω) ∪ E, density lam x) ≤ ∫ x in Ω, density lam x := by
    apply setIntegral_mono_set hiΩ ?_ (Filter.Eventually.of_forall
      (Set.union_subset Set.inter_subset_right hsub))
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact interior_nonneg (by linarith : 0 < lam) hx
  change (∫ x in D, density lam x)+C-1/100000 ≤ ∫ x in Ω, density lam x
  rw [hu] at hinc
  linarith

end
end RiemannGaussian.ZetaRieszFiveOwnerCredit
