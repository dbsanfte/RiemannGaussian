/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourOrderingBudget
import RiemannGaussian.ZetaRieszFourCapacityCover

/-!
# Exact angular-integral bounds for the literal adverse four-prime population

The existing capped coefficient gives a uniform fine-cell estimate with
multiplicative cost 1003/1000 and additive cost 1/100000 per unit angular
volume. Disjoint cofactor cells share one volume budget. Actual prime-window
estimates then give a signed floor for the entire clipped adverse population,
including ordering faces, on the unchanged dyadic core and with its complete
signed complement. The covering domain must still be compared with the
certified two-dimensional angular domain; no whole joint floor is asserted.
-/

namespace RiemannGaussian.ZetaRieszFourInteriorBudget
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFourPrimeCells ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget

/-- The exact four-prime coefficient density in the three cofactor shares.
This is the integrand of the existing ordered cap integral, before its
least-share variable is integrated. -/
def density (lam : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  boxCap lam 1 0 x x / (lam*(1-∑ i, x i)*∏ i, x i)

private theorem cap_perturbation {lam h b : ℝ} {lo x : Fin 3 → ℝ}
    (hb : 0 ≤ b) (hh : h ≤ b)
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ lo i+b) :
    boxCap lam 1 h lo (fun i => lo i+b) ≤ boxCap lam 1 0 x x+5*b := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have hinner : min (lam-1+∑ i, (lo i+b))
      (min (1+h-lam-lo 2) (2-(∑ i, lo i)+2*h-2*lam)) ≤
      min (lam-1+∑ i, x i) (min (1-lam-x 2) (2-(∑ i, x i)-2*lam))+5*b := by
    simp only [Fin.sum_univ_three]
    simpa only [min_add_add_right] using
      min_le_min (show lam-1+(lo 0+b+(lo 1+b)+(lo 2+b)) ≤
        lam-1+(x 0+x 1+x 2)+5*b by linarith)
        (min_le_min (show 1+h-lam-lo 2 ≤ 1-lam-x 2+5*b by linarith)
          (show 2-(lo 0+lo 1+lo 2)+2*h-2*lam ≤
            2-(x 0+x 1+x 2)-2*lam+5*b by linarith))
  have hmax := max_le_max (show (0 : ℝ) ≤ 0+5*b by positivity) hinner
  simp only [max_add_add_right] at hmax
  have hcap := min_le_min (show lo 0+b ≤ x 0+5*b by linarith) hmax
  simpa only [boxCap, zero_mul, mul_zero, mul_one, add_zero, sub_zero, one_mul,
    min_add_add_right] using hcap

/-- A sufficiently fine cell costs at most 0.3 percent of its exact
pointwise density plus 1/100000 per unit volume. The positive coefficient
keeps all three caps; no absolute carrier envelope occurs. -/
theorem angular_pointwise_le {lam h b : ℝ} {lo x : Fin 3 → ℝ}
    (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (hL : (17/25 : ℝ) ≤ lam)
    (hlo : ∀ i, 0 < lo i) (hmesh : ∀ i, b ≤ lo i/1000000000)
    (ha : (1/25 : ℝ) ≤ lo 1) (hq : (13/100 : ℝ) ≤ lo 2)
    (hp : (9/25 : ℝ) ≤ 1-∑ i, (lo i+b))
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ lo i+b) :
    (501/500 : ℝ)*((1+h)/lam)*boxCap lam 1 h lo (fun i => lo i+b) /
        (1-∑ i, (lo i+b))*(∏ i, 1/lo i) ≤
      (1003/1000 : ℝ)*density lam x+1/100000 := by
  let p := 1-∑ i, (lo i+b)
  let q := 1-∑ i, x i
  let C := boxCap lam 1 0 x x
  have hL0 : 0 < lam := by linarith
  have hp0 : 0 < p := by dsimp [p]; linarith
  have hqlo : p ≤ q := by
    dsimp [p,q]
    exact sub_le_sub_left (Finset.sum_le_sum (fun i _ => (hx i).2)) _
  have hq0 : 0 < q := hp0.trans_le hqlo
  have hx0 (i : Fin 3) : 0 < x i := (hlo i).trans_le (hx i).1
  have hloProd : 0 < ∏ i, lo i := Finset.prod_pos (fun i _ => hlo i)
  have hxProd : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx0 i)
  have hlo0 : lo 0 ≤ 1 := by
    simp only [Fin.sum_univ_three] at hp
    linarith [hlo 1,hlo 2]
  have hbsmall : b ≤ (1/1000000000 : ℝ) := by linarith [hmesh 0]
  have hhsmall : 1+h ≤ (1000001/1000000 : ℝ) := by linarith
  have hxrel (i : Fin 3) : x i ≤ (1000001/1000000 : ℝ)*lo i := by
    linarith [hx i,hmesh i,hlo i]
  have hqrel : q ≤ (1000001/1000000 : ℝ)*p := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hx i).1)
    simp only [Fin.sum_univ_three] at hp hs
    dsimp [q,p]
    simp only [Fin.sum_univ_three]
    linarith
  have hC0 : 0 ≤ C := boxCap_nonneg _ _ _ (hx0 0).le
  have hd0 : 0 < lam*p*(∏ i, lo i) := by positivity
  have hd1 : 0 < lam*q*(∏ i, x i) := by positivity
  have hd : lam*q*(∏ i, x i) ≤
      (1000001/1000000 : ℝ)^4*(lam*p*(∏ i, lo i)) := by
    have hp' := mul_le_mul hqrel
      (Finset.prod_le_prod (fun i _ => (hx0 i).le) (fun i _ => hxrel i))
      hxProd.le (by positivity)
    have he := mul_le_mul_of_nonneg_left hp' hL0.le
    simp only [Fin.prod_univ_three] at he ⊢
    convert he using 1 <;> first | rfl | ring
  have hmain : C/(lam*p*(∏ i, lo i)) ≤
      (1000001/1000000 : ℝ)^4*density lam x := by
    change C/(lam*p*(∏ i, lo i)) ≤ (1000001/1000000 : ℝ)^4*(C/(lam*q*(∏ i, x i)))
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hd0 hd1).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hC0]
  have herr : (5*b)/(lam*p*(∏ i, lo i)) ≤ (1/127000 : ℝ) := by
    have hden : (17/25 : ℝ)*(9/25)*(1/25)*(13/100)*lo 0 ≤
        lam*p*(∏ i, lo i) := by
      rw [Fin.prod_univ_three]
      have hden1 := mul_le_mul hL hp (by norm_num) hL0.le
      have hden2 := mul_le_mul ha hq (by norm_num) (hlo 1).le
      have he := mul_le_mul_of_nonneg_right
        (mul_le_mul hden1 hden2 (by norm_num) (by positivity)) (hlo 0).le
      dsimp [p] at he ⊢
      nlinarith
    apply (div_le_iff₀ hd0).mpr
    have hm := hmesh 0
    nlinarith
  have hcap := cap_perturbation (lam := lam) hb.le hhb hx
  have hsum : boxCap lam 1 h lo (fun i => lo i+b)/(lam*p*(∏ i, lo i)) ≤
      (1000001/1000000 : ℝ)^4*density lam x+1/127000 := by
    calc
      _ ≤ (C+5*b)/(lam*p*(∏ i, lo i)) := div_le_div_of_nonneg_right hcap hd0.le
      _ = C/(lam*p*(∏ i, lo i))+(5*b)/(lam*p*(∏ i, lo i)) := add_div _ _ _
      _ ≤ _ := add_le_add hmain herr
  have hD0 : 0 ≤ density lam x := div_nonneg hC0 hd1.le
  calc
    _ = (501/500 : ℝ)*(1+h)*
        (boxCap lam 1 h lo (fun i => lo i+b)/(lam*p*(∏ i, lo i))) := by
      simp only [Fin.prod_univ_three]
      dsimp [p]
      field_simp
    _ ≤ (501/500 : ℝ)*(1000001/1000000)*
        ((1000001/1000000 : ℝ)^4*density lam x+1/127000) := by
      apply mul_le_mul _ hsum (div_nonneg (boxCap_nonneg _ _ _ (by linarith [hlo 0])) hd0.le)
        (by norm_num)
      exact mul_le_mul_of_nonneg_left hhsmall (by norm_num)
    _ ≤ _ := by nlinarith

/-- Half-open cofactor-share cells retain all grid endpoints exactly. -/
def cell (lo : Fin 3 → ℝ) (b : ℝ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (lo i) (lo i+b))

private theorem mem_cell {lo x : Fin 3 → ℝ} {b : ℝ} :
    x ∈ cell lo b ↔ ∀ i, lo i < x i ∧ x i ≤ lo i+b := by simp [cell]

private theorem measurable_cell (lo : Fin 3 → ℝ) (b : ℝ) : MeasurableSet (cell lo b) :=
  (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

private theorem cell_volume_ne_top (lo : Fin 3 → ℝ) (b : ℝ) : volume (cell lo b) ≠ ⊤ := by
  rw [cell,Real.volume_pi_Ioc]
  exact ne_of_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))

private theorem cell_volume (lo : Fin 3 → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    volume.real (cell lo b) = b^3 := by
  change (volume (cell lo b)).toReal = _
  rw [cell,Real.volume_pi_Ioc_toReal (fun _ => le_add_of_nonneg_right hb)]
  simp only [add_sub_cancel_left,Fin.prod_univ_three]
  ring

/-- The exact density is integrable on every interior comparison cell;
all four prime-share denominators are bounded away from zero there. -/
theorem integrableOn_density {lam b : ℝ} {lo : Fin 3 → ℝ}
    (hL : 0 < lam) (hlo : ∀ i, 0 < lo i)
    (hp : 0 < 1-∑ i, (lo i+b)) : IntegrableOn (density lam) (cell lo b) := by
  have hc : ContinuousOn (density lam) (Set.Icc lo (fun i => lo i+b)) := by
    apply ContinuousOn.div
    · dsimp [boxCap]
      fun_prop
    · fun_prop
    · intro x hx
      have hx0 (i : Fin 3) : 0 < x i := (hlo i).trans_le (hx.1 i)
      have hprod : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx0 i)
      have hp' : 0 < 1-∑ i, x i := hp.trans_le
        (sub_le_sub_left (Finset.sum_le_sum (fun i _ => hx.2 i)) _)
      exact ne_of_gt (by positivity)
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  have hx := mem_cell.mp hx
  exact ⟨fun i => (hx i).1.le,fun i => (hx i).2⟩

/-- The explicit finite-cell debit is paid by the exact angular integral
plus a numerical mesh cost. This estimates the cap before summing or
taking the signed prime-population floor. -/
theorem angular_integral_le {lam h b : ℝ} {lo : Fin 3 → ℝ}
    (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b)
    (hL : (17/25 : ℝ) ≤ lam)
    (hlo : ∀ i, 0 < lo i) (hmesh : ∀ i, b ≤ lo i/1000000000)
    (ha : (1/25 : ℝ) ≤ lo 1) (hq : (13/100 : ℝ) ≤ lo 2)
    (hp : (9/25 : ℝ) ≤ 1-∑ i, (lo i+b)) :
    (501/500 : ℝ)*((1+h)/lam)*boxCap lam 1 h lo (fun i => lo i+b) /
        (1-∑ i, (lo i+b))*(∏ i, b/lo i) ≤
      (1003/1000 : ℝ)*(∫ x in cell lo b, density lam x)+b^3/100000 := by
  have hf := integrableOn_density (by linarith : 0 < lam) hlo (by linarith)
  have hc (c : ℝ) := integrableOn_const (cell_volume_ne_top lo b) (C := c)
  have hi := setIntegral_mono_on (hc _)
    ((hf.const_mul (1003/1000 : ℝ)).add (hc (1/100000))) (measurable_cell lo b)
    (fun x hx => angular_pointwise_le hb hh hhb hL hlo hmesh ha hq hp
      (fun i => ⟨((mem_cell.mp hx) i).1.le,((mem_cell.mp hx) i).2⟩))
  simp only [Pi.add_apply] at hi
  rw [integral_add (hf.const_mul _) (hc _)] at hi
  simp only [integral_const_mul,setIntegral_const,cell_volume lo hb.le,smul_eq_mul] at hi
  convert hi using 1 <;> first | rfl | ((try simp only [Fin.prod_univ_three]); ring)

private theorem boxCap_smul {t : ℝ} (ht : 0 ≤ t) (L T h : ℝ) (lo hi : Fin 3 → ℝ) :
    boxCap (t*L) (t*T) (t*h) (fun i => t*lo i) (fun i => t*hi i) =
      t*boxCap L T h lo hi := by
  simp only [boxCap,← Finset.mul_sum,mul_min_of_nonneg _ _ ht,mul_max_of_nonneg _ _ ht,mul_zero]
  congr 2
  congr 1
  · ring
  · congr 1 <;> ring

private theorem cellDebit_normalized {t : ℝ} (ht : 0 < t)
    (N : ℕ) (L h y b : ℝ) (lo : Fin 3 → ℝ) :
    cellDebit N L t h y (fun i => t*lo i) (fun _ => t*b) =
      ((501/500 : ℝ)*((1+h/t)/(L/t))*
        boxCap (L/t) 1 (h/t) lo (fun i => lo i+b) /
        (1-∑ i, (lo i+b))*(∏ i, b/lo i))*
      ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (max 0 (-Real.cos (y*t))+|y| * h)*h) := by
  have hc : boxCap L t h (fun i => t*lo i) (fun i => t*lo i+t*b) =
      t*boxCap (L/t) 1 (h/t) lo (fun i => lo i+b) := by
    have he := boxCap_smul ht.le (L/t) 1 (h/t) lo (fun i => lo i+b)
    simpa only [mul_div_cancel₀ _ ht.ne',mul_one,mul_add] using he
  have hs : t-∑ i, (t*lo i+t*b) = t*(1-∑ i, (lo i+b)) := by
    simp only [Fin.sum_univ_three]
    ring
  have hratio : (1+h/t)/(L/t) = (t+h)/L := by
    have he : 1+h/t = (t+h)/t := by rw [add_div,div_self ht.ne']
    rw [he,div_div_div_cancel_right₀ ht.ne']
  have hprod : (∏ i, (t*b)/(t*lo i)) = ∏ i, b/lo i :=
    Finset.prod_congr rfl (fun i _ => mul_div_mul_left _ _ ht.ne')
  have hcancel (C P : ℝ) : (t*C)*(h/(t*P)) = C*(h/P) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    calc
      _ = (t*t⁻¹)*(C*(h*P⁻¹)) := by ring
      _ = _ := by rw [mul_inv_cancel₀ ht.ne',one_mul]
  dsimp only [cellDebit]
  rw [hc,hs,hprod,hratio]
  calc
    _ = (501/500 : ℝ)*((t+h)/L)*
        ((t*boxCap (L/t) 1 (h/t) lo (fun i => lo i+b))*(h/(t*(1-∑ i, (lo i+b)))))*
        (max 0 (-Real.cos (y*t))+|y| * h)*(Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (∏ i, b/lo i) := by ring
    _ = _ := by rw [hcancel]; ring

/-- An actual retained adverse prime cell is controlled by its exact
cofactor angular integral, with the original moment, allocation, phase and
arbitrary support mask unchanged. The 0.3 percent factor includes counting;
the additive 1/100000 cost is per unit angular volume. -/
theorem eventually_cell_integral_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L t y b : ℝ) (lo : Fin 3 → ℝ),
      0 < t → 0 < b → h/t ≤ b → (17/25 : ℝ) ≤ L/t → L ≤ t →
      2*(t+h) ≤ 3*L → (∀ i, α*N ≤ t*lo i) → β*N ≤ t*b →
      α*N ≤ t/4 → (∀ i, 0 < lo i) → (∀ i, b ≤ lo i/1000000000) →
      (1/25 : ℝ) ≤ lo 1 → (13/100 : ℝ) ≤ lo 2 →
      (9/25 : ℝ) ≤ 1-∑ i, (lo i+b) →
      -(((1003/1000 : ℝ)*(∫ x in cell lo b, density (L/t) x)+b^3/100000)*
        ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (∑ n ∈ boundaryCell S L t h y (fun i => t*lo i) (fun _ => t*b),
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_boundary_cell_floor hh hhu hα hβ]
    with N hN S A L t y b lo ht hb hhb hL hLt hTc hlogs hwidth hmin hlo hmesh ha hq hp
  have hL0 : 0 < L := by
    have he := (le_div_iff₀ ht).mp hL
    nlinarith
  have hl : α*N ≤ t-∑ i, (t*lo i+t*b) := by
    have he := mul_le_mul_of_nonneg_left hp ht.le
    simp only [Fin.sum_univ_three] at he ⊢
    nlinarith
  have hf := hN (fun i => t*lo i) (fun _ => t*b) A S L t y hlogs (fun _ => hwidth)
    hL0 hLt hTc hl
  have hbnd := mul_le_mul_of_nonneg_right
    (angular_integral_le hb (div_nonneg hh.le ht.le) hhb hL hlo hmesh ha hq hp)
    (show 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (-Real.cos (y*t))+|y| * h)*h by positivity)
  rw [← cellDebit_normalized ht N L h y b lo] at hbnd
  exact (neg_le_neg hbnd).trans hf

private theorem grid_cells_disjoint {M : ℕ} {a b : ℝ} (hb : 0 < b)
    {v w : Fin 3 → Fin M} (hne : v ≠ w) :
    Disjoint (cell (gridLo a b v) b) (cell (gridLo a b w) b) := by
  have hex : ∃ i, v i ≠ w i := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  obtain ⟨i,hi⟩ := hex
  have hn : (v i : ℕ) ≠ (w i : ℕ) := fun h => hi (Fin.ext h)
  apply Set.disjoint_left.mpr
  intro x hv hw
  have hv := (mem_cell.mp hv) i
  have hw := (mem_cell.mp hw) i
  dsimp [gridLo] at hv hw
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hh : (v i : ℝ)+1 ≤ (w i : ℝ) := by exact_mod_cast hlt
    nlinarith
  · have hh : (w i : ℝ)+1 ≤ (v i : ℝ) := by exact_mod_cast hgt
    nlinarith

private theorem cell_subset_unit {lo : Fin 3 → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hlo : ∀ i, 0 < lo i) (hp : 0 < 1-∑ i, (lo i+b)) :
    cell lo b ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
  intro x hx
  have hx := mem_cell.mp hx
  refine ⟨fun i => (hlo i).le.trans (hx i).1.le,fun i => ?_⟩
  have hs : lo i+b ≤ ∑ j, (lo j+b) :=
    Finset.single_le_sum (f := fun j => lo j+b)
      (fun j _ => add_nonneg (hlo j).le hb) (Finset.mem_univ i)
  linarith [hx i]

/-- All active cofactor cells are disjoint, so their mesh errors spend
one volume budget, not one budget per cell. No count, phase or signed
carrier is completed by this angular estimate. -/
theorem angular_family_le {M : ℕ} (I : Finset (Fin 3 → Fin M)) {a b lam h : ℝ}
    (hb : 0 < b) (hh : 0 ≤ h) (hhb : h ≤ b) (hL : (17/25 : ℝ) ≤ lam)
    (hg : ∀ v ∈ I,
      (∀ i, 0 < gridLo a b v i) ∧
      (∀ i, b ≤ gridLo a b v i/1000000000) ∧
      (1/25 : ℝ) ≤ gridLo a b v 1 ∧ (13/100 : ℝ) ≤ gridLo a b v 2 ∧
      (9/25 : ℝ) ≤ 1-∑ i, (gridLo a b v i+b)) :
    (∑ v ∈ I,
      (501/500 : ℝ)*((1+h)/lam)*boxCap lam 1 h (gridLo a b v) (fun i => gridLo a b v i+b) /
        (1-∑ i, (gridLo a b v i+b))*(∏ i, b/gridLo a b v i)) ≤
      (1003/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b, density lam x)+1/100000 := by
  have hdis : Set.Pairwise (I : Set (Fin 3 → Fin M))
      (fun v w => Disjoint (cell (gridLo a b v) b) (cell (gridLo a b w) b)) :=
    fun _ _ _ _ hne => grid_cells_disjoint hb hne
  have hf (v : Fin 3 → Fin M) (hv : v ∈ I) :=
    integrableOn_density (by linarith : 0 < lam) (hg v hv).1 (by linarith [(hg v hv).2.2.2.2])
  have hi := integral_biUnion_finset I (fun v _ => measurable_cell (gridLo a b v) b) hdis hf
  have hs := Finset.sum_le_sum (fun v hv => angular_integral_le hb hh hhb hL
    (hg v hv).1 (hg v hv).2.1 (hg v hv).2.2.1 (hg v hv).2.2.2.1 (hg v hv).2.2.2.2)
  have hvol : (∑ _v ∈ I, b^3) ≤ (1 : ℝ) := by
    have hj := integral_biUnion_finset (f := fun _ : Fin 3 → ℝ => (1 : ℝ)) I
      (fun v _ => measurable_cell (gridLo a b v) b) hdis
      (fun v _ => integrableOn_const (cell_volume_ne_top (gridLo a b v) b))
    have hsub : (⋃ v ∈ I, cell (gridLo a b v) b) ⊆
        Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
      apply Set.iUnion_subset
      intro v
      apply Set.iUnion_subset
      intro hv
      exact cell_subset_unit hb.le (hg v hv).1 (by linarith [(hg v hv).2.2.2.2])
    have he := setIntegral_mono_set (μ := (volume : Measure (Fin 3 → ℝ)))
      (s := ⋃ v ∈ I, cell (gridLo a b v) b)
      (t := Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1))
      ((continuous_const : Continuous (fun _ : Fin 3 → ℝ => (1 : ℝ))).integrableOn_Icc)
      (Filter.Eventually.of_forall (fun _ => zero_le_one)) (Filter.Eventually.of_forall hsub)
    rw [hj] at he
    simp only [setIntegral_const,cell_volume _ hb.le,smul_eq_mul,mul_one] at he
    simpa only [Measure.real,Real.volume_Icc_pi,sub_zero,ENNReal.ofReal_one,
      Finset.prod_const_one,ENNReal.toReal_one] using he
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← hi] at hs
  have he : (∑ _v ∈ I, b^3/100000) ≤ (1/100000 : ℝ) := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hvol (by norm_num)
  linarith

/-- Simultaneous signed transfer for an entire finite family of angular
cells. The numerical error is 1/100000 for the WHOLE family. All literal
support, allocation, positive-coefficient and negative-cosine predicates
remain inside `boundaryCell`; overlapping product incidences only overpay
an adverse population. -/
theorem eventually_family_integral_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (M : ℕ) (I : Finset (Fin 3 → Fin M))
      (L t y a b : ℝ),
      0 < t → 0 < b → h/t ≤ b → (17/25 : ℝ) ≤ L/t → L ≤ t →
      2*(t+h) ≤ 3*L → α*N ≤ t*a → β*N ≤ t*b → α*N ≤ t/4 →
      (∀ v ∈ I,
        (∀ i, 0 < gridLo a b v i) ∧
        (∀ i, b ≤ gridLo a b v i/1000000000) ∧
        (1/25 : ℝ) ≤ gridLo a b v 1 ∧ (13/100 : ℝ) ≤ gridLo a b v 2 ∧
        (9/25 : ℝ) ≤ 1-∑ i, (gridLo a b v i+b)) →
      -(((1003/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b, density (L/t) x)+1/100000)*
        ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (∑ n ∈ I.biUnion (fun v => boundaryCell S L t h y
              (fun i => t*gridLo a b v i) (fun _ => t*b)),
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_boundary_cell_floor hh hhu hα hβ]
    with N hN S A M I L t y a b ht hb hhb hL hLt hTc hlogs hwidth hmin hg
  let D := fun v : Fin 3 → Fin M => boundaryCell S L t h y
    (fun i => t*gridLo a b v i) (fun _ => t*b)
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let E := (Real.exp (-t/2)*(t+h)^N/N.factorial)*
    (max 0 (-Real.cos (y*t))+|y| * h)*h
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hL0 : 0 < L := by
    have he := (le_div_iff₀ ht).mp hL
    nlinarith
  have hcell (v : Fin 3 → Fin M) (hv : v ∈ I) :
      -cellDebit N L t h y (fun i => t*gridLo a b v i) (fun _ => t*b) ≤ (∑ n ∈ D v, f n).re := by
    have hl : α*N ≤ t-∑ i, (t*gridLo a b v i+t*b) := by
      have he := mul_le_mul_of_nonneg_left (hg v hv).2.2.2.2 ht.le
      simp only [Fin.sum_univ_three] at he ⊢
      nlinarith
    apply hN _ _ A S L t y _ (fun _ => hwidth) hL0 hLt hTc hl
    intro i
    exact hlogs.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb.le)) ht.le)
  have hs := Finset.sum_le_sum hcell
  have hu := ZetaRieszJointPrimeCells.sum_cells_le_union_of_nonpos I D (fun n => (f n).re)
    (fun v _ n hn => boundaryCell_atom_nonpos S A N L t h y _ _ hn)
  simp only [← Complex.re_sum,Finset.sum_neg_distrib] at hs
  simp only [← Complex.re_sum] at hu
  have hbnd := mul_le_mul_of_nonneg_right
    (angular_family_le I hb (div_nonneg hh.le ht.le) hhb hL hg) hE
  rw [Finset.sum_mul] at hbnd
  have hnorm : (∑ v ∈ I, cellDebit N L t h y (fun i => t*gridLo a b v i) (fun _ => t*b)) ≤
      ((1003/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b, density (L/t) x)+1/100000)*E := by
    simpa only [cellDebit_normalized ht,E] using hbnd
  exact (neg_le_neg hnorm).trans (hs.trans hu)

private theorem gridLo_smul (t a b : ℝ) {M : ℕ} (v : Fin 3 → Fin M) :
    gridLo (t*a) (t*b) v = fun i => t*gridLo a b v i := by
  funext i
  dsimp [gridLo]
  ring

private theorem active_normalized_geometry (S : Finset ℕ) {L t h y b : ℝ}
    {lo : Fin 3 → ℝ} (ht : 0 < t) (hhb : h/t ≤ b) (hb : b ≤ 1/249600)
    (hL : (693/1015 : ℝ)*t ≤ L) (hLt : L ≤ t)
    (hne : (boundaryCell (clippedSupport S) L t h y (fun i => t*lo i)
      (fun _ => t*b)).Nonempty) :
    (1/25 : ℝ) ≤ lo 1 ∧ (13/100 : ℝ) ≤ lo 2 ∧
      (9/25 : ℝ) ≤ 1-∑ i, (lo i+b) := by
  have hwidth : h ≤ t*b := by simpa only [mul_comm] using (div_le_iff₀ ht).mp hhb
  have hg := active_cell_geometry S hwidth
    (by nlinarith : t*b ≤ t/249600) hL hLt hne
  simp only [Fin.sum_univ_three] at hg ⊢
  refine ⟨?_,?_,?_⟩ <;> nlinarith [hg.1,hg.2.1,hg.2.2.1]

/-- The complete clipped adverse population is controlled by the exact
integral over its nonempty grid cells and ONE 1/100000 mesh budget.
Every ordering face and literal largest-prime mask remains in the finite
cover. This does not identify the covering domain with the smaller domain
of the optional two-dimensional angular certificate. -/
theorem eventually_complete_integral_floor {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (M : ℕ) (L t y a b : ℝ),
      0 < t → 0 < a → 0 < b → h/t ≤ b → b ≤ 1/249600 →
      1000000000*b ≤ a → (693/1015 : ℝ)*(t+h) ≤ L → L ≤ t →
      2*(t+h) ≤ 3*L → α*N ≤ t*a → β*N ≤ t*b → α*N ≤ t/4 →
      t+h ≤ t*a+M*(t*b) →
      let P := clippedSupport S
      let I := (gridCover M (t*a) (t*b) t).filter (fun v =>
        (boundaryCell P L t h y (fun i => t*gridLo a b v i) (fun _ => t*b)).Nonempty);
      -(((1003/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b, density (L/t) x)+1/100000)*
        ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (∑ n ∈ adversePopulation P L t h y (t*a),
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_family_integral_floor hh hhu hα hβ]
    with N hN S A M L t y a b ht ha hb hhb hbT hab hL hLt hTc hlogs hwidth hmin hcover
  dsimp only
  let P := clippedSupport S
  let I := (gridCover M (t*a) (t*b) t).filter (fun v =>
    (boundaryCell P L t h y (fun i => t*gridLo a b v i) (fun _ => t*b)).Nonempty)
  let D := fun v : Fin 3 → Fin M => boundaryCell P L t h y
    (fun i => t*gridLo a b v i) (fun _ => t*b)
  let U := I.biUnion D
  let Q := adversePopulation P L t h y (t*a)
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hL' : (693/1015 : ℝ)*t ≤ L := by linarith
  have hL0 : 0 < L := by nlinarith
  have hgeom (v : Fin 3 → Fin M) (hv : v ∈ I) :
      (∀ i, 0 < gridLo a b v i) ∧
      (∀ i, b ≤ gridLo a b v i/1000000000) ∧
      (1/25 : ℝ) ≤ gridLo a b v 1 ∧ (13/100 : ℝ) ≤ gridLo a b v 2 ∧
      (9/25 : ℝ) ≤ 1-∑ i, (gridLo a b v i+b) := by
    have hbase (i : Fin 3) : a ≤ gridLo a b v i :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hb.le)
    refine ⟨fun i => ha.trans_le (hbase i),fun i => by linarith [hbase i],?_⟩
    exact active_normalized_geometry S ht hhb hbT hL' hLt (Finset.mem_filter.mp hv).2
  have hf := hN P A M I L t y a b ht hb hhb
    ((le_div_iff₀ ht).mpr (by nlinarith)) hLt hTc hlogs hwidth hmin hgeom
  have hQU : Q ⊆ U := by
    intro n hn
    have hwidth' := (div_le_iff₀ ht).mp hhb
    have hg := adversePopulation_subset_grid P M
      (by nlinarith : h ≤ t/100) (by positivity : 0 < t*b)
      (by nlinarith : t*b ≤ t/100) hL0 hLt
      (by nlinarith : (17/25 : ℝ)*(t+h) ≤ L) hcover hn
    obtain ⟨v,hv,hnv⟩ := Finset.mem_biUnion.mp hg
    rw [gridLo_smul] at hnv
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,⟨n,hnv⟩⟩,hnv⟩
  have hrest : (∑ n ∈ U\Q, f n).re ≤ 0 := by
    rw [Complex.re_sum]
    apply Finset.sum_nonpos
    intro n hn
    obtain ⟨v,_hv,hnv⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hn).1
    exact boundaryCell_atom_nonpos P A N L t h y _ _ hnv
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hQU)
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ Q, f n).re
  change _ ≤ (∑ n ∈ U, f n).re at hf
  linarith

/-- On the original dyadic schedule every clipped adverse four-prime
label above log p>delta*N has the exact-integral floor. Refinement changes
only the finite covering mesh. The core response, moment, cutoff, allocation
and entire signed complement are unchanged. -/
theorem eventually_core_integral_floor {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∃ M : ℕ, ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let a := δ*N/t
      let b := (δ/1000000000)*N/t
      let P := clippedSupport S
      let I := (gridCover M (δ*N) ((δ/1000000000)*N) t).filter (fun v =>
        (boundaryCell P L t h y (fun i => t*gridLo a b v i) (fun _ => (δ/1000000000)*N)).Nonempty)
      let Q := adversePopulation P L t h y (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∑ n ∈ S\Q, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (((1003/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b, density (L/t) x)+1/100000)*
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
  refine ⟨M,?_⟩
  filter_upwards [ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_complete_integral_floor hh hhu hδ hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU (h := h)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hwidth,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hN hch hratio hwidth hj t y
  dsimp only
  intro htlo hthi
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
  have hsmall : b ≤ 1/249600 := by
    apply (div_le_iff₀ ht).mpr
    dsimp [β]
    nlinarith
  have hmesh : 1000000000*b ≤ a := by dsimp [a,b,β]; ring_nf; rfl
  have hch' := hch t htlo hthi
  have hcut := (le_div_iff₀ (show 0 < t+h by linarith)).mp
    (hratio (t+h) (by linarith) hthi).1
  have hcover := mul_le_mul_of_nonneg_right hM hn0
  have hf := hN S A M L t y a b ht ha hb
    (by exact div_le_div_of_nonneg_right hwidth ht.le) hsmall hmesh hcut hch'.1 hch'.2
    (by rw [hta]) (by rw [htb]) (by nlinarith)
    (by rw [hta,htb]; nlinarith [mul_nonneg hδ.le hn0])
  dsimp only at hf
  rw [hta,htb] at hf
  have hQS : Q ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hQS)
  rw [Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  change _ ≤ (∑ n ∈ Q, f n).re at hf
  linarith

/-- The new cell density is literally the existing capped least-prime
integrand, with the other cofactor share left unintegrated. -/
theorem density_eq_ordered (lam r a q : ℝ) :
    density lam ![r,a,q] =
      min r (max 0 (min (lam-(1-r-a-q))
        (min (1-lam-q) (1+(1-r-a-q)-2*lam)))) /
        (lam*(1-r-a-q)*q*(r*a)) := by
  simp [density,boxCap,Fin.sum_univ_three,Fin.prod_univ_three]
  congr 1
  · congr 2
    congr 1
    · ring
    · congr 1; ring
  · ring

end
end RiemannGaussian.ZetaRieszFourInteriorBudget
