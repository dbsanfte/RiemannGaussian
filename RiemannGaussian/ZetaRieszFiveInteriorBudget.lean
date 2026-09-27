/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPrimeCells
import RiemannGaussian.ZetaRieszFourInteriorBudget

/-!
# Angular-integral credit for disjoint literal five-prime populations

The common three-cap coefficient is retained before the prime-cell lower
bound. A fine cofactor grid loses at most one explicit angular-volume
budget. The purpose is a signed inequality for the original arithmetic
population, with its entire complementary carrier unchanged.
-/

namespace RiemannGaussian.ZetaRieszFiveInteriorBudget
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszFivePrimeCells ZetaRieszJointPrimeCells

/-- The three-cap density in the four ordered cofactor shares. -/
def density (lam : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  boxCap lam 1 0 x x / (lam*(1-∑ i, x i)*∏ i, x i)

private theorem cap_perturbation {lam h b : ℝ} {lo x : Fin 4 → ℝ}
    (hb : 0 ≤ b) (hh : h ≤ b)
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ lo i+b) :
    boxCap lam 1 0 x x ≤ boxCap lam 1 h lo (fun i => lo i+b)+12*b := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have hc (A B C D : ℝ) (hA : A ≤ C+4*b) (hB : B ≤ D+4*b) :
      min (x 0) (max 0 (min A B)) ≤ min (lo 0) (max 0 (min C D))+4*b := by
    have hm := min_le_min hA hB
    simp only [min_add_add_right] at hm
    have hz := max_le_max (show (0 : ℝ) ≤ 0+4*b by positivity) hm
    simp only [max_add_add_right] at hz
    simpa only [min_add_add_right] using
      min_le_min (show x 0 ≤ lo 0+4*b by linarith) hz
  have ha := hc (lam-1+x 2+x 1+x 0) (1-lam-x 2)
    (lam-1-h+lo 2+lo 1+lo 0) (1-lam-(lo 2+b)) (by linarith) (by linarith)
  have hq := hc (lam-1+x 3+x 1+x 0) (1-lam-x 3)
    (lam-1-h+lo 3+lo 1+lo 0) (1-lam-(lo 3+b)) (by linarith) (by linarith)
  have hp := hc (lam-x 3-x 2) (x 3+x 2+x 1+x 0-lam)
    (lam-(lo 3+b)-(lo 2+b)) (lo 3+lo 2+lo 1+lo 0-lam)
    (by linarith) (by linarith)
  simp only [boxCap,sub_zero]
  linarith

/-- The fine-cell lower score retains 99.6 percent of the exact density,
with an additive loss at most 1/100000 per unit angular volume. This pays
the already-proved 997/1000 prime-count/allocation cost as well. -/
theorem angular_pointwise_lower {lam h b : ℝ} {lo x : Fin 4 → ℝ}
    (hb : 0 < b) (hsmall : b ≤ 1/1000000000000000000)
    (hhb : h ≤ b) (hL : (17/25 : ℝ) ≤ lam)
    (hlo : ∀ i, (1/200 : ℝ) ≤ lo i)
    (hp : (1/10 : ℝ) ≤ 1-∑ i, (lo i+b))
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ lo i+b) :
    (996/1000 : ℝ)*density lam x-1/100000 ≤
      (997/1000 : ℝ)*(1/lam)*boxCap lam 1 h lo (fun i => lo i+b) /
        (1-∑ i, lo i)*(∏ i, 1/(lo i+b)) := by
  let p := 1-∑ i, lo i
  let q := 1-∑ i, x i
  let C := boxCap lam 1 0 x x
  let B := boxCap lam 1 h lo (fun i => lo i+b)
  have hL0 : 0 < lam := by linarith
  have hlo0 (i : Fin 4) : 0 < lo i := by linarith [hlo i]
  have hx0 (i : Fin 4) : 0 < x i := (hlo0 i).trans_le (hx i).1
  have hqlo : (1/10 : ℝ) ≤ q := hp.trans
    (sub_le_sub_left (Finset.sum_le_sum (fun i _ => (hx i).2)) _)
  have hqp : q ≤ p := sub_le_sub_left (Finset.sum_le_sum (fun i _ => (hx i).1)) _
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hC0 : 0 ≤ C := boxCap_nonneg _ _ _ (hx0 0).le
  have hB0 : 0 ≤ B := boxCap_nonneg _ _ _ (hlo0 0).le
  have hpProd : 0 < ∏ i, (lo i+b) :=
    Finset.prod_pos (fun i _ => by linarith [hlo0 i])
  have hxProd : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx0 i)
  have hd0 : 0 < lam*p*(∏ i, (lo i+b)) := by positivity
  have hd1 : 0 < lam*q*(∏ i, x i) := by positivity
  have hpRel : p ≤ (1000001/1000000 : ℝ)*q := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hx i).2)
    dsimp [p,q] at *
    simp only [Fin.sum_univ_four] at hs hqlo ⊢
    linarith
  have hxRel (i : Fin 4) : lo i+b ≤ (1000001/1000000 : ℝ)*x i := by
    linarith [hx i,hlo i]
  have hd : lam*p*(∏ i, (lo i+b)) ≤
      (1000001/1000000 : ℝ)^5*(lam*q*(∏ i, x i)) := by
    have he := mul_le_mul_of_nonneg_left
      (mul_le_mul hpRel
        (Finset.prod_le_prod (fun i _ => by linarith [hlo0 i]) (fun i _ => hxRel i))
        hpProd.le (by positivity)) hL0.le
    simp only [Fin.prod_univ_four] at he ⊢
    convert he using 1 <;> first | rfl | ring
  have hmain : C/(lam*q*(∏ i, x i)) ≤
      (1000001/1000000 : ℝ)^5*(C/(lam*p*(∏ i, (lo i+b)))) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hd1 hd0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hC0]
  have hden : (17/25 : ℝ)*(1/10)*(1/200)^4 ≤ lam*p*(∏ i, (lo i+b)) := by
    have he := mul_le_mul
      (mul_le_mul hL (hqp.trans' hqlo) (by norm_num) hL0.le)
      (Finset.prod_le_prod (s := Finset.univ) (fun _ _ => (by norm_num : (0 : ℝ) ≤ 1/200))
        (fun i _ => (hlo i).trans (le_add_of_nonneg_right hb.le)))
      (by positivity) (by positivity)
    norm_num [Fin.prod_univ_four] at he ⊢
    exact he
  have herr : (12*b)/(lam*p*(∏ i, (lo i+b))) ≤ (1/1000000 : ℝ) := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith
  have hcap := cap_perturbation (lam := lam) hb.le hhb hx
  have hsum : C/(lam*p*(∏ i, (lo i+b))) ≤
      B/(lam*p*(∏ i, (lo i+b)))+1/1000000 := by
    calc
      _ ≤ (B+12*b)/(lam*p*(∏ i, (lo i+b))) := div_le_div_of_nonneg_right hcap hd0.le
      _ = _+_ := add_div _ _ _
      _ ≤ _ := add_le_add le_rfl herr
  have hD0 : 0 ≤ B/(lam*p*(∏ i, (lo i+b))) := div_nonneg hB0 hd0.le
  have he := hmain.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  change density lam x ≤ _ at he
  have hnum : (996/1000 : ℝ)*density lam x-1/100000 ≤
      (997/1000 : ℝ)*(B/(lam*p*(∏ i, (lo i+b)))) := by nlinarith
  convert hnum using 1
  simp only [Fin.prod_univ_four]
  dsimp [B,p]
  field_simp

/-- Half-open cofactor cells keep each shared grid face on exactly one side. -/
def cell (lo : Fin 4 → ℝ) (b : ℝ) : Set (Fin 4 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (lo i) (lo i+b))

private theorem mem_cell {lo x : Fin 4 → ℝ} {b : ℝ} :
    x ∈ cell lo b ↔ ∀ i, lo i < x i ∧ x i ≤ lo i+b := by simp [cell]

private theorem measurable_cell (lo : Fin 4 → ℝ) (b : ℝ) : MeasurableSet (cell lo b) :=
  (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

private theorem cell_volume_ne_top (lo : Fin 4 → ℝ) (b : ℝ) : volume (cell lo b) ≠ ⊤ := by
  rw [cell,Real.volume_pi_Ioc]
  exact ne_of_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))

private theorem cell_volume (lo : Fin 4 → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    volume.real (cell lo b) = b^4 := by
  change (volume (cell lo b)).toReal = _
  rw [cell,Real.volume_pi_Ioc_toReal (fun _ => le_add_of_nonneg_right hb)]
  simp only [add_sub_cancel_left,Fin.prod_univ_four]
  ring

/-- Every cell used for the literal lower bound has an integrable exact
cap density; the four cofactor shares and the owner share stay positive. -/
theorem integrableOn_density {lam b : ℝ} {lo : Fin 4 → ℝ}
    (hL : 0 < lam) (hlo : ∀ i, 0 < lo i)
    (hp : 0 < 1-∑ i, (lo i+b)) : IntegrableOn (density lam) (cell lo b) := by
  have hc : ContinuousOn (density lam) (Set.Icc lo (fun i => lo i+b)) := by
    apply ContinuousOn.div
    · dsimp [boxCap]
      fun_prop
    · fun_prop
    · intro x hx
      have hx0 (i : Fin 4) : 0 < x i := (hlo i).trans_le (hx.1 i)
      have hprod : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx0 i)
      have hp' : 0 < 1-∑ i, x i := hp.trans_le
        (sub_le_sub_left (Finset.sum_le_sum (fun i _ => hx.2 i)) _)
      exact ne_of_gt (by positivity)
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  have hx := mem_cell.mp hx
  exact ⟨fun i => (hx i).1.le,fun i => (hx i).2⟩

/-- An exact angular integral is paid by the literal five-prime cell
score with numerical loss proportional to its angular volume. -/
theorem angular_integral_lower {lam h b : ℝ} {lo : Fin 4 → ℝ}
    (hb : 0 < b) (hsmall : b ≤ 1/1000000000000000000)
    (hhb : h ≤ b) (hL : (17/25 : ℝ) ≤ lam)
    (hlo : ∀ i, (1/200 : ℝ) ≤ lo i)
    (hp : (1/10 : ℝ) ≤ 1-∑ i, (lo i+b)) :
    (996/1000 : ℝ)*(∫ x in cell lo b, density lam x)-b^4/100000 ≤
      (997/1000 : ℝ)*(1/lam)*boxCap lam 1 h lo (fun i => lo i+b) /
        (1-∑ i, lo i)*(∏ i, b/(lo i+b)) := by
  have hf := integrableOn_density (by linarith : 0 < lam)
    (fun i => by linarith [hlo i]) (by linarith : 0 < 1-∑ i, (lo i+b))
  have hc (c : ℝ) := integrableOn_const (cell_volume_ne_top lo b) (C := c)
  have hi := setIntegral_mono_on ((hf.const_mul (996/1000 : ℝ)).sub (hc (1/100000)))
    (hc _) (measurable_cell lo b) (fun x hx => angular_pointwise_lower
      hb hsmall hhb hL hlo hp (fun i => ⟨((mem_cell.mp hx) i).1.le,((mem_cell.mp hx) i).2⟩))
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hf.const_mul _) (hc _)] at hi
  simp only [integral_const_mul,setIntegral_const,cell_volume lo hb.le,smul_eq_mul] at hi
  convert hi using 1 <;> first | rfl | ((try simp only [Fin.prod_univ_four]); ring)

/-- The fixed grid is indexed without evaluating its enormous finite size. -/
def gridLo (a b : ℝ) {M : ℕ} (v : Fin 4 → Fin M) (i : Fin 4) : ℝ :=
  a+(v i : ℕ)*b

private theorem grid_cells_disjoint {M : ℕ} {a b : ℝ} (hb : 0 < b)
    {v w : Fin 4 → Fin M} (hne : v ≠ w) :
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

private theorem cell_subset_unit {lo : Fin 4 → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hlo : ∀ i, 0 < lo i) (hp : 0 < 1-∑ i, (lo i+b)) :
    cell lo b ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
  intro x hx
  have hx := mem_cell.mp hx
  refine ⟨fun i => (hlo i).le.trans (hx i).1.le,fun i => ?_⟩
  have hs : lo i+b ≤ ∑ j, (lo j+b) :=
    Finset.single_le_sum (f := fun j => lo j+b)
      (fun j _ => add_nonneg (hlo j).le hb) (Finset.mem_univ i)
  linarith [hx i]

/-- The full family loses only ONE 1/100000 angular budget. In particular
the loss is not multiplied by the number of grid cells or prime labels. -/
theorem angular_family_lower {M : ℕ} (I : Finset (Fin 4 → Fin M)) {a b lam h : ℝ}
    (hb : 0 < b) (hsmall : b ≤ 1/1000000000000000000)
    (hhb : h ≤ b) (hL : (17/25 : ℝ) ≤ lam)
    (hg : ∀ v ∈ I, (∀ i, (1/200 : ℝ) ≤ gridLo a b v i) ∧
      (1/10 : ℝ) ≤ 1-∑ i, (gridLo a b v i+b)) :
    (996/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b, density lam x)-1/100000 ≤
      ∑ v ∈ I, (997/1000 : ℝ)*(1/lam)*
        boxCap lam 1 h (gridLo a b v) (fun i => gridLo a b v i+b) /
        (1-∑ i, gridLo a b v i)*(∏ i, b/(gridLo a b v i+b)) := by
  have hdis : Set.Pairwise (I : Set (Fin 4 → Fin M))
      (fun v w => Disjoint (cell (gridLo a b v) b) (cell (gridLo a b w) b)) :=
    fun _ _ _ _ hne => grid_cells_disjoint hb hne
  have hf (v : Fin 4 → Fin M) (hv : v ∈ I) :=
    integrableOn_density (lo := gridLo a b v) (b := b) (by linarith : 0 < lam)
      (fun i => by linarith [(hg v hv).1 i]) (by linarith [(hg v hv).2])
  have hi := integral_biUnion_finset I (fun v _ => measurable_cell (gridLo a b v) b) hdis hf
  have hs := Finset.sum_le_sum (fun v hv => angular_integral_lower hb hsmall hhb hL
    (hg v hv).1 (hg v hv).2)
  have hvol : (∑ _v ∈ I, b^4) ≤ (1 : ℝ) := by
    have hj := integral_biUnion_finset (f := fun _ : Fin 4 → ℝ => (1 : ℝ)) I
      (fun v _ => measurable_cell (gridLo a b v) b) hdis
      (fun v _ => integrableOn_const (cell_volume_ne_top (gridLo a b v) b))
    have hsub : (⋃ v ∈ I, cell (gridLo a b v) b) ⊆
        Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) := by
      apply Set.iUnion_subset
      intro v
      apply Set.iUnion_subset
      intro hv
      exact cell_subset_unit hb.le (fun i => by linarith [(hg v hv).1 i])
        (by linarith [(hg v hv).2])
    have he := setIntegral_mono_set (μ := (volume : Measure (Fin 4 → ℝ)))
      (s := ⋃ v ∈ I, cell (gridLo a b v) b)
      (t := Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1))
      ((continuous_const : Continuous (fun _ : Fin 4 → ℝ => (1 : ℝ))).integrableOn_Icc)
      (Filter.Eventually.of_forall (fun _ => zero_le_one)) (Filter.Eventually.of_forall hsub)
    rw [hj] at he
    simp only [setIntegral_const,cell_volume _ hb.le,smul_eq_mul,mul_one] at he
    simpa only [Measure.real,Real.volume_Icc_pi,sub_zero,ENNReal.ofReal_one,
      Finset.prod_const_one,ENNReal.toReal_one] using he
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← hi] at hs
  have he : (∑ _v ∈ I, b^4/100000) ≤ (1/100000 : ℝ) := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hvol (by norm_num)
  linarith

private theorem boxCap_smul {t : ℝ} (ht : 0 ≤ t) (L T h : ℝ) (lo hi : Fin 4 → ℝ) :
    boxCap (t*L) (t*T) (t*h) (fun i => t*lo i) (fun i => t*hi i) =
      t*boxCap L T h lo hi := by
  simp only [boxCap,mul_add,mul_sub,mul_min_of_nonneg _ _ ht,
    mul_max_of_nonneg _ _ ht,mul_zero]

private theorem cellCredit_normalized {t : ℝ} (ht : 0 < t)
    (N : ℕ) (L h y b : ℝ) (lo : Fin 4 → ℝ) :
    cellCredit N L t h y (fun i => t*lo i) (fun _ => t*b) =
      ((997/1000 : ℝ)*(1/(L/t))*
        boxCap (L/t) 1 (h/t) lo (fun i => lo i+b) /
        (1-∑ i, lo i)*(∏ i, b/(lo i+b)))*
      ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
        max 0 (-Real.cos (y*t)-|y| * h)*h) := by
  have hc : boxCap L t h (fun i => t*lo i) (fun i => t*lo i+t*b) =
      t*boxCap (L/t) 1 (h/t) lo (fun i => lo i+b) := by
    have he := boxCap_smul ht.le (L/t) 1 (h/t) lo (fun i => lo i+b)
    simpa only [mul_div_cancel₀ _ ht.ne',mul_one,mul_add] using he
  have hs : t-∑ i, t*lo i = t*(1-∑ i, lo i) := by
    simp only [Fin.sum_univ_four]
    ring
  have hratio : 1/(L/t) = t/L := by simp only [one_div,inv_div]
  have hprod : (∏ i, (t*b)/(t*lo i+t*b)) = ∏ i, b/(lo i+b) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_add,mul_div_mul_left _ _ ht.ne']
  have hcancel (C P : ℝ) : (t*C)*(h/(t*P)) = C*(h/P) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    calc
      _ = (t*t⁻¹)*(C*(h*P⁻¹)) := by ring
      _ = _ := by rw [mul_inv_cancel₀ ht.ne',one_mul]
  dsimp only [cellCredit]
  rw [hc,hs,hprod,hratio]
  calc
    _ = (997/1000 : ℝ)*(t/L)*
        ((t*boxCap (L/t) 1 (h/t) lo (fun i => lo i+b))*(h/(t*(1-∑ i, lo i))))*
        max 0 (-Real.cos (y*t)-|y| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
        (∏ i, b/(lo i+b)) := by ring
    _ = _ := by rw [hcancel]; ring

private theorem grid_separated {M : ℕ} {a b : ℝ} (hb : 0 < b)
    {v w : Fin 4 → Fin M} (hne : v ≠ w) :
    ∃ i, gridLo a b v i+b ≤ gridLo a b w i ∨ gridLo a b w i+b ≤ gridLo a b v i := by
  have hex : ∃ i, v i ≠ w i := by
    by_contra hn
    push Not at hn
    exact hne (funext hn)
  obtain ⟨i,hi⟩ := hex
  have hn : (v i : ℕ) ≠ (w i : ℕ) := fun h => hi (Fin.ext h)
  refine ⟨i,?_⟩
  dsimp [gridLo]
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · left
    have hh : (v i : ℝ)+1 ≤ (w i : ℝ) := by exact_mod_cast hlt
    nlinarith
  · right
    have hh : (w i : ℝ)+1 ≤ (v i : ℝ) := by exact_mod_cast hgt
    nlinarith

/-- A numerical exact-integral credit inside the ORIGINAL core. Every
five-prime population is literal and disjoint. Its allocation/counting and
fine-grid errors together retain 996/1000 of the covered angular integral,
with ONE 1/100000 angular loss. All other labels remain signed, for all
phases. The uncovered favorable-domain boundary still needs comparison. -/
theorem eventually_family_core_floor {u h a b : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/1000000000000000000) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset (Fin 4 → Fin M)) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D := I.biUnion (fun v => supplyCell t h y
        (fun i => t*gridLo a b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∀ v ∈ I,
        (∀ i, (1/200 : ℝ) ≤ gridLo a b v i) ∧
        (∀ i k, i < k → gridLo a b v i+b ≤ gridLo a b v k) ∧
        (1/10 : ℝ) ≤ 1-∑ i, (gridLo a b v i+b) ∧
        gridLo a b v 3+b ≤ 1-∑ i, (gridLo a b v i+b) ∧
        1-(∑ i, gridLo a b v i)+h/t ≤ 9/16 ∧
        1-gridLo a b v 3-gridLo a b v 2+h/t ≤ L/t ∧
        L/t ≤ 1-(gridLo a b v 1+b)-(gridLo a b v 0+b)) →
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (((996/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b,
          density (L/t) x)-1/100000)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hwidth : ∀ᶠ N : ℕ in atTop, h ≤ b*N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hb).eventually_ge_atTop h
  filter_upwards [eventually_joint_cell_family_floor (ι := Fin 0) (κ := Fin 4 → Fin M)
      hu hU hh hhu (by norm_num : (0 : ℝ) < 1/200) hb,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (ZetaRieszFivePrimePairSupply.eventually_core_cutoff_ratio hu.le hU),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hwidth,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hratio hwidth hj I t y
  dsimp only
  intro htlo hthi hg
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hj
  have hNt : (N : ℝ) ≤ t := by nlinarith
  have ht : 0 < t := by linarith
  have hhb : h/t ≤ b := (div_le_iff₀ ht).mpr (by nlinarith)
  have hlow := (hratio (t+h) (by linarith) hthi).1
  have hL : (17/25 : ℝ) ≤ L/t := by
    have he := (le_div_iff₀ (show 0 < t+h by linarith)).mp hlow
    apply (le_div_iff₀ ht).mpr
    dsimp [L]
    nlinarith
  have h5 (v : Fin 4 → Fin M) (hv : v ∈ I) :
      (∀ i, (1/200 : ℝ)*N ≤ t*gridLo a b v i) ∧
      (∀ _i : Fin 4, b*N ≤ t*b) ∧
      (∀ i k, i < k → t*gridLo a b v i+t*b ≤ t*gridLo a b v k) ∧
      (1/200 : ℝ)*N ≤ t-∑ i, (t*gridLo a b v i+t*b) ∧
      t*gridLo a b v 3+t*b ≤ t-∑ i, (t*gridLo a b v i+t*b) ∧
      t-(∑ i, t*gridLo a b v i)+h ≤ (9/16 : ℝ)*t ∧
      t-t*gridLo a b v 3-t*gridLo a b v 2+h ≤ L ∧
      L ≤ t-(t*gridLo a b v 1+t*b)-(t*gridLo a b v 0+t*b) := by
    obtain ⟨hlo,ho,hp,hq,hmax,hsat,htriple⟩ := hg v hv
    refine ⟨fun i => ?_,fun _ => by nlinarith,fun i k hik => ?_,?_,?_,?_,?_,?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left (hlo i) ht.le]
    · nlinarith [mul_le_mul_of_nonneg_left (ho i k hik) ht.le]
    · have he := mul_le_mul_of_nonneg_left hp ht.le
      simp only [Fin.sum_univ_four] at he ⊢
      nlinarith
    · have he := mul_le_mul_of_nonneg_left hq ht.le
      simp only [Fin.sum_univ_four] at he ⊢
      nlinarith
    · have he := mul_le_mul_of_nonneg_left hmax ht.le
      simp only [mul_add,mul_div_cancel₀ _ ht.ne',Fin.sum_univ_four] at he ⊢
      nlinarith
    · have he := mul_le_mul_of_nonneg_left hsat ht.le
      simp only [mul_add,mul_div_cancel₀ _ ht.ne'] at he
      nlinarith
    · have he := mul_le_mul_of_nonneg_left htriple ht.le
      simp only [mul_div_cancel₀ _ ht.ne'] at he
      nlinarith
  have hsep (v : Fin 4 → Fin M) (_hv : v ∈ I) (w : Fin 4 → Fin M)
      (_hw : w ∈ I) (hne : v ≠ w) :
      ∃ i, t*gridLo a b v i+t*b ≤ t*gridLo a b w i ∨
        t*gridLo a b w i+t*b ≤ t*gridLo a b v i := by
    obtain ⟨i,hi⟩ := grid_separated (a := a) hb hne
    refine ⟨i,?_⟩
    rcases hi with hi | hi
    · left
      nlinarith [mul_le_mul_of_nonneg_left hi ht.le]
    · right
      nlinarith [mul_le_mul_of_nonneg_left hi ht.le]
  have hf := hJ ∅ I (fun _ _ => 0) (fun _ _ => 0)
    (fun v i => t*gridLo a b v i) (fun _ _ => t*b) t y htlo hthi
    (by simp) h5 hsep
  simp only [Finset.biUnion_empty,Finset.empty_union,Finset.sum_empty,sub_zero] at hf
  have hang := angular_family_lower I hb hsmall hhb hL
    (fun v hv => ⟨(hg v hv).1,(hg v hv).2.2.1⟩)
  let F := (Real.exp (-(t+h)/2)*t^N/N.factorial)*
    max 0 (-Real.cos (y*t)-|y| * h)*h
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hbnd := mul_le_mul_of_nonneg_right hang hF
  rw [Finset.sum_mul] at hbnd
  have hnorm : ((996/1000 : ℝ)*(∫ x in ⋃ v ∈ I, cell (gridLo a b v) b,
      density (L/t) x)-1/100000)*F ≤
      ∑ v ∈ I, cellCredit N L t h y (fun i => t*gridLo a b v i) (fun _ => t*b) := by
    simpa only [cellCredit_normalized ht,F] using hbnd
  dsimp [F] at hnorm
  linarith

end
end RiemannGaussian.ZetaRieszFiveInteriorBudget
