/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCapacityCheck
import RiemannGaussian.ZetaRieszCapacityCover
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Whole-cell upper certificates for the adverse four-prime density

The density is exactly the ordered cap integral already used in the
four/five population test. No arithmetic carrier is redefined. Empty and
zero-cap cells are proved zero, normal cells use the checked cap integral,
and coarse cells use the independent second-smallest-share bound.
-/

namespace RiemannGaussian.ZetaRieszFourCapacityCover
open MeasureTheory ZetaRieszCapacityCover ZetaRieszOrderedCapacity
open scoped BigOperators

/-- The ordered four-prime angular density, with the least share integrated
over its exact ordering interval. An empty interval contributes zero. -/
noncomputable def density (lam : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  let S := 1-x 0-x 1
  (∫ r in Set.Ioc (max 0 (S-x 1)) (S/2),
    min r (max 0 (min (lam-x 0) (min (1-lam-x 1) (1+x 0-2*lam))))/(r*(S-r))) /
      (lam*x 0*x 1)

/-- The exact moving-fibre density is measurable, including its empty
cells. No smoothness across a clipping boundary is assumed. -/
theorem measurable_density (lam : ℝ) : Measurable (density lam) := by
  classical
  let g : ((Fin 2 → ℝ) × ℝ) → ℝ := fun v =>
    min v.2 (max 0 (min (lam-v.1 0) (min (1-lam-v.1 1) (1+v.1 0-2*lam)))) /
      (v.2*(1-v.1 0-v.1 1-v.2))
  let E : Set ((Fin 2 → ℝ) × ℝ) :=
    {v | max 0 (1-v.1 0-v.1 1-v.1 1) < v.2 ∧ v.2 ≤ (1-v.1 0-v.1 1)/2}
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hE : MeasurableSet E := by
    have hl : MeasurableSet {v : ((Fin 2 → ℝ) × ℝ) |
        max 0 (1-v.1 0-v.1 1-v.1 1) < v.2} :=
      measurableSet_lt (by fun_prop) measurable_snd
    have hu : MeasurableSet {v : ((Fin 2 → ℝ) × ℝ) |
        v.2 ≤ (1-v.1 0-v.1 1)/2} :=
      measurableSet_le measurable_snd (by fun_prop)
    exact hl.inter hu
  have hi : Measurable (fun x : Fin 2 → ℝ => ∫ r : ℝ, E.indicator g (x,r)) :=
    ((hg.indicator hE).stronglyMeasurable.integral_prod_right').measurable
  have he (x : Fin 2 → ℝ) :
      (∫ r : ℝ, E.indicator g (x,r)) =
      ∫ r in Set.Ioc (max 0 (1-x 0-x 1-x 1)) ((1-x 0-x 1)/2), g (x,r) := by
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  have hd : density lam = fun x : Fin 2 → ℝ =>
      (∫ r : ℝ, E.indicator g (x,r))/(lam*x 0*x 1) := by
    funext x
    rw [he]
    rfl
  rw [hd]
  exact hi.div (by fun_prop)

/-- Every numerical cell retains the elementary positive denominators and
the largest-share upper bound needed for the coarse-cell estimate. -/
def valid (lo hi P : ℚ) (B : Box) : Prop :=
  0 < lo ∧ lo ≤ hi ∧ P < lo ∧
  0 < (B 0).1 ∧ (B 0).1 ≤ (B 0).2 ∧ (B 0).2 ≤ P ∧
  0 < (B 1).1 ∧ (B 1).1 ≤ (B 1).2 ∧ (B 0).2+(B 1).2 < 1

instance (lo hi P : ℚ) (B : Box) : Decidable (valid lo hi P B) := by
  unfold valid
  infer_instance

/-- Cap-integral parameters enclosing every fibre of an outer cell. -/
def cap (lo hi : ℚ) (B : Box) (upper : ℚ) : ZetaRieszCapacityCheck.Cap :=
  let Slo := 1-(B 0).2-(B 1).2
  let Shi := 1-(B 0).1-(B 1).1
  ⟨max 0 (Slo-(B 1).2),Shi/2,Slo,
    max 0 (min (hi-(B 0).1) (min (1-lo-(B 1).1) (1+(B 0).2-2*lo))),
    -1,upper*lo*(B 0).1*(B 1).1⟩

/-- The branch choices are exact rational tests. Only a whole-cell cap
enclosure can accept the normal branch. -/
def check (lo hi P : ℚ) (B : Box) (w : ℚ × ℚ) : Bool :=
  decide (valid lo hi P B ∧ w.1 = 0 ∧ 0 ≤ w.2) &&
  let c := cap lo hi B w.2
  if c.height ≤ 0 ∨ c.b ≤ c.a then true
  else if c.b < c.total then ZetaRieszCapacityCheck.check c
  else decide (2*c.b ≤ w.2*(lo-P)*lo*(B 0).1*(B 1).1)

private theorem fibre_eq {lam p q : ℝ} (h : max 0 (1-p-q-q) ≤ (1-p-q)/2) :
    density lam ![p,q] =
      (∫ r : ℝ in max 0 (1-p-q-q)..((1-p-q)/2),
        min r (max 0 (min (lam-p) (min (1-lam-q) (1+p-2*lam))))/
          (r*(1-p-q-r)))/(lam*p*q) := by
  simp only [density,Matrix.cons_val_zero,Matrix.cons_val_one,
    intervalIntegral.integral_of_le h]

private theorem fibre_nonneg {a b S m : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbS : b < S) (hm : 0 ≤ m) :
    0 ≤ ∫ r : ℝ in a..b, min r m/(r*(S-r)) := by
  apply intervalIntegral.integral_nonneg hab
  intro r hr
  exact div_nonneg (le_min (ha.trans hr.1) hm)
    (mul_nonneg (ha.trans hr.1) (by linarith [hr.2]))

/-- All elementary endpoint comparisons used by the cap enclosure are
valid throughout the closed cell and the entire cutoff bin. -/
theorem parameters {lo hi P : ℚ} {B : Box} (hv : valid lo hi P B)
    {lam p q : ℝ} (hlam : (lo : ℝ) ≤ lam ∧ lam ≤ hi)
    (hp : (B 0).1 ≤ p ∧ p ≤ (B 0).2) (hq : (B 1).1 ≤ q ∧ q ≤ (B 1).2)
    (upper : ℚ) :
    let c := cap lo hi B upper
    0 < lam ∧ 0 < p ∧ 0 < q ∧ p ≤ (P : ℝ) ∧ 0 < 1-p-q ∧
    (c.a : ℝ) ≤ max 0 (1-p-q-q) ∧ (1-p-q)/2 ≤ (c.b : ℝ) ∧
    (c.total : ℝ) ≤ 1-p-q ∧
    max 0 (min (lam-p) (min (1-lam-q) (1+p-2*lam))) ≤ (c.height : ℝ) := by
  have hl : (0 : ℝ) < lo := by exact_mod_cast hv.1
  have hp0 : (0 : ℝ) < (B 0).1 := by exact_mod_cast hv.2.2.2.1
  have hph : ((B 0).2 : ℝ) ≤ P := by exact_mod_cast hv.2.2.2.2.2.1
  have hq0 : (0 : ℝ) < (B 1).1 := by exact_mod_cast hv.2.2.2.2.2.2.1
  have hsum : ((B 0).2 : ℝ)+(B 1).2 < 1 := by exact_mod_cast hv.2.2.2.2.2.2.2.2
  dsimp only
  simp only [cap,Rat.cast_max,Rat.cast_min,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,
    Rat.cast_div,Rat.cast_ofNat,Rat.cast_zero,Rat.cast_one]
  refine ⟨hl.trans_le hlam.1,hp0.trans_le hp.1,hq0.trans_le hq.1,hp.2.trans hph,
    by linarith [hp.2,hq.2],?_,by linarith [hp.1,hq.1],by linarith [hp.2,hq.2],?_⟩
  · exact max_le_max le_rfl (by linarith [hp.2,hq.2])
  · apply max_le_max le_rfl
    exact min_le_min (by linarith [hlam.2,hp.1])
      (min_le_min (by linarith [hlam.1,hq.1]) (by linarith [hlam.1,hp.2]))

/-- An accepted leaf controls the full four-prime density throughout its
closed outer cell and for every cutoff in the specified bin. -/
theorem check_sound {lo hi P : ℚ} {B : Box} {w : ℚ × ℚ}
    (hc : check lo hi P B w = true) {lam : ℝ}
    (hlam : (lo : ℝ) ≤ lam ∧ lam ≤ hi) {x : Fin 2 → ℝ}
    (hx : CertifiedBoxCover.Mem x B) :
    (w.1 : ℝ) ≤ density lam x ∧ density lam x ≤ (w.2 : ℝ) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hv,hw₁,hw₂⟩ := hc.1
  have hw : (0 : ℝ) ≤ w.2 := by exact_mod_cast hw₂
  let p := x 0
  let q := x 1
  have hxe : x = ![p,q] := by ext i; fin_cases i <;> rfl
  have hp := hx 0
  have hq := hx 1
  change (B 0).1 ≤ p ∧ p ≤ (B 0).2 at hp
  change (B 1).1 ≤ q ∧ q ≤ (B 1).2 at hq
  let c := cap lo hi B w.2
  have hnum := hc.2
  change (if c.height ≤ 0 ∨ c.b ≤ c.a then true
    else if c.b < c.total then ZetaRieszCapacityCheck.check c
    else decide (2*c.b ≤ w.2*(lo-P)*lo*(B 0).1*(B 1).1)) = true at hnum
  obtain ⟨hL,hp0,hq0,hpP,hS,ha,hb,hSl,hm⟩ := parameters hv hlam hp hq w.2
  change (c.a : ℝ) ≤ _ at ha
  change _ ≤ (c.b : ℝ) at hb
  change (c.total : ℝ) ≤ _ at hSl
  change _ ≤ (c.height : ℝ) at hm
  let a := max 0 (1-p-q-q)
  let b := (1-p-q)/2
  let m := max 0 (min (lam-p) (min (1-lam-q) (1+p-2*lam)))
  change (c.a : ℝ) ≤ a at ha
  change b ≤ (c.b : ℝ) at hb
  have ha0 : 0 ≤ a := le_max_left _ _
  have hm0 : 0 ≤ m := le_max_left _ _
  have hbS : b < 1-p-q := by dsimp [b]; linarith
  have hden : 0 < lam*p*q := mul_pos (mul_pos hL hp0) hq0
  rw [hw₁,Rat.cast_zero,hxe]
  by_cases hab : a ≤ b
  · rw [fibre_eq hab]
    change 0 ≤ (∫ r : ℝ in a..b, min r m/(r*(1-p-q-r)))/(lam*p*q) ∧ _
    have hi0 := fibre_nonneg ha0 hab hbS hm0
    refine ⟨div_nonneg hi0 hden.le,(div_le_iff₀ hden).mpr ?_⟩
    have hprod : (lo : ℝ)*(B 0).1*(B 1).1 ≤ lam*p*q := by
      have hpl : (0 : ℝ) ≤ (B 0).1 := by exact_mod_cast hv.2.2.2.1.le
      have hql : (0 : ℝ) ≤ (B 1).1 := by exact_mod_cast hv.2.2.2.2.2.2.1.le
      exact mul_le_mul (mul_le_mul hlam.1 hp.1 hpl hL.le) hq.1 hql
        (mul_nonneg hL.le hp0.le)
    have hec : (c.upper : ℝ) = (w.2 : ℝ)*((lo : ℝ)*(B 0).1*(B 1).1) := by
      simp [c,cap]
      ring
    have hpay : (c.upper : ℝ) ≤ (w.2 : ℝ)*(lam*p*q) := by
      rw [hec]
      exact mul_le_mul_of_nonneg_left hprod hw
    by_cases hz : c.height ≤ 0 ∨ c.b ≤ c.a
    · have hzero : (∫ r : ℝ in a..b, min r m/(r*(1-p-q-r))) = 0 := by
        rcases hz with hmz | hbaz
        · have hmz' : (c.height : ℝ) ≤ 0 := by exact_mod_cast hmz
          have hm' : m = 0 := le_antisymm (hm.trans hmz') hm0
          calc
            _ = ∫ _r : ℝ in a..b, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro r hr
              rw [Set.uIcc_of_le hab] at hr
              simp only [hm',min_eq_right (ha0.trans hr.1),zero_div]
            _ = 0 := by simp
        · have hba : (c.b : ℝ) ≤ c.a := by exact_mod_cast hbaz
          have hab' : a = b := le_antisymm hab (hb.trans (hba.trans ha))
          simp [hab']
      rw [hzero]
      positivity
    · by_cases hnormal : c.b < c.total
      · have hc' : ZetaRieszCapacityCheck.check c = true := by simpa [hz,hnormal] using hnum
        exact (ZetaRieszCapacityCheck.integral_le_of_check hc' ha hab hb hSl hm0 hm).trans hpay
      · have hcoarse : 2*c.b ≤ w.2*(lo-P)*lo*(B 0).1*(B 1).1 := by
          simpa [hz,hnormal] using hnum
        have hgap : (0 : ℝ) < lo-P := by exact_mod_cast (sub_pos.mpr hv.2.2.1)
        have hI : (∫ r : ℝ in a..b, min r m/(r*(1-p-q-r))) ≤
            (b-a)*(2/((lo : ℝ)-P)) := by
          calc
            _ ≤ ∫ _r : ℝ in a..b, 2/((lo : ℝ)-P) := by
              apply intervalIntegral.integral_mono_on hab
                (cap_integrable_nonneg ha0 hab hbS hm0) intervalIntegrable_const
              intro r hr
              rcases (ha0.trans hr.1).eq_or_lt with hr0 | hr0
              · rw [← hr0]
                simp only [zero_mul,div_zero]
                positivity
              · exact four_cap_density_le hr0 (by dsimp [b] at hr; linarith [hr.2])
                  hpP (by exact_mod_cast hv.2.2.1) hlam.1
            _ = _ := by rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]
        have hC : (2 : ℝ)*(c.b : ℝ) ≤
            (w.2 : ℝ)*((lo : ℝ)-P)*lo*(B 0).1*(B 1).1 := by exact_mod_cast hcoarse
        have hend : (c.b : ℝ)*(2/((lo : ℝ)-P)) ≤ (c.upper : ℝ) := by
          rw [hec,← mul_div_assoc]
          apply (div_le_iff₀ hgap).mpr
          nlinarith only [hC]
        exact (hI.trans ((mul_le_mul_of_nonneg_right
          (show b-a ≤ (c.b : ℝ) by linarith) (by positivity)).trans hend)).trans hpay
  · have he : Set.Ioc a b = ∅ := Set.Ioc_eq_empty_of_le (le_of_lt (lt_of_not_ge hab))
    change 0 ≤ (∫ r in Set.Ioc a b, _)/_ ∧ (∫ r in Set.Ioc a b, _)/_ ≤ (w.2 : ℝ)
    rw [he,setIntegral_empty,zero_div]
    exact ⟨le_rfl,hw⟩

/-- A complete accepted numerical cover supplies a uniform bound for the
whole four-prime angular integral. Measurability, integrability, every fibre
enclosure and every subdivision are discharged; only the explicit finite
checker results remain to be computed. -/
theorem integral_le_of_checked_cover {lo hi P upper : ℚ} (tree : Tree) {B : Box}
    (hB : ∀ i, (B i).1 ≤ (B i).2)
    (hc : ZetaRieszCapacityCover.check (check lo hi P) tree B = true)
    (ht : decide ((totals tree B).2 ≤ upper) = true)
    {lam : ℝ} (hlam : (lo : ℝ) ≤ lam ∧ lam ≤ hi) :
    (∫ x in region B, density lam x) ≤ (upper : ℝ) := by
  have hl : ∀ B w, check lo hi P B w = true →
      ∀ x ∈ region B, (w.1 : ℝ) ≤ density lam x ∧ density lam x ≤ (w.2 : ℝ) := by
    intro B w hw x hx
    apply check_sound hw hlam
    intro i
    have hi := Set.mem_pi.mp hx i (Set.mem_univ i)
    exact ⟨hi.1.le,hi.2⟩
  have hint := integrableOn_of_check (density lam) (measurable_density lam)
    (check lo hi P) hl tree hc
  have hb := (integral_bounds_of_check (density lam) (check lo hi P) hl tree hB hint hc).2
  apply hb.trans
  simp only [decide_eq_true_eq] at ht
  exact_mod_cast ht

end RiemannGaussian.ZetaRieszFourCapacityCover
