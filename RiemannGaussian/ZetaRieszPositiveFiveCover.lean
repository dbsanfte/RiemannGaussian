/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveInterior
import RiemannGaussian.CertifiedBoxCover
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A checked complete upper debit for the positive-five interior

The three outer shares retain the translated least-prime cap. Checked
harmonic integrals are added over an exhaustive half-open box partition.
A leaf's first witness is a lower cap bound used in the subtraction; its
second witness bounds the resulting nonnegative density. No prime-count
or phase transfer is assumed by this integral certificate.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveCover.Cover
open MeasureTheory
open scoped BigOperators

/-- The largest, second-smallest and middle cofactor shares. -/
abbrev Box := CertifiedBoxCover.Box (Fin 3)

/-- Each leaf carries a cap-subtraction witness and an upper density bound. -/
abbrev Tree := CertifiedBoxCover.Tree (Fin 3) (ℚ × ℚ)

/-- Half-open integration cells give an exact disjoint subdivision. -/
def region (B : Box) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (B i).1 (B i).2)

/-- The signed rational area of a box; valid boxes have nonnegative area. -/
def area (B : Box) : ℚ := ∏ i, ((B i).2-(B i).1)

/-- Check every cut as well as every numerical leaf. -/
def check (leaf : Box → ℚ × ℚ → Bool) : Tree → Box → Bool
  | .leaf w, B => leaf B w
  | .split i q l r, B =>
    decide ((B i).1 ≤ q ∧ q ≤ (B i).2) &&
      check leaf l (CertifiedBoxCover.leftBox B i q) &&
      check leaf r (CertifiedBoxCover.rightBox B i q)

/-- Add the actual area-weighted leaf budgets, with no externally supplied
total and no dropped zero-valued children. -/
def totals : Tree → Box → ℚ × ℚ
  | .leaf w, B => (0,area B*w.2)
  | .split i q l r, B =>
    let L := totals l (CertifiedBoxCover.leftBox B i q)
    let R := totals r (CertifiedBoxCover.rightBox B i q)
    (L.1+R.1,L.2+R.2)

private theorem mem_region {B : Box} {x : Fin 3 → ℝ} :
    x ∈ region B ↔ ∀ i, (B i).1 < x i ∧ x i ≤ (B i).2 := by
  simp [region]

private theorem measurable_region (B : Box) : MeasurableSet (region B) :=
  (measurableSet_pi (Set.to_countable _)).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

private theorem volume_region_ne_top (B : Box) : volume (region B) ≠ ⊤ := by
  rw [region,Real.volume_pi_Ioc]
  exact ne_of_lt (ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top))

private theorem volume_region (B : Box) (hB : ∀ i, (B i).1 ≤ (B i).2) :
    volume.real (region B) = (area B : ℝ) := by
  change (volume (region B)).toReal = _
  rw [region,Real.volume_pi_Ioc_toReal (by
    intro i
    change ((B i).1 : ℝ) ≤ ((B i).2 : ℝ)
    exact_mod_cast hB i)]
  simp [area]

private theorem split_regions {B : Box} (i : Fin 3) {q : ℚ}
    (hq : (B i).1 ≤ q ∧ q ≤ (B i).2) :
    region B = region (CertifiedBoxCover.leftBox B i q) ∪
      region (CertifiedBoxCover.rightBox B i q) := by
  have hql : ((B i).1 : ℝ) ≤ q := by exact_mod_cast hq.1
  have hqu : (q : ℝ) ≤ (B i).2 := by exact_mod_cast hq.2
  ext x
  simp only [Set.mem_union,mem_region]
  constructor
  · intro hx
    by_cases hxi : x i ≤ (q : ℝ)
    · left
      intro j
      by_cases hj : j = i
      · subst j
        simpa [CertifiedBoxCover.leftBox] using And.intro (hx i).1 hxi
      · simpa [CertifiedBoxCover.leftBox,Function.update_of_ne hj] using hx j
    · right
      intro j
      by_cases hj : j = i
      · subst j
        simpa [CertifiedBoxCover.rightBox] using And.intro (lt_of_not_ge hxi) (hx i).2
      · simpa [CertifiedBoxCover.rightBox,Function.update_of_ne hj] using hx j
  · intro hx j
    rcases hx with hl | hr
    · by_cases hj : j = i
      · subst j
        have hi := hl i
        simp only [CertifiedBoxCover.leftBox,Function.update_self] at hi
        exact ⟨hi.1,hi.2.trans hqu⟩
      · simpa [CertifiedBoxCover.leftBox,Function.update_of_ne hj] using hl j
    · by_cases hj : j = i
      · subst j
        have hi := hr i
        simp only [CertifiedBoxCover.rightBox,Function.update_self] at hi
        exact ⟨hql.trans_lt hi.1,hi.2⟩
      · simpa [CertifiedBoxCover.rightBox,Function.update_of_ne hj] using hr j

private theorem split_disjoint (B : Box) (i : Fin 3) (q : ℚ) :
    Disjoint (region (CertifiedBoxCover.leftBox B i q))
      (region (CertifiedBoxCover.rightBox B i q)) := by
  apply Set.disjoint_left.mpr
  intro x hl hr
  have hleft := (mem_region.mp hl) i
  have hright := (mem_region.mp hr) i
  simp only [CertifiedBoxCover.leftBox,CertifiedBoxCover.rightBox,
    Function.update_self] at hleft hright
  exact (not_lt_of_ge hleft.2) hright.1

private theorem leaf_bounds {f : (Fin 3 → ℝ) → ℝ} {B : Box} {w : ℚ × ℚ}
    (hB : ∀ i, (B i).1 ≤ (B i).2) (hf : IntegrableOn f (region B))
    (hw : ∀ x ∈ region B, 0 ≤ f x ∧ f x ≤ (w.2 : ℝ)) :
    (0 : ℝ) ≤ (∫ x in region B, f x) ∧
      (∫ x in region B, f x) ≤ (area B*w.2 : ℚ) := by
  have hl : 0 ≤ ∫ x in region B, f x :=
    setIntegral_nonneg (measurable_region B) (fun x hx => (hw x hx).1)
  have hu := setIntegral_mono_on hf (integrableOn_const (volume_region_ne_top B))
    (measurable_region B) (fun x hx => (hw x hx).2)
  simpa only [setIntegral_const,volume_region B hB,smul_eq_mul,Rat.cast_mul] using And.intro hl hu

/-- Successful bounded leaves also discharge integrability on the whole
cover. Measurability suffices; no continuity across clipping faces is needed. -/
theorem integrableOn_of_check (f : (Fin 3 → ℝ) → ℝ) (hf : Measurable f)
    (leaf : Box → ℚ × ℚ → Bool)
    (hleaf : ∀ B w, leaf B w = true →
      ∀ x ∈ region B, 0 ≤ f x ∧ f x ≤ (w.2 : ℝ))
    (tree : Tree) {B : Box} (hc : check leaf tree B = true) :
    IntegrableOn f (region B) := by
  induction tree generalizing B with
  | leaf w =>
    apply Measure.integrableOn_of_bounded (M := |(w.2 : ℝ)|)
      (volume_region_ne_top B) hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurable_region B)] with x hx
    have hb := hleaf B w hc x hx
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · exact (neg_nonpos.mpr (abs_nonneg _)).trans hb.1
    · exact hb.2.trans (le_abs_self _)
  | split i q l r ihl ihr =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    rw [split_regions i hc.1.1]
    exact (ihl hc.1.2).union (ihr hc.2)

/-- A checked exhaustive tree proves a two-sided integral inequality on
the complete root. Leaf soundness is a pointwise numerical enclosure;
integrability is retained explicitly and no count/phase estimate is assumed. -/
theorem integral_bounds_of_check (f : (Fin 3 → ℝ) → ℝ)
    (leaf : Box → ℚ × ℚ → Bool)
    (hleaf : ∀ B w, leaf B w = true →
      ∀ x ∈ region B, 0 ≤ f x ∧ f x ≤ (w.2 : ℝ))
    (tree : Tree) {B : Box} (hB : ∀ i, (B i).1 ≤ (B i).2)
    (hf : IntegrableOn f (region B)) (hc : check leaf tree B = true) :
    ((totals tree B).1 : ℝ) ≤ (∫ x in region B, f x) ∧
      (∫ x in region B, f x) ≤ ((totals tree B).2 : ℝ) := by
  induction tree generalizing B with
  | leaf w => simpa only [totals,Rat.cast_zero] using leaf_bounds hB hf (hleaf B w hc)
  | split i q l r ihl ihr =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    have he := split_regions i hc.1.1
    have hlsub : region (CertifiedBoxCover.leftBox B i q) ⊆ region B :=
      he ▸ Set.subset_union_left
    have hrsub : region (CertifiedBoxCover.rightBox B i q) ⊆ region B :=
      he ▸ Set.subset_union_right
    have hBl : ∀ j, (CertifiedBoxCover.leftBox B i q j).1 ≤
        (CertifiedBoxCover.leftBox B i q j).2 := by
      intro j
      by_cases hj : j = i
      · subst j; simpa [CertifiedBoxCover.leftBox] using hc.1.1.1
      · simpa [CertifiedBoxCover.leftBox,Function.update_of_ne hj] using hB j
    have hBr : ∀ j, (CertifiedBoxCover.rightBox B i q j).1 ≤
        (CertifiedBoxCover.rightBox B i q j).2 := by
      intro j
      by_cases hj : j = i
      · subst j; simpa [CertifiedBoxCover.rightBox] using hc.1.1.2
      · simpa [CertifiedBoxCover.rightBox,Function.update_of_ne hj] using hB j
    have hl := ihl hBl (hf.mono_set hlsub) hc.1.2
    have hr := ihr hBr (hf.mono_set hrsub) hc.2
    have hi : (∫ x in region B, f x) =
        (∫ x in region (CertifiedBoxCover.leftBox B i q), f x)+
          ∫ x in region (CertifiedBoxCover.rightBox B i q), f x := by
      rw [he]
      exact setIntegral_union (split_disjoint B i q) (measurable_region _)
        (hf.mono_set hlsub) (hf.mono_set hrsub)
    simp only [totals,Rat.cast_add,hi]
    simpa using And.intro (add_le_add hl.1 hr.1) (add_le_add hl.2 hr.2)


end RiemannGaussian.ZetaRieszPositiveFiveCover.Cover

namespace RiemannGaussian.ZetaRieszPositiveFiveCover
noncomputable section
open MeasureTheory ZetaRieszPositiveFiveInterior ZetaRieszOrderedCapacity
open scoped BigOperators

/-- Exact positive-five density after integrating the least cofactor
share. The strict middle ordering makes the rejected half-open cells
empty, while the remaining second-largest share is retained in the
harmonic denominator. -/
def density (lam : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  if x 1 < x 2 then
    (∫ r in Set.Ioc 0 (min (x 1) (1-x 0-x 1-2*x 2)),
      max 0 (min (r-max 0 (max (lam-x 0-x 1) (2*lam-2*x 0-x 1-x 2)))
        (max 0 (min (lam-x 0) (1+2*x 0-3*lam)))) /
        (r*(1-x 0-x 1-x 2-r))) / (lam*x 0*x 1*x 2)
  else 0

/-- Measurability includes every ordering and clipping boundary. -/
theorem measurable_density (lam : ℝ) : Measurable (density lam) := by
  classical
  let g : ((Fin 3 → ℝ) × ℝ) → ℝ := fun v =>
    max 0 (min (v.2-max 0 (max (lam-v.1 0-v.1 1) (2*lam-2*v.1 0-v.1 1-v.1 2)))
      (max 0 (min (lam-v.1 0) (1+2*v.1 0-3*lam)))) /
        (v.2*(1-v.1 0-v.1 1-v.1 2-v.2))
  let E : Set ((Fin 3 → ℝ) × ℝ) :=
    {v | 0 < v.2 ∧ v.2 ≤ min (v.1 1) (1-v.1 0-v.1 1-2*v.1 2)}
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_snd
    · exact measurableSet_le measurable_snd (by fun_prop)
  have hi : Measurable (fun x : Fin 3 → ℝ => ∫ r : ℝ, E.indicator g (x,r)) :=
    ((hg.indicator hE).stronglyMeasurable.integral_prod_right').measurable
  have he (x : Fin 3 → ℝ) : (∫ r : ℝ, E.indicator g (x,r)) =
      ∫ r in Set.Ioc 0 (min (x 1) (1-x 0-x 1-2*x 2)), g (x,r) := by
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  have hd : density lam = fun x : Fin 3 → ℝ =>
      if x 1 < x 2 then (∫ r : ℝ, E.indicator g (x,r))/(lam*x 0*x 1*x 2) else 0 := by
    funext x
    rw [he]
    rfl
  rw [hd]
  exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
    (hi.div (by fun_prop)) measurable_const

/-- All geometric checks use rational arithmetic. -/
def valid (lo hi owner : ℚ) (B : Cover.Box) : Prop :=
  0 < lo ∧ lo ≤ hi ∧ owner < lo ∧
    (∀ i, 0 < (B i).1 ∧ (B i).1 ≤ (B i).2) ∧
    (B 0).2 ≤ owner ∧ (B 0).2+(B 1).2+(B 2).2 < 1

instance (lo hi owner : ℚ) (B : Cover.Box) : Decidable (valid lo hi owner B) := by
  unfold valid
  infer_instance

/-- Lower translated-cap offset over the complete outer cell. -/
def offset (lo : ℚ) (B : Cover.Box) : ℚ :=
  max 0 (max (lo-(B 0).2-(B 1).2) (2*lo-2*(B 0).2-(B 1).2-(B 2).2))

/-- Upper cap height and interval with the lower harmonic total. -/
def cap (lo hi : ℚ) (B : Cover.Box) (lower upper : ℚ) : ZetaRieszCapacityCheck.Cap :=
  let c := max 0 (min (hi-(B 0).1) (1+2*(B 0).2-3*lo))
  ⟨0,min (B 1).2 (1-(B 0).1-(B 1).1-2*(B 2).1),
    1-(B 0).2-(B 1).2-(B 2).2,offset lo B+c,
    -1,lower+upper*lo*(B 0).1*(B 1).1*(B 2).1⟩

/-- Two ordinary cap enclosures pay their difference before cubature.
The zero-offset branch needs just one cap enclosure. -/
def check (lo hi owner : ℚ) (B : Cover.Box) (w : ℚ × ℚ) : Bool :=
  decide (valid lo hi owner B ∧ 0 ≤ w.2) &&
  let r := offset lo B
  let c := cap lo hi B w.1 w.2
  if (B 2).2 ≤ (B 1).1 ∨ c.height ≤ r ∨ c.b ≤ r then true
  else if r = 0 then
    decide (w.1 = 0) && ZetaRieszCapacityCheck.check c
  else ZetaRieszCapacityCheck.check c &&
    ZetaRieszCapacityCheck.check {c with height := r,lower := w.1,upper := 1000000}

private theorem shifted_integrable {b S r c : ℝ} (hb : 0 ≤ b) (hbS : b < S)
    (hr : 0 ≤ r) (hc : 0 ≤ c) :
    IntervalIntegrable (fun x : ℝ => max 0 (min (x-r) c)/(x*(S-x))) volume 0 b := by
  have hbig := cap_integrable_nonneg le_rfl hb hbS (add_nonneg hr hc)
  have hsmall := cap_integrable_nonneg le_rfl hb hbS hr
  convert hbig.sub hsmall using 1
  funext x
  rw [shifted_cap_eq_cap_sub hc,sub_div]

private theorem shifted_integral_nonneg {b S r c : ℝ} (hb : 0 ≤ b) (hbS : b < S) :
    0 ≤ ∫ x : ℝ in 0..b, max 0 (min (x-r) c)/(x*(S-x)) := by
  apply intervalIntegral.integral_nonneg hb
  intro x hx
  exact div_nonneg (le_max_left _ _) (mul_nonneg hx.1 (by linarith [hx.2]))

/-- Parameter monotonicity retains the translated-cap subtraction. -/
theorem shifted_integral_mono {b B S T r R c C : ℝ}
    (hb : 0 ≤ b) (hbB : b ≤ B) (hBT : B < T) (hTS : T ≤ S)
    (hR : 0 ≤ R) (hRr : R ≤ r) (hc : 0 ≤ c) (hcC : c ≤ C) :
    (∫ x : ℝ in 0..b, max 0 (min (x-r) c)/(x*(S-x))) ≤
      ∫ x : ℝ in 0..B, max 0 (min (x-R) C)/(x*(T-x)) := by
  have hbT := hbB.trans_lt hBT
  apply (intervalIntegral.integral_mono_on hb
    (shifted_integrable hb (hbT.trans_le hTS) (hR.trans hRr) hc)
    (shifted_integrable hb hbT hR (hc.trans hcC)) ?_).trans
  · apply intervalIntegral.integral_mono_interval le_rfl hb hbB
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_nonneg (le_max_left _ _)
        (mul_nonneg hx.1.le (by linarith [hx.2]))
    · exact shifted_integrable (hb.trans hbB) hBT hR (hc.trans hcC)
  · intro x hx
    rcases hx.1.eq_or_lt with hzero | hpos
    · rw [← hzero]
      simp
    · apply div_le_div₀ (le_max_left _ _)
        (max_le_max le_rfl (min_le_min (by linarith) hcC))
        (mul_pos hpos (sub_pos.mpr (hx.2.trans_lt hbT)))
      exact mul_le_mul_of_nonneg_left (by linarith) hpos.le

private theorem parameters {lo hi owner : ℚ} {B : Cover.Box}
    (hv : valid lo hi owner B) {lam : ℝ} (hlam : (lo : ℝ) ≤ lam ∧ lam ≤ hi)
    {x : Fin 3 → ℝ} (hx : CertifiedBoxCover.Mem x B) (w : ℚ × ℚ) :
    let c := cap lo hi B w.1 w.2
    0 < lam ∧ 0 < x 0 ∧ 0 < x 1 ∧ 0 < x 2 ∧
    0 < 1-x 0-x 1-x 2 ∧
    min (x 1) (1-x 0-x 1-2*x 2) ≤ (c.b : ℝ) ∧
    (c.total : ℝ) ≤ 1-x 0-x 1-x 2 ∧
    (offset lo B : ℝ) ≤ max 0 (max (lam-x 0-x 1) (2*lam-2*x 0-x 1-x 2)) ∧
    max 0 (min (lam-x 0) (1+2*x 0-3*lam)) ≤ (c.height : ℝ)-offset lo B ∧
    (lo : ℝ)*(B 0).1*(B 1).1*(B 2).1 ≤ lam*x 0*x 1*x 2 := by
  obtain ⟨hlo,_,_,hB,_,hsum⟩ := hv
  have hl : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hlow (i : Fin 3) : (0 : ℝ) < (B i).1 := by exact_mod_cast (hB i).1
  have hpos (i : Fin 3) : 0 < x i := (hlow i).trans_le (hx i).1
  have hsum' : ((B 0).2 : ℝ)+(B 1).2+(B 2).2 < 1 := by exact_mod_cast hsum
  have hden := mul_le_mul
    (mul_le_mul (mul_le_mul hlam.1 (hx 0).1 (hlow 0).le (hl.trans_le hlam.1).le)
      (hx 1).1 (hlow 1).le (mul_nonneg (hl.trans_le hlam.1).le (hpos 0).le))
    (hx 2).1 (hlow 2).le
    (mul_nonneg (mul_nonneg (hl.trans_le hlam.1).le (hpos 0).le) (hpos 1).le)
  dsimp only
  refine ⟨hl.trans_le hlam.1,hpos 0,hpos 1,hpos 2,
    by linarith [(hx 0).2,(hx 1).2,(hx 2).2],?_,?_,?_,?_,hden⟩
  · simp only [cap,Rat.cast_min,Rat.cast_sub,Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat]
    exact min_le_min (hx 1).2 (by linarith [(hx 0).1,(hx 1).1,(hx 2).1])
  · simp only [cap,Rat.cast_sub,Rat.cast_one]
    linarith [(hx 0).2,(hx 1).2,(hx 2).2]
  · simp only [offset,Rat.cast_max,Rat.cast_sub,Rat.cast_mul,Rat.cast_zero,Rat.cast_ofNat]
    exact max_le_max le_rfl (max_le_max (by linarith [hlam.1,(hx 0).2,(hx 1).2])
      (by linarith [hlam.1,(hx 0).2,(hx 1).2,(hx 2).2]))
  · simp only [cap,Rat.cast_add,Rat.cast_max,Rat.cast_min,Rat.cast_sub,Rat.cast_mul,
      Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat,add_sub_cancel_left]
    exact max_le_max le_rfl (min_le_min (by linarith [hlam.2,(hx 0).1])
      (by linarith [hlam.1,(hx 0).2]))

private theorem cap_integral_le {lo hi owner : ℚ} {B : Cover.Box} {w : ℚ × ℚ}
    (hc : check lo hi owner B w = true)
    (hn : ¬ ((B 2).2 ≤ (B 1).1 ∨ (cap lo hi B w.1 w.2).height ≤ offset lo B ∨
      (cap lo hi B w.1 w.2).b ≤ offset lo B)) :
    let c := cap lo hi B w.1 w.2
    (c.b : ℝ) < c.total ∧
    (∫ r : ℝ in 0..(c.b : ℝ),
      max 0 (min (r-offset lo B) ((c.height : ℝ)-offset lo B))/(r*(c.total-r))) ≤
      (w.2 : ℝ)*((lo : ℝ)*(B 0).1*(B 1).1*(B 2).1) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hr : 0 ≤ offset lo B := le_max_left _ _
  let c := cap lo hi B w.1 w.2
  have hnum := hc.2
  change (if (B 2).2 ≤ (B 1).1 ∨ c.height ≤ offset lo B ∨ c.b ≤ offset lo B then true
    else if offset lo B = 0 then decide (w.1 = 0) && ZetaRieszCapacityCheck.check c
    else ZetaRieszCapacityCheck.check c &&
      ZetaRieszCapacityCheck.check {c with height := offset lo B,lower := w.1,upper := 1000000}) = true
    at hnum
  rw [if_neg hn] at hnum
  have hbig : ZetaRieszCapacityCheck.check c = true := by
    split_ifs at hnum with h
    · simp only [Bool.and_eq_true] at hnum
      exact hnum.2
    · simp only [Bool.and_eq_true] at hnum
      exact hnum.1
  have hg : 0 ≤ c.a ∧ c.a < c.b ∧ c.b < c.total ∧ 0 < c.height := by
    have h := hbig
    simp only [ZetaRieszCapacityCheck.check,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1
  refine ⟨by exact_mod_cast hg.2.2.1,?_⟩
  have hpay : (c.upper : ℝ)-(w.1 : ℝ) =
      (w.2 : ℝ)*((lo : ℝ)*(B 0).1*(B 1).1*(B 2).1) := by
    simp only [c,cap,Rat.cast_add,Rat.cast_mul]
    ring
  rw [← hpay]
  by_cases hr0 : offset lo B = 0
  · rw [if_pos hr0] at hnum
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hnum
    have hw0 : (w.1 : ℝ) = 0 := by exact_mod_cast hnum.1
    have hh : (0 : ℝ) ≤ c.height := by exact_mod_cast hg.2.2.2.le
    have hb : (0 : ℝ) ≤ c.b := by
      have : (0 : ℚ) < c.b := hg.2.1
      exact_mod_cast this.le
    have he : (offset lo B : ℝ) = 0 := by rw [hr0,Rat.cast_zero]
    rw [he,hw0,sub_zero]
    calc
      _ = ∫ r : ℝ in 0..(c.b : ℝ), min r (c.height : ℝ)/(r*(c.total-r)) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [Set.uIcc_of_le hb] at hr
        change max 0 (min (r-0) (c.height : ℝ))/(r*(c.total-r)) = _
        rw [sub_zero,max_eq_right (le_min hr.1 hh)]
      _ ≤ _ := by simpa only [c,cap,Rat.cast_zero,sub_zero] using
          (ZetaRieszCapacityCheck.check_sound hbig).2
  · rw [if_neg hr0] at hnum
    simp only [Bool.and_eq_true] at hnum
    have hs := hnum.2
    have hrc : offset lo B ≤ c.height := by
      dsimp [c,cap]
      exact le_add_of_nonneg_right (le_max_left _ _)
    simpa only [c,cap,Rat.cast_zero] using
      checked_shifted_cap_integral_le c (offset lo B) w.1 1000000 hbig hs hrc

/-- Each accepted leaf bounds the actual translated positive-five fibre
throughout its half-open outer cell. No point or ordering face is sampled. -/
theorem check_sound {lo hi owner : ℚ} {B : Cover.Box} {w : ℚ × ℚ}
    (hc : check lo hi owner B w = true) {lam : ℝ}
    (hlam : (lo : ℝ) ≤ lam ∧ lam ≤ hi) {x : Fin 3 → ℝ}
    (hx : x ∈ Cover.region B) :
    0 ≤ density lam x ∧ density lam x ≤ (w.2 : ℝ) := by
  have hc' := hc
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc'
  obtain ⟨hv,hwq⟩ := hc'.1
  have hw : (0 : ℝ) ≤ w.2 := by exact_mod_cast hwq
  have hclosed : CertifiedBoxCover.Mem x B := by
    intro i
    have hi := Set.mem_pi.mp hx i (Set.mem_univ i)
    exact ⟨hi.1.le,hi.2⟩
  obtain ⟨hl,hp,hb,ha,hQ,hR,hQt,hoff,hcap,hden⟩ := parameters hv hlam hclosed w
  let c := cap lo hi B w.1 w.2
  let R := min (x 1) (1-x 0-x 1-2*x 2)
  let Q := 1-x 0-x 1-x 2
  let r := max 0 (max (lam-x 0-x 1) (2*lam-2*x 0-x 1-x 2))
  let m := max 0 (min (lam-x 0) (1+2*x 0-3*lam))
  change R ≤ (c.b : ℝ) at hR
  change (c.total : ℝ) ≤ Q at hQt
  change (offset lo B : ℝ) ≤ r at hoff
  change m ≤ (c.height : ℝ)-offset lo B at hcap
  have hr : 0 ≤ r := le_max_left _ _
  have hm : 0 ≤ m := le_max_left _ _
  have hRQ : R < Q := by
    have h := min_le_right (x 1) (1-x 0-x 1-2*x 2)
    dsimp [R,Q]
    linarith
  have hd : 0 < lam*x 0*x 1*x 2 := mul_pos (mul_pos (mul_pos hl hp) hb) ha
  unfold density
  by_cases horder : x 1 < x 2
  · rw [if_pos horder]
    change 0 ≤ (∫ v in Set.Ioc 0 R, max 0 (min (v-r) m)/(v*(Q-v)))/_ ∧ _
    by_cases hR0 : 0 ≤ R
    · rw [← intervalIntegral.integral_of_le hR0]
      have hi0 := shifted_integral_nonneg (r := r) (c := m) hR0 hRQ
      refine ⟨div_nonneg hi0 hd.le,(div_le_iff₀ hd).mpr ?_⟩
      by_cases hz : (B 2).2 ≤ (B 1).1 ∨ c.height ≤ offset lo B ∨ c.b ≤ offset lo B
      · have hzero : (∫ v : ℝ in 0..R, max 0 (min (v-r) m)/(v*(Q-v))) = 0 := by
          rcases hz with hord | hheight | hend
          · have hord' : ((B 2).2 : ℝ) ≤ (B 1).1 := by exact_mod_cast hord
            exfalso
            linarith [(hclosed 2).2,(hclosed 1).1]
          · have hh : (c.height : ℝ) ≤ offset lo B := by exact_mod_cast hheight
            have hmz : m = 0 := le_antisymm (by linarith) hm
            simp only [hmz,max_eq_left (min_le_right _ _),zero_div,
              intervalIntegral.integral_zero]
          · have hh : (c.b : ℝ) ≤ offset lo B := by exact_mod_cast hend
            calc
              _ = ∫ _v : ℝ in 0..R, (0 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro v hv
                rw [Set.uIcc_of_le hR0] at hv
                have hvr : v-r ≤ 0 := by linarith [hv.2]
                dsimp only
                rw [max_eq_left ((min_le_left _ _).trans hvr),zero_div]
              _ = 0 := by simp
        rw [hzero]
        positivity
      · obtain ⟨hBT,hpay⟩ := cap_integral_le hc hz
        have hro : (0 : ℝ) ≤ offset lo B := by exact_mod_cast (le_max_left 0
          (max (lo-(B 0).2-(B 1).2) (2*lo-2*(B 0).2-(B 1).2-(B 2).2)))
        exact (shifted_integral_mono hR0 hR hBT hQt hro hoff hm hcap).trans
          (hpay.trans (mul_le_mul_of_nonneg_left hden hw))
    · have he : Set.Ioc (0 : ℝ) R = ∅ := Set.Ioc_eq_empty_of_le (le_of_not_ge hR0)
      rw [he,setIntegral_empty,zero_div]
      exact ⟨le_rfl,hw⟩
  · rw [if_neg horder]
    exact ⟨le_rfl,hw⟩

/-- An exhaustive accepted cover proves the complete positive-five
angular debit, with its integrability and all fibre enclosures discharged. -/
theorem integral_le_of_checked_cover {lo hi owner upper : ℚ} (tree : Cover.Tree)
    {B : Cover.Box} (hB : ∀ i, (B i).1 ≤ (B i).2)
    (hc : Cover.check (check lo hi owner) tree B = true)
    (ht : decide ((Cover.totals tree B).2 ≤ upper) = true)
    {lam : ℝ} (hlam : (lo : ℝ) ≤ lam ∧ lam ≤ hi) :
    (∫ x in Cover.region B, density lam x) ≤ (upper : ℝ) := by
  have hs : ∀ B w, check lo hi owner B w = true → ∀ x ∈ Cover.region B,
      0 ≤ density lam x ∧ density lam x ≤ (w.2 : ℝ) :=
    fun _ _ hw _ hx => check_sound hw hlam hx
  have hint := Cover.integrableOn_of_check (density lam) (measurable_density lam)
    (check lo hi owner) hs tree hc
  have hb := (Cover.integral_bounds_of_check (density lam) (check lo hi owner) hs tree hB hint hc).2
  apply hb.trans
  simp only [decide_eq_true_eq] at ht
  exact_mod_cast ht

end
end RiemannGaussian.ZetaRieszPositiveFiveCover
