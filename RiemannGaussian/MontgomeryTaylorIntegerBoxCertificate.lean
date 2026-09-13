/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorIntegerCoordinates
import RiemannGaussian.MontgomeryTaylorBoxCertificate
import RiemannGaussian.MontgomeryTaylorFastCurvature
import RiemannGaussian.CertifiedIntegerRangeTree

/-!
# Integer checks for continuous seven-point boxes

All per-box comparisons and costs use integers. The real interpretation
retains the same pair terms, signed gradients and complete curvature matrix.
This verifier does not assert that the full cover has passed.
-/

namespace RiemannGaussian.MontgomeryTaylorIntegerBoxCertificate
open MontgomeryTaylorIntegerCoordinates MontgomeryTaylorSevenWindowForms
open MontgomeryTaylorSevenWindowModel MontgomeryTaylorSevenWindowParameters
open MontgomeryTaylorNumericalKernel (kernel squaredDD)
open MontgomeryTaylorRangeTable
open scoped BigOperators

/-- The common real coordinate used by all integer interval endpoints. -/
noncomputable def real (n : ℤ) : ℝ := (rational n : ℝ)

/-- Both real coordinate implementations agree exactly. -/
theorem real_eq (n : ℤ) : real n = CertifiedIntegerRangeTree.coordinate denominator n := by
  simp only [real, rational, CertifiedIntegerRangeTree.coordinate,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]

/-- Positive scaling preserves the exact integer order. -/
theorem real_le (a b : ℤ) : real a ≤ real b ↔ a ≤ b := by
  simp only [real_eq]
  exact CertifiedIntegerRangeTree.coordinate_le (by decide : 0 < denominator) a b

/-- Integer cuts with paired squared-value and signed-curvature bounds. -/
abbrev Table := CertifiedIntegerRangeTree.Tree (ℤ × ℤ)

/-- Every cached bound has its continuous analytic interpretation. -/
def TableValid (table : Table) (l r : ℤ) : Prop :=
  CertifiedIntegerRangeTree.Valid denominator realBounds
    (fun x => (kernel x ^ 2, squaredDD x)) table l r

/-- Integer queries retain the complete continuous pair of bounds. -/
theorem query_sound {table : Table} {l r a b : ℤ} (ht : TableValid table l r)
    {x : ℝ} (hx : x ∈ Set.Icc (real l) (real r))
    (hq : x ∈ Set.Icc (real a) (real b)) :
    realBounds (CertifiedIntegerRangeTree.query table l r a b) ≤
      (kernel x ^ 2, squaredDD x) := by
  exact CertifiedIntegerRangeTree.query_sound (by decide : 0 < denominator)
    realBounds realBounds_monotone table ht
    (by simpa only [real_eq] using hx) (by simpa only [real_eq] using hq)

/-- Outside the table, retain the universal squared-value lower bound zero. -/
def valueQuery (table : Table) (l r a b : ℤ) : ℤ :=
  if l ≤ a ∧ b ≤ r then (CertifiedIntegerRangeTree.query table l r a b).1 else 0

/-- Every integer value query bounds the true squared kernel. -/
theorem valueQuery_le {table : Table} {l r a b : ℤ} (ht : TableValid table l r)
    {x : ℝ} (hx : x ∈ Set.Icc (real a) (real b)) :
    (valueQuery table l r a b : ℝ) / boundScale ≤ kernel x ^ 2 := by
  unfold valueQuery
  split_ifs with hab
  · exact (query_sound ht
      ⟨((real_le l a).mpr hab.1).trans hx.1, hx.2.trans ((real_le b r).mpr hab.2)⟩ hx).1
  · simpa only [Int.cast_zero, zero_div] using sq_nonneg (kernel x)

/-- Six integer closed coordinate intervals. -/
abbrev Box := Fin 6 → ℤ × ℤ

/-- Lower gap endpoints. -/
def lower (B : Box) (j : Fin 6) : ℤ := (B j).1

/-- Upper gap endpoints. -/
def upper (B : Box) (j : Fin 6) : ℤ := (B j).2

/-- Membership includes all real points between the exact endpoints. -/
def Mem (x : Fin 6 → ℝ) (B : Box) : Prop :=
  ∀ j, x j ∈ Set.Icc (real (lower B j)) (real (upper B j))

/-- Explicit integer pair sums enclose every real pair separation in a box. -/
theorem separation_mem {B : Box} {x : Fin 6 → ℝ} (hx : Mem x B) (t : Fin 19) :
    linearForm t x ∈ Set.Icc (real (separations (lower B) t))
      (real (separations (upper B) t)) := by
  simpa only [real, separations_cast, ← linearFormRat_cast] using
    linearForm_mem_box t (fun j => rational (lower B j)) (fun j => rational (upper B j)) hx

/-- Exact integer comparison for the entire interval floor. -/
def checkInterval (table : Table) (l r : ℤ) (B : Box) : Bool :=
  decide (3950020 * (denominator : ℤ) * boundScale ≤
    intervalNumerator (lower B) (fun t => valueQuery table l r
      (separations (lower B) t) (separations (upper B) t)))

/-- An accepted interval leaf proves the complete real model floor. -/
theorem checkInterval_sound {table : Table} {l r : ℤ} (ht : TableValid table l r)
    {B : Box} (hc : checkInterval table l r B = true)
    {x : Fin 6 → ℝ} (hx : Mem x B) : modelFloor ≤ finiteModel x := by
  let v := fun t => valueQuery table l r (separations (lower B) t) (separations (upper B) t)
  have hv (t : Fin 19) : (((v t : ℚ) / boundScale : ℚ) : ℝ) ≤
      kernel (linearForm t x) ^ 2 := by
    simpa only [v, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
      valueQuery_le ht (separation_mem hx t)
  have hb := intervalLower_le (fun j => rational (lower B j))
    (fun t => (v t : ℚ) / boundScale) x hv (fun j => (hx j).1)
  simp only [checkInterval, decide_eq_true_eq] at hc
  have hi : (3950020 : ℝ) * denominator * boundScale ≤ intervalNumerator (lower B) v := by
    exact_mod_cast hc
  have hpos : (0 : ℝ) < 1000000000 * denominator * boundScale := by
    norm_num [denominator, boundScale]
  have htar := div_le_div_of_nonneg_right hi (le_of_lt hpos)
  rw [intervalNumerator_cast] at htar
  have heq : (3950020 : ℝ) * denominator * boundScale /
      (1000000000 * denominator * boundScale) = modelFloor := by
    norm_num [modelFloor, denominator, boundScale]
  rw [heq] at htar
  rw [finiteModel_eq_objective]
  exact htar.trans hb

/-- Exact integer cache for one independently verified anchor. -/
structure Anchor where
  /-- Catalogue entry whose proved bounds this cache reproduces. -/
  sourceIndex : ℕ
  /-- Exact gap numerators. -/
  point : Fin 6 → ℤ
  /-- Complete value lower bound, scaled by the common bound scale. -/
  value : ℤ
  /-- Complete signed gradient lower bounds at that scale. -/
  lower : Fin 6 → ℤ
  /-- Complete signed gradient upper bounds at that scale. -/
  upper : Fin 6 → ℤ

/-- Decode an integer cache into the independently proved rational interface. -/
def Anchor.decode (a : Anchor) : MontgomeryTaylorAnchorBounds.Anchor :=
  ⟨fun j => rational (a.point j), (a.value : ℚ) / boundScale,
    fun j => (a.lower j : ℚ) / boundScale, fun j => (a.upper j : ℚ) / boundScale⟩

/-- One-time exact field comparison with a previously certified anchor. -/
def checkCache (old : ℕ → Option MontgomeryTaylorAnchorBounds.Anchor) (a : Anchor) : Bool :=
  match old a.sourceIndex with
  | none => false
  | some b => decide ((∀ j, a.decode.point j = b.point j) ∧ a.decode.value = b.value ∧
      (∀ j, a.decode.lower j = b.lower j) ∧ (∀ j, a.decode.upper j = b.upper j))

/-- Exact integer-cache comparisons transport the existing real proof. -/
theorem checkCache_sound (old : ℕ → Option MontgomeryTaylorAnchorBounds.Anchor)
    (hold : ∀ i b, old i = some b → MontgomeryTaylorAnchorBounds.Valid b)
    {a : Anchor} (hc : checkCache old a = true) : MontgomeryTaylorAnchorBounds.Valid a.decode := by
  cases hb : old a.sourceIndex with
  | none => simp only [checkCache, hb, Bool.false_eq_true] at hc
  | some b =>
    simp only [checkCache, hb, decide_eq_true_eq] at hc
    have hp := funext hc.1
    have hl := funext hc.2.2.1
    have hu := funext hc.2.2.2
    simpa only [MontgomeryTaylorAnchorBounds.Valid, hp, hc.2.1, hl, hu] using
      hold a.sourceIndex b hb

/-- Short block indexing keeps integer-anchor lookup independent of catalogue length. -/
def catalogueLookup (blocks : List (List Anchor)) (i : ℕ) : Option Anchor :=
  (blocks[i / 32]?.getD [])[i % 32]?

/-- A successful lookup returns one of the proved integer caches. -/
theorem catalogueLookup_valid (blocks : List (List Anchor))
    (hblocks : ∀ block ∈ blocks, ∀ a ∈ block, MontgomeryTaylorAnchorBounds.Valid a.decode)
    {i : ℕ} {a : Anchor} (h : catalogueLookup blocks i = some a) :
    MontgomeryTaylorAnchorBounds.Valid a.decode := by
  unfold catalogueLookup at h
  cases hb : blocks[i / 32]? with
  | none =>
    simp only [hb, Option.getD_none, List.getElem?_nil] at h
    cases h
  | some block =>
    simp only [hb, Option.getD_some] at h
    exact hblocks block (List.mem_of_getElem? hb) a (List.mem_of_getElem? h)

/-- The common hull retains both the box and the exact anchor. -/
def hull (B : Box) (a : Anchor) : Box :=
  fun j => (min (lower B j) (a.point j), max (upper B j) (a.point j))

/-- Every point of the original box is in the hull. -/
theorem mem_hull {B : Box} {x : Fin 6 → ℝ} (hx : Mem x B) (a : Anchor) :
    Mem x (hull B a) := by
  intro j
  exact ⟨((real_le _ _).mpr (min_le_left _ _)).trans (hx j).1,
    (hx j).2.trans ((real_le _ _).mpr (le_max_left _ _))⟩

/-- The exact anchor is in that same hull. -/
theorem anchor_mem_hull (B : Box) (a : Anchor) : Mem (fun j => real (a.point j)) (hull B a) := by
  intro j
  exact ⟨(real_le _ _).mpr (min_le_right _ _), (real_le _ _).mpr (le_max_right _ _)⟩

/-- Signed curvatures and a full integer factor for their matrix. -/
abbrev CurvatureWitness := MontgomeryTaylorBoxCertificate.CurvatureWitness

/-- Domain, signed-curvature, full-matrix and affine-support integer checks. -/
def checkAnchor (table : Table) (l r : ℤ) (B : Box) (a : Anchor)
    (w : CurvatureWitness) : Bool :=
  decide (∀ t : Fin 19,
    (10000000 : ℤ) ≤ separations (lower (hull B a)) t ∧
      l ≤ separations (lower (hull B a)) t ∧
      separations (upper (hull B a)) t ≤ r ∧
      w.curvature t ≤ (CertifiedIntegerRangeTree.query table l r
        (separations (lower (hull B a)) t) (separations (upper (hull B a)) t)).2) &&
  MontgomeryTaylorFastCurvature.check w.curvature w.factor &&
  decide (395002 * (boundScale : ℤ) * denominator ≤
    100000000 * tangentNumerator a.value a.point (lower B) (upper B) a.lower a.upper)

/-- Accepted integer anchor data control the whole continuous box, keeping
the coupled signed gradient and curvature through the final comparison. -/
theorem checkAnchor_sound {table : Table} {l r : ℤ} (ht : TableValid table l r)
    {B : Box} {a : Anchor} (ha : MontgomeryTaylorAnchorBounds.Valid a.decode)
    {w : CurvatureWitness} (hc : checkAnchor table l r B a w = true)
    {x : Fin 6 → ℝ} (hx : Mem x B) : modelFloor ≤ finiteModel x := by
  simp only [checkAnchor, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hlo (t : Fin 19) : (1 : ℝ) / 3 ≤ real (separations (lower (hull B a)) t) := by
    have he : real 10000000 = (1 : ℝ) / 3 := by norm_num [real, rational, denominator]
    rw [← he]
    exact (real_le _ _).mpr (hc.1.1 t).1
  have hdd (t : Fin 19) (z : ℝ)
      (hz : z ∈ Set.Icc (real (separations (lower (hull B a)) t))
        (real (separations (upper (hull B a)) t))) :
      (w.curvature t : ℝ) / boundScale ≤ squaredDD z := by
    have hz' : z ∈ Set.Icc (real l) (real r) :=
      ⟨((real_le _ _).mpr (hc.1.1 t).2.1).trans hz.1,
        hz.2.trans ((real_le _ _).mpr (hc.1.1 t).2.2.1)⟩
    have hb := (query_sound ht hz' hz).2
    have hd : (w.curvature t : ℝ) ≤
        ((CertifiedIntegerRangeTree.query table l r
          (separations (lower (hull B a)) t) (separations (upper (hull B a)) t)).2 : ℝ) := by
      exact_mod_cast (hc.1.1 t).2.2.2
    exact (div_le_div_of_nonneg_right hd (Nat.cast_nonneg boundScale)).trans hb
  have htangent := objective_tangent_lower (fun j => real (a.point j)) x
    (fun t => (w.curvature t : ℝ) / boundScale)
    (fun t => real (separations (lower (hull B a)) t))
    (fun t => real (separations (upper (hull B a)) t)) hlo
    (fun t => separation_mem (anchor_mem_hull B a) t)
    (fun t => separation_mem (mem_hull hx a) t) hdd
    (MontgomeryTaylorFastCurvature.check_sound hc.1.2)
  have hb := MontgomeryTaylorAnchorBounds.box_tangent_lower ha
    (fun j => rational (lower B j)) (fun j => rational (upper B j)) x hx
  have hi : (395002 : ℝ) * boundScale * denominator ≤
      100000000 * tangentNumerator a.value a.point (lower B) (upper B) a.lower a.upper := by
    exact_mod_cast hc.2
  have hpos : (0 : ℝ) < (boundScale : ℝ) * denominator := by norm_num [boundScale, denominator]
  have hnum : modelFloor ≤
      (tangentNumerator a.value a.point (lower B) (upper B) a.lower a.upper : ℝ) /
        ((boundScale : ℝ) * denominator) := by
    apply (le_div_iff₀ hpos).mpr
    norm_num only [modelFloor] at *
    nlinarith
  rw [tangentNumerator_cast] at hnum
  rw [finiteModel_eq_objective]
  exact hnum.trans (hb.trans htangent)

end RiemannGaussian.MontgomeryTaylorIntegerBoxCertificate
