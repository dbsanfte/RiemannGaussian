/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertificateData.MontgomeryTaylorPhaseCycle
import RiemannGaussian.MontgomeryTaylorAdaptiveCell
import RiemannGaussian.CertifiedRangeTree

/-!
# A continuous table for the kernel value and signed curvature

The leaves check both analytic bounds at once. Cached integer bounds permit
subsequent boxes to query complete pair-separation intervals without either
reevaluating trigonometric functions or scanning every grid cell.
-/

namespace RiemannGaussian.MontgomeryTaylorRangeTable
open LeanCert.Core MontgomeryTaylorNumericalKernel

/-- Common exact scale of the integer value and curvature bounds. -/
def boundScale : ℕ := 1099511627776

/-- Convert the two fixed-point integers to real lower bounds. -/
noncomputable def realBounds (b : ℤ × ℤ) : ℝ × ℝ :=
  ((b.1 : ℝ) / boundScale, (b.2 : ℝ) / boundScale)

/-- The fixed positive scale preserves the componentwise ordering. -/
theorem realBounds_monotone : Monotone realBounds := by
  intro a b hab
  constructor
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg boundScale)
    exact_mod_cast hab.1
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg boundScale)
    exact_mod_cast hab.2

/-- A dyadic enclosure of an arbitrary nonempty rational table cell. -/
def cell (l r : ℚ) (h : l ≤ r) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨l, r, h⟩ (-53)

/-- Check both proposed integer bounds on the entire continuous cell.
The phase lookup is already independently certified by the Lean kernel. -/
def leafCheck (l r : ℚ) (b : ℤ × ℤ) (n : ℕ) : Bool :=
  if h : l ≤ r then
    let cs := MontgomeryTaylorPhaseGrid.CertificateData.lookup n
    MontgomeryTaylorAdaptiveCell.checkLower n cs.1 cs.2 (cell l r h)
      ((b.1 : ℚ) / boundScale) ((b.2 : ℚ) / boundScale)
  else false

/-- The leaf check supplies two genuine continuous analytic bounds. -/
theorem leafCheck_sound {l r : ℚ} {b : ℤ × ℤ} {n : ℕ}
    (h : leafCheck l r b n = true) {x : ℝ} (hx : x ∈ Set.Icc (l : ℝ) r) :
    realBounds b ≤ (kernel x ^ 2, squaredDD x) := by
  unfold leafCheck at h
  split_ifs at h with hlr
  · have hphase := MontgomeryTaylorPhaseGrid.CertificateData.lookup_error n
    have hmem : x ∈ cell l r hlr :=
      IntervalDyadic.mem_ofIntervalRat (prec := -53) (hprec := by norm_num) hx
    have he := MontgomeryTaylorAdaptiveCell.lower_of_check hphase.1 hphase.2 hmem h
    simpa only [realBounds, Prod.le_def, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using he

/-- Table data include a phase index at each leaf and cached integer lower
bounds for both analytic quantities at every node. -/
abbrev Table := CertifiedRangeTree.Tree (ℤ × ℤ) ℕ

/-- Execute all leaf and cache checks for a proposed table. -/
def check (table : Table) (l r : ℚ) : Bool :=
  CertifiedRangeTree.check leafCheck table l r

/-- Independently checked table pieces compose after two cache comparisons. -/
theorem check_node {left right : Table} {l m r : ℚ} {b : ℤ × ℤ}
    (hleft : check left l m = true) (hright : check right m r = true)
    (hbl : b ≤ left.lower) (hbr : b ≤ right.lower) :
    check (.node b m left right) l r = true := by
  simp only [check, CertifiedRangeTree.check, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hbl, hbr⟩, hleft⟩, hright⟩

/-- The exact continuous meaning of a fully checked table. -/
def Valid (table : Table) (l r : ℚ) : Prop :=
  CertifiedRangeTree.Valid realBounds (fun x => (kernel x ^ 2, squaredDD x))
    (fun _ => True) table l r

/-- Every accepted table has a full continuous interpretation. -/
theorem check_sound {table : Table} {l r : ℚ} (h : check table l r = true) :
    Valid table l r :=
  CertifiedRangeTree.check_sound realBounds realBounds_monotone _ _ leafCheck
    (fun _ _ _ _ hc _ _ hx => leafCheck_sound hc hx) table h

/-- A cached query bounds the value and signed curvature at every point
of the requested interval, with the table-domain hypothesis explicit. -/
theorem query_sound {table : Table} {l r a b : ℚ} (h : Valid table l r)
    {x : ℝ} (hx : x ∈ Set.Icc (l : ℝ) r) (hq : x ∈ Set.Icc (a : ℝ) b) :
    realBounds (CertifiedRangeTree.query table l r a b) ≤ (kernel x ^ 2, squaredDD x) :=
  CertifiedRangeTree.query_sound realBounds realBounds_monotone table h trivial hx hq

/-- Squared-value queries outside the table retain the exact universal
lower bound zero. Inside the table they use the cached continuous bound. -/
def valueQuery (table : Table) (l r a b : ℚ) : ℚ :=
  if l ≤ a ∧ b ≤ r then
    ((CertifiedRangeTree.query table l r a b).1 : ℚ) / boundScale
  else 0

/-- Every squared-value query is sound, including the zero fallback for
pair separations beyond the stored table. -/
theorem valueQuery_le {table : Table} {l r a b : ℚ} (h : Valid table l r)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) b) : (valueQuery table l r a b : ℝ) ≤ kernel x ^ 2 := by
  unfold valueQuery
  split_ifs with hab
  · have hmem : x ∈ Set.Icc (l : ℝ) r :=
      ⟨(by exact_mod_cast hab.1 : (l : ℝ) ≤ a).trans hx.1,
        hx.2.trans (by exact_mod_cast hab.2 : (b : ℝ) ≤ r)⟩
    have hv := (query_sound h hmem hx).1
    simpa only [realBounds, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hv
  · simpa only [Rat.cast_zero] using sq_nonneg (kernel x)

end RiemannGaussian.MontgomeryTaylorRangeTable
