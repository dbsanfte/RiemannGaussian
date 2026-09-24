/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldComparison
import LeanCert.Engine.IntervalEvalDyadic

/-!
# Checked real cells for the Rosser prime-counting estimates

Exact endpoint counts and outward logarithm enclosures imply the original
strict inequalities throughout each closed real interval. The count-step
interface preserves checked prime blocks without kernel re-enumeration of
the entire prefix. No numerical count or logarithm is assumed.
-/

namespace RiemannGaussian.RosserSchoenfeldFiniteBounds
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Real LeanCert.Core
open RosserSchoenfeldComparison

/-- A rigorous rational enclosure of the actual integer logarithm. -/
def logBox (n : ℕ) : IntervalRat :=
  IntervalRat.logComputable (IntervalRat.singleton n) 20

/-- The checked logarithm enclosure contains its actual real value. -/
theorem mem_logBox {n : ℕ} (hn : 0 < n) : log (n : ℝ) ∈ logBox n := by
  apply IntervalRat.mem_logComputable
  · simpa using IntervalRat.mem_singleton (n : ℚ)
  · change (0 : ℚ) < n
    exact_mod_cast hn

/-- Strict rational margins sufficient for both original count bounds on a cell. -/
def check (a b ca cb : ℕ) : Bool := decide (
  1 / 2 < (logBox a).lo ∧
  (b : ℚ) < ca * ((logBox a).lo - 1 / 2) ∧
  (cb : ℚ) * (logBox b).hi ^ 2 < a * ((logBox b).hi + 3 / 2))

/-- Checked counts and margins prove both bounds at every real point in the cell. -/
theorem comparison_on_cell {a b ca cb : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hca : ca = Nat.primeCounting a) (hcb : cb = Nat.primeCounting b)
    (hc : check a b ca cb = true) {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) b) :
    lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hb := lt_of_lt_of_le ha hab
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbR : (0 : ℝ) < b := haR.trans_le habR
  have hx0 : 0 < x := haR.trans_le hx.1
  have hla := (mem_logBox ha).1
  have hlb := (mem_logBox hb).2
  have hlax := log_le_log haR hx.1
  have hlxb := log_le_log hx0 hx.2
  simp only [check, decide_eq_true_eq] at hc
  have hA : (1 / 2 : ℝ) < ((logBox a).lo : ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hcL : (b : ℝ) < ca * (((logBox a).lo : ℝ) - 1 / 2) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.2.1
    push_cast at hh
    exact hh
  have hcU : (cb : ℝ) * ((logBox b).hi : ℝ) ^ 2 <
      a * (((logBox b).hi : ℝ) + 3 / 2) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.2.2
    push_cast at hh
    exact hh
  have hlogx : 0 < log x := by linarith
  have hB : 0 < ((logBox b).hi : ℝ) := by linarith
  have hlowCount : (ca : ℝ) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    rw [hca]
    exact_mod_cast Nat.monotone_primeCounting ((Nat.le_floor_iff hx0.le).mpr hx.1)
  have huppCount : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ cb := by
    rw [hcb]
    exact_mod_cast Nat.monotone_primeCounting (by simpa using Nat.floor_mono hx.2)
  constructor
  · apply lt_of_lt_of_le _ hlowCount
    unfold lower
    apply (div_lt_iff₀ (show 0 < log x - 1 / 2 by linarith)).mpr
    have hh := mul_le_mul_of_nonneg_left (show ((logBox a).lo : ℝ) - 1 / 2 ≤ log x - 1 / 2 by linarith)
      (Nat.cast_nonneg ca : (0 : ℝ) ≤ ca)
    exact lt_of_le_of_lt hx.2 (hcL.trans_le hh)
  · apply lt_of_le_of_lt huppCount
    have hcU' : (cb : ℝ) < (a : ℝ) / ((logBox b).hi : ℝ) *
        (1 + 3 / (2 * ((logBox b).hi : ℝ))) := by
      apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hB)).mp
      field_simp
      nlinarith
    apply hcU'.trans_le
    unfold upper
    apply mul_le_mul
    · exact div_le_div₀ hx0.le hx.1 hlogx (hlxb.trans hlb)
    · gcongr
      exact hlxb.trans hlb
    · positivity
    · positivity

/-- The complete prime list in a consecutive interval of natural numbers. -/
def primeBlock (a n : ℕ) : List ℕ :=
  (List.range' a n).filter (fun p => decide (Nat.Prime p))

/-- Actual prime counts increase by the length of the complete intervening block. -/
theorem primeCounting_step {a b : ℕ} (hab : a ≤ b) :
    Nat.primeCounting b = Nat.primeCounting a + (primeBlock (a+1) (b-a)).length := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [show b+1 = (a+1)+(b-a) by omega, Nat.count_add]
  congr 1
  simp [primeBlock, Nat.count, List.range'_eq_map_range, ← List.countP_eq_length_filter, List.countP_map, Function.comp_def]


/-- Adjacent closed cells cover their full union, including their shared endpoint. -/
theorem join {a b c : ℝ}
    (h₁ : ∀ x ∈ Set.Icc a b, lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x)
    (h₂ : ∀ x ∈ Set.Icc b c, lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x) :
    ∀ x ∈ Set.Icc a c, lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x := by
  intro x hx
  by_cases h : x ≤ b
  · exact h₁ x ⟨hx.1, h⟩
  · exact h₂ x ⟨(le_of_not_ge h), hx.2⟩


/-- A checked block transports an exact count without re-evaluating its prefix. -/
theorem primeCounting_step_of_block {a b ca cb : ℕ} {l : List ℕ}
    (hab : a ≤ b) (hca : Nat.primeCounting a = ca)
    (hblock : primeBlock (a+1) (b-a) = l) (hlen : ca+l.length = cb) :
    Nat.primeCounting b = cb := by
  rw [primeCounting_step hab, hca, hblock]
  exact hlen

/-- Complete adjacent prime blocks concatenate without a boundary overlap. -/
theorem primeBlock_append (a m n : ℕ) :
    primeBlock a (m+n) = primeBlock a m ++ primeBlock (a+m) n := by
  unfold primeBlock
  rw [← List.range'_append_1, List.filter_append]

/-- A checked prefix and a checked next block give the complete enlarged catalog. -/
theorem primeBlock_append_of_eq {a b : ℕ} {xs ys zs : List ℕ}
    (hab : a ≤ b) (hx : primeBlock 0 (a+1) = xs)
    (hy : primeBlock (a+1) (b-a) = ys) (hz : xs ++ ys = zs) :
    primeBlock 0 (b+1) = zs := by
  rw [show b+1 = (a+1)+(b-a) by omega, primeBlock_append, hx]
  simpa only [Nat.zero_add, hy] using hz


end RiemannGaussian.RosserSchoenfeldFiniteBounds
