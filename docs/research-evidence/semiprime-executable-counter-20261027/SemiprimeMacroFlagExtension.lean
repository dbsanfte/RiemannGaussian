/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroGraph
import RiemannGaussian.SemiprimeMacroBitNetwork

/-!
# Canonical extension of actual macro graph flag wires

The digit flags determine every OR output uniquely. The terminal check reads
exactly whether a source digit flag is true, including the one-digit graph.
No assumption about accepted multiplication or a counter is used here.
-/
namespace RiemannGaussian.SemiprimeMacroFlagExtension

open SemiprimeMacroGraph

/-- Executable orPrefix OR, with false padding outside the digit range. -/
def orPrefix {d : ℕ} (hd : 0 < d) (flags : Fin d → Bool) : ℕ → Bool
  | 0 => flags ⟨0, hd⟩
  | k + 1 => orPrefix hd flags k || if h : k + 1 < d then flags ⟨k + 1, h⟩ else false

/-- Canonical values of the literal digit and non-initial OR wires. -/
def buildFlags {d : ℕ} (hd : 0 < d) (flags : Fin 2 → Fin d → Bool) :
    FlagSignal d → Bool
  | .digit side i => flags side i
  | .orOut side i => orPrefix hd (flags side) (i.val + 1)

@[simp] theorem buildFlags_digit {d : ℕ} (hd : 0 < d)
    (flags : Fin 2 → Fin d → Bool) (side : Fin 2) (i : Fin d) :
    buildFlags hd flags (.digit side i) = flags side i := rfl

/-- The actual previous-wire index, not an abstract list predecessor. -/
def previous {d : ℕ} (hd : 0 < d) (values : FlagSignal d → Bool)
    (side : Fin 2) (i : Fin (d - 1)) : Bool :=
  if hi : i.val = 0 then values (.digit side ⟨0, hd⟩)
  else values (.orOut side ⟨i.val - 1, by have := i.isLt; omega⟩)

/-- The literal terminal wire also covers the d=1 case without an OR output. -/
def terminal {d : ℕ} (hd : 0 < d) (values : FlagSignal d → Bool)
    (side : Fin 2) : Bool :=
  if he : d = 1 then values (.digit side ⟨0, hd⟩)
  else values (.orOut side ⟨d - 2, by omega⟩)

/-- Every generated value satisfies its actual local OR-vertex equation. -/
theorem buildFlags_or {d : ℕ} (hd : 0 < d) (flags : Fin 2 → Fin d → Bool)
    (side : Fin 2) (i : Fin (d - 1)) :
    buildFlags hd flags (.orOut side i) =
      (previous hd (buildFlags hd flags) side i ||
        flags side ⟨i.val + 1, by have := i.isLt; omega⟩) := by
  have hi : i.val + 1 < d := by have := i.isLt; omega
  change orPrefix hd (flags side) (i.val + 1) =
    ((if hz : i.val = 0 then flags side ⟨0, hd⟩ else
      orPrefix hd (flags side) (i.val - 1 + 1)) || flags side ⟨i.val + 1, hi⟩)
  rw [orPrefix]
  simp only [dite_eq_left hi]
  by_cases hz : i.val = 0
  · simp only [dite_eq_left hz]
    congr 1
    rw [hz]
    rfl
  · have hp : i.val - 1 + 1 = i.val := by omega
    simp only [dite_eq_right hz, hp]

/-- Prefix truth is precisely a true digit within its index range. -/
theorem prefix_true_iff {d : ℕ} (hd : 0 < d) (flags : Fin d → Bool)
    (k : ℕ) (hk : k < d) :
    orPrefix hd flags k = true ↔ ∃ i : Fin d, i.val ≤ k ∧ flags i = true := by
  induction k with
  | zero =>
    simp only [orPrefix]
    constructor
    · intro h; exact ⟨⟨0, hd⟩, Nat.le_refl 0, h⟩
    · rintro ⟨i, hi, hf⟩
      have he : i = ⟨0, hd⟩ := Fin.ext (by change i.val = 0; omega)
      simpa [he] using hf
  | succ k ih =>
    have hprev : k < d := by omega
    simp only [orPrefix, dite_eq_left hk, Bool.or_eq_true, ih hprev]
    constructor
    · rintro (⟨i, hi, hf⟩ | hf)
      · exact ⟨i, by omega, hf⟩
      · exact ⟨⟨k + 1, hk⟩, Nat.le_refl _, hf⟩
    · rintro ⟨i, hi, hf⟩
      by_cases he : i.val = k + 1
      · right
        have hx : i = ⟨k + 1, hk⟩ := Fin.ext he
        simpa [hx] using hf
      · exact Or.inl ⟨i, by omega, hf⟩

/-- The terminal reads exactly the OR of all digit flags. -/
theorem terminal_buildFlags_iff {d : ℕ} (hd : 0 < d)
    (flags : Fin 2 → Fin d → Bool) (side : Fin 2) :
    terminal hd (buildFlags hd flags) side = true ↔ ∃ i, flags side i = true := by
  have hlast : d - 1 < d := by omega
  have hterm : terminal hd (buildFlags hd flags) side = orPrefix hd (flags side) (d - 1) := by
    by_cases he : d = 1
    · simp [terminal, he, buildFlags, orPrefix]
    · have hs : d - 2 + 1 = d - 1 := by omega
      simp [terminal, he, buildFlags, hs]
  rw [hterm, prefix_true_iff hd (flags side) (d - 1) hlast]
  constructor
  · rintro ⟨i, _, hf⟩; exact ⟨i, hf⟩
  · rintro ⟨i, hf⟩; exact ⟨i, by have := i.isLt; omega, hf⟩

/-- Local digit and OR checks admit no additional internal extension choices. -/
theorem unique_flags {d : ℕ} (hd : 0 < d) (flags : Fin 2 → Fin d → Bool)
    (values : FlagSignal d → Bool)
    (hdigit : ∀ side i, values (.digit side i) = flags side i)
    (hor : ∀ side (i : Fin (d - 1)), values (.orOut side i) =
      (previous hd values side i || flags side ⟨i.val + 1, by have := i.isLt; omega⟩)) :
    values = buildFlags hd flags := by
  have hout : ∀ (side : Fin 2) (k : ℕ) (hk : k < d - 1),
      values (.orOut side ⟨k, hk⟩) = orPrefix hd (flags side) (k + 1) := by
    intro side k
    induction k with
    | zero =>
      intro hk
      have hb : 1 < d := by omega
      simpa [previous, orPrefix, hdigit, hb] using hor side ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hprev : k < d - 1 := by omega
      have hb : k + 1 + 1 < d := by omega
      have he : k + 1 - 1 = k := by omega
      simpa [previous, orPrefix, he, hb, ih hprev] using hor side ⟨k + 1, hk⟩
  funext signal
  cases signal with
  | digit side i => exact hdigit side i
  | orOut side i => exact hout side i.val i.isLt

/-- Exactly one complete flag assignment satisfies the actual local equations. -/
theorem existsUnique_flags {d : ℕ} (hd : 0 < d) (flags : Fin 2 → Fin d → Bool) :
    ∃! values : FlagSignal d → Bool,
      (∀ side i, values (.digit side i) = flags side i) ∧
      (∀ side (i : Fin (d - 1)), values (.orOut side i) =
        (previous hd values side i || flags side ⟨i.val + 1, by have := i.isLt; omega⟩)) := by
  refine ⟨buildFlags hd flags, ⟨buildFlags_digit hd flags, buildFlags_or hd flags⟩, ?_⟩
  intro values h
  exact unique_flags hd flags values h.1 h.2

/-- Actual source input flag, with the special low-digit nontriviality check. -/
def inputFlag {d bits : ℕ} (words : Fin d → BitVec bits) (i : Fin d) : Bool :=
  if i.val = 0 then decide (2 ≤ SemiprimeBooleanNetwork.decode (words i))
  else decide (SemiprimeBooleanNetwork.decode (words i) ≠ 0)

/-- True source flags are equivalent to a nontrivial actual radix operand. -/
theorem inputFlag_exists_iff {d bits : ℕ} (hd : 0 < d)
    (words : Fin d → BitVec bits) (hbits : 0 < bits) :
    (∃ i, inputFlag words i = true) ↔ 2 ≤ SemiprimeBooleanNetwork.operand words := by
  cases d with
  | zero => omega
  | succ d =>
    have he := SemiprimeMacroBitNetwork.actual_input_flag words hbits
    rw [SemiprimeMacroBitNetwork.or_terminal] at he
    have ht :
        ((List.ofFn (fun i : Fin d => SemiprimeBooleanNetwork.decode (words i.succ))).map
          (fun digit => decide (digit ≠ 0))).any id = true ↔
          ∃ i : Fin d, SemiprimeBooleanNetwork.decode (words i.succ) ≠ 0 := by
      rw [List.any_map, List.any_eq_true]
      constructor
      · rintro ⟨x, hx, hp⟩
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact ⟨i, by simpa using hp⟩
      · rintro ⟨i, hi⟩
        exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, by simpa using hi⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq, ht,
      SemiprimeBooleanNetwork.nontrivialFlag] at he
    simpa [Fin.exists_fin_succ, inputFlag] using he

/-- Canonical terminal truth for the actual bit-array input checks. -/
theorem terminal_inputFlag_iff {d bits : ℕ} (hd : 0 < d)
    (words : Fin 2 → Fin d → BitVec bits) (hbits : 0 < bits) (side : Fin 2) :
    terminal hd (buildFlags hd (fun s => inputFlag (words s))) side = true ↔
      2 ≤ SemiprimeBooleanNetwork.operand (words side) := by
  rw [terminal_buildFlags_iff, inputFlag_exists_iff hd (words side) hbits]

end RiemannGaussian.SemiprimeMacroFlagExtension

#print axioms RiemannGaussian.SemiprimeMacroFlagExtension.buildFlags_or
#print axioms RiemannGaussian.SemiprimeMacroFlagExtension.terminal_buildFlags_iff
#print axioms RiemannGaussian.SemiprimeMacroFlagExtension.unique_flags
#print axioms RiemannGaussian.SemiprimeMacroFlagExtension.existsUnique_flags

#print axioms RiemannGaussian.SemiprimeMacroFlagExtension.inputFlag_exists_iff
#print axioms RiemannGaussian.SemiprimeMacroFlagExtension.terminal_inputFlag_iff
