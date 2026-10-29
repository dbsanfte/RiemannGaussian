/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAcquiredPrefixSearch
import RiemannGaussian.SemiprimeLocalBits

/-! # Original checker bits directly supply physical local entries

The actual Boolean checker and every-occurrence restriction execute once.
Their accepted bit becomes the one-cell numerator, without an integer or
rational encoding pass. Finite prefix/address implementation remains the same
explicit boundary as the original prefix controller.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimePrefixEntryWords
open SemiprimeMacroEntryBitPrimitives SemiprimeLocalBits
open SemiprimeBitIndexClipping SemiprimeBitArithmetic
variable {n F : ℕ}

/-- Materialize the actual accepted bit and retain checker and prefix-scan work. -/
def entry (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) : EntryWord :=
  let original := base e input
  let accepted := original.accepted && SemiprimeAcquiredPrefixSearch.prefixGate arity coordinate fixed e input
  ⟨⟨false,[accepted]⟩,original.clock+fixed.length*(3*arity e+2)+4⟩

/-- The physical one-cell integer is exactly the original restricted entry. -/
theorem entry_value (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    (entry arity coordinate base fixed e input).bits.value =
      (SemiprimeAcquiredPrefixSearch.entry arity coordinate base fixed e input).value := by
  simp [entry,SemiprimeAcquiredPrefixSearch.entry,SignedWord.value,bitValue,bitNat]

/-- No output-height advice is needed for the actual original Boolean table. -/
theorem entry_abs (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    (entry arity coordinate base fixed e input).bits.value.natAbs ≤ 1 := by
  rw [entry_value]
  exact SemiprimeAcquiredPrefixSearch.entry_abs arity coordinate base fixed e input

/-- The original checker produces a literal single-cell magnitude. -/
theorem entry_length (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    (entry arity coordinate base fixed e input).bits.magnitude.length=1 := rfl

/-- Word construction adds three cells to the retained original entry ledger. -/
theorem entry_clock (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (e : Fin F) (input : Fin (arity e) → Bool) :
    (entry arity coordinate base fixed e input).clock =
      (SemiprimeAcquiredPrefixSearch.entry arity coordinate base fixed e input).arithmetic+3 := by
  simp only [entry,SemiprimeAcquiredPrefixSearch.entry,Nat.add_assoc]

/-- Uniform costs are supplied by the real checker, with the prefix scan retained. -/
theorem entry_clock_le (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (base : (e : Fin F) → (Fin (arity e) → Bool) → CheckRun)
    (fixed : List (Fin n × Bool)) (A w : ℕ)
    (hw : ∀ e, arity e≤w) (hbase : ∀ e input, (base e input).clock≤A)
    (e : Fin F) (input : Fin (arity e) → Bool) :
    (entry arity coordinate base fixed e input).clock ≤ A+fixed.length*(3*w+2)+4 := by
  change (base e input).clock+fixed.length*(3*arity e+2)+4 ≤ _
  gcongr
  exact hbase e input
  exact hw e

end RiemannGaussian.SemiprimePrefixEntryWords
