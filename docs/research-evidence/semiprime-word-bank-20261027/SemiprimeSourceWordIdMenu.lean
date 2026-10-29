/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordBankSemantics
import RiemannGaussian.SemiprimeSourceWordBankIndexed
import RiemannGaussian.SemiprimeSourceWordMenuOrder
import RiemannGaussian.SemiprimeSourceWordIdControl

/-! # Actual acquired candidate-ID menu and exact indexed-source order
The runtime menu is obtained directly from the acquired Boolean IDs. Decoding
and the original indexed enumeration are proof specifications only.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceWordIdMenu
open SemiprimeSourceWordBank SemiprimeSourceWordBankSemantics
open SemiprimeSourceWordIdControl

/-- Actual physical first candidate, with a total literal fallback. -/
def first (bank : Bank) : List Bool := bank.ids.headD []
/-- Actual remaining physical candidates, retaining their exact acquired order. -/
def tail (bank : Bank) : List (List Bool) := bank.ids.tail

/-- Positive original alphabet gives a genuinely nonempty acquired ID bank. -/
theorem ids_nonempty (r Q : ℕ) [NeZero r] : (acquire r Q).ids ≠ [] := by
  have hlen : (acquire r Q).ids.length=r^Q := by
    rw [acquire_ids_length]
    exact rows_length r Q
  have hp : 0 < r^Q := pow_pos (NeZero.pos r) _
  intro h
  rw [h] at hlen
  simp only [List.length_nil] at hlen
  omega

/-- Controller head/tail exactly split the acquired finite menu. -/
theorem split (r Q : ℕ) [NeZero r] : first (acquire r Q)::tail (acquire r Q)=(acquire r Q).ids := by
  have h := ids_nonempty r Q
  cases hi : (acquire r Q).ids with
  | nil => exact False.elim (h hi)
  | cons a as => simp [first,tail,hi]

/-- The physical controller's first candidate really belongs to its acquired bank. -/
theorem first_mem (r Q : ℕ) [NeZero r] : first (acquire r Q)∈(acquire r Q).ids := by
  rw [← split r Q]
  exact List.mem_cons_self

/-- All concrete controller candidates are actual acquired IDs. -/
theorem candidates_valid (r Q : ℕ) [NeZero r] :
    InMenu (acquire r Q).ids (first (acquire r Q)::tail (acquire r Q)) := by
  rw [split r Q]
  exact fun _ h => h

/-- The actual physical menu decodes to the canonical zero-first indexed menu. -/
theorem indexed_decode (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (acquire r Q).ids.map (decode r Q)=
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst::
        (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordTail := by
  rw [ids_decode,SemiprimeSourceWordMenuOrder.indexed_menu]

/-- Exact first-candidate equality, preserving the original tie convention. -/
theorem first_decode (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    decode r Q (first (acquire r Q))=
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst := by
  have h := indexed_decode n F r Q arity
  rw [← split r Q,List.map_cons] at h
  exact (List.cons.inj h).1

/-- Exact tail equality, beyond membership/cardinality or a permutation. -/
theorem tail_decode (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (tail (acquire r Q)).map (decode r Q)=
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordTail := by
  have h := indexed_decode n F r Q arity
  rw [← split r Q,List.map_cons] at h
  exact (List.cons.inj h).2

/-- The actually acquired first physical ID is the literal zero default used by counting. -/
theorem first_eq_default (r Q : ℕ) [NeZero r] : first (acquire r Q)=defaultID := by
  apply decode_injective r Q (first_mem r Q) (SemiprimeSourceWordBankIndexed.default_mem r Q)
  have h := first_decode 0 0 r Q (fun i => Fin.elim0 i)
  have hz : decode r Q (first (acquire r Q))=(fun _ => 0) := h
  exact hz.trans (SemiprimeSourceWordBankIndexed.decode_default r Q).symm

end RiemannGaussian.SemiprimeSourceWordIdMenu
