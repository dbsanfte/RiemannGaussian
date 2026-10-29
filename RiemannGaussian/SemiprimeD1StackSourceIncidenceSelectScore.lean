/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSpec
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectOccurrences
/-! # The actual closed scorer fixes the exact original selector score
All scores here specify the binary word emitted by the actual47-role source.
No score supplier, evaluator, count or clock is an operand of the selector.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScore
open SemiprimeBitArithmetic (bitValue)
open SemiprimeD1StackSourceIncidenceSelectMeaning
namespace S
export SemiprimeD1StackSourceIncidenceSpec (total term)
end S
namespace Choice
export SemiprimeD1StackSourceIncidenceSelectSpec (tailChoice tailChoice_mem)
end Choice
/-- The whole actual ordered-pair score word represents the exact original separated incidence count. -/
theorem total_codeScore (ids:List (List Bool)) (L N:Nat) (square cube fourth:List Bool)
    (hs:bitValue square=L^2) (hc:bitValue cube=L^3) (hf:bitValue fourth=L^4)
    (rows:List (List Bool×List Bool)) (hk:ids.length ≤ N)
    (hr:∀row∈rows,bitValue row.1 < N ∧ bitValue row.2 < N) :
    bitValue (S.total ids square cube fourth rows)=
      codeScore L (List.range' ids.length (N-ids.length)) ids rows :=by
  rw [SemiprimeD1StackSourceIncidenceSpec.total_value]
  unfold codeScore
  apply congrArg List.sum
  apply List.map_congr_left
  intro left hl
  apply congrArg List.sum
  apply List.map_congr_left
  intro right hright
  exact SemiprimeD1StackSourceIncidenceSpec.term_formula ids L N square cube fourth hs hc hf left right hk
    (hr left hl) (hr right hright)
/-- The source's actual binary output has exactly the old rational query value, with denominator one. -/
theorem total_query_original (n F r a:Nat) [NeZero r] (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (ids:List (List Bool))
    (square cube fourth:List Bool) (hs:bitValue square=(r^a)^2)
    (hc:bitValue cube=(r^a)^3) (hf:bitValue fourth=(r^a)^4)
    (hk:ids.length ≤ n+F)
    (hm:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    (bitValue (S.total ids square cube fourth (originalKeys n F a arity owner)):Rat)=
      (SemiprimeD1IncidenceSearch.query (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner)
        ids (n+F-ids.length)).word.value :=by
  rw [total_codeScore ids (r^a) (n+F) square cube fourth hs hc hf _ hk
      (SemiprimeD1StackSourceIncidenceSelectOccurrences.original_key_ranges n F a arity owner),
    query_value_original n F r a arity owner ids (n+F-ids.length) hm]
/-- Winner specified by the physically produced score words, in actual catalogue order. -/
def winner (rows:List (List Bool×List Bool)) (square cube fourth:List Bool)
    (ids:List (List Bool)) (first:List Bool) (rest:List (List Bool)) :List Bool :=
  Choice.tailChoice (fun id=>bitValue (S.total (id::ids) square cube fourth rows)) first rest
/-- Actual-word winner is the exact original step choice at the physically remaining marker count. -/
theorem winner_original (n F r a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (ids:List (List Bool)) (remaining:Nat)
    (square cube fourth:List Bool) (hs:bitValue square=(r^a)^2)
    (hc:bitValue cube=(r^a)^3) (hf:bitValue fourth=(r^a)^4)
    (first:List Bool) (rest:List (List Bool)) (hlen:ids.length+1+remaining=n+F) :
    winner (originalKeys n F a arity owner) square cube fourth ids first rest=
      stepChoice (r^a) (originalKeys n F a arity owner) remaining ids first rest :=by
  apply SemiprimeD1StackSourceIncidenceSelectSpec.tailChoice_congr
  intro id _
  have hk:(id::ids).length ≤ n+F:=by simp only [List.length_cons];omega
  have h:=total_codeScore (id::ids) (r^a) (n+F) square cube fourth hs hc hf _ hk
    (SemiprimeD1StackSourceIncidenceSelectOccurrences.original_key_ranges n F a arity owner)
  have he:n+F-(id::ids).length=remaining:=by simp only [List.length_cons];omega
  rw [he] at h
  simpa only [List.length_cons] using h
/-- Exact byte-result iteration specified by actual scorer output and actual consumed marker shape. -/
def selected (rows:List (List Bool×List Bool)) (square cube fourth:List Bool)
    (first:List Bool) (rest:List (List Bool)) :List Bool→List (List Bool)→List (List Bool)
  | [],ids=>ids
  | _::tokens,ids=>selected rows square cube fourth first rest tokens
      (winner rows square cube fourth ids first rest::ids)
/-- All actual-word choices, not only their values, reproduce the complete original prepared selection. -/
theorem selected_original (n F r a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (tokens:List Bool) (ids:List (List Bool))
    (square cube fourth:List Bool) (hs:bitValue square=(r^a)^2)
    (hc:bitValue cube=(r^a)^3) (hf:bitValue fourth=(r^a)^4)
    (first:List Bool) (rest:List (List Bool)) (hlen:ids.length+tokens.length=n+F) :
    selected (originalKeys n F a arity owner) square cube fourth first rest tokens ids=
      select (r^a) (originalKeys n F a arity owner) first rest tokens ids :=by
  induction tokens generalizing ids with
  | nil=>rfl
  | cons token tokens ih=>
    have hw:=winner_original n F r a arity owner ids tokens.length square cube fourth hs hc hf first rest
      (by simp only [List.length_cons] at hlen;omega)
    rw [selected,select,hw,ih _ (by simp only [List.length_cons] at hlen ⊢;omega)]
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScore
