/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalRow
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueLoop
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueParse SemiprimeD1StackOwnerCatalogueRow
open SemiprimeD1StackOwnerCatalogueOriginalRow
open SemiprimeD1StackPortOwnerRecipeSpec (original)
open SemiprimeD1StackPortOwnerRecipeClassify (originalTag)
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Proof specification of the actual E records and the first E physically acquired M-bank words. -/
abbrev Pair (r t digits:Nat) := SemiprimeMacroGraph.Edge r t digits×List Bool
/-- Exact actual six-field edge reader; each record has no extra vector marker. -/
def edgeTapeOf {r t digits:Nat} (pairs:List (Pair r t digits)) : List Bool :=
  pairs.foldr (fun p rest=>SemiprimeD1EdgeCatalogueEncoding.edge p.1 rest) []
/-- Exact actual acquired ID-vector prefix followed by the untouched M-E suffix. -/
def idTapeOf {r t digits:Nat} (pairs:List (Pair r t digits)) (tail:List Bool) : List Bool :=
  pairs.foldr (fun p rest=>true::frame p.2 rest) tail
/-- The actual emitted row bytes, preserving physical edge order and both endpoint halves. -/
def bytes {r t digits:Nat} (pairs:List (Pair r t digits)) : List Bool :=
  pairs.flatMap (fun p=>emitted (fields p.1 p.2) (original p.1) (originalTag p.1))
/-- Sum of the SAME physical row-iteration budgets. -/
def budget {r t digits:Nat} (pairs:List (Pair r t digits)) : Nat :=
  (pairs.map (fun p=>SemiprimeD1StackOwnerCatalogueRow.budget (fields p.1 p.2)
    (original p.1) (originalTag p.1))).sum
/-- Entire real E-wire loop, consuming exactly one owner-ID word per actual edge.
The unused acquired ID suffix remains present; no identification of E and M is used. -/
theorem loop_run {r t digits:Nat} (hd:0<digits) (s:S.Stack→List Bool) (hm:Metadata s r t digits)
    (pairs:List (Pair r t digits)) (ids collector:List Bool) :
    ∃time≤budget pairs,Runs program time (.local .parse)
      (data s (fun _=>[]) (fun _=>[]) (rowAux (edgeTapeOf pairs) (idTapeOf pairs ids) collector))
      (.local .parse) (data s (fun _=>[]) (fun _=>[]) (rowAux [] ids ((bytes pairs).reverse++collector))) := by
  induction pairs generalizing collector with
  | nil=>
    refine ⟨0,by simp [budget],?_⟩
    exact SemiprimeD1StackProcedureTrace.runs_refl program _ _
  | cons p pairs ih=>
    obtain ⟨a,ha,har⟩:=original_row_run hd s hm p.1 p.2 (edgeTapeOf pairs) (idTapeOf pairs ids) collector
    obtain ⟨b,hb,hbr⟩:=ih ((emitted (fields p.1 p.2) (original p.1) (originalTag p.1)).reverse++collector)
    have h:=runs_trans program _ _ _ _ _ _ _ _ har hbr
    refine ⟨a+b,?_,?_⟩
    · simp only [budget,List.map_cons,List.sum_cons] at *
      omega
    · simpa only [edgeTapeOf,idTapeOf,List.foldr_cons,bytes,List.flatMap_cons,List.reverse_append,List.append_assoc] using h
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueLoop
