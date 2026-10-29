/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceEncoding
import RiemannGaussian.SemiprimeD1StackSourceIncidenceView
/-! # Exact physical stores for the ordered occurrence-pair scan -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
namespace Env
export SemiprimeD1StackSourceEnvironmentView (view)
export SemiprimeD1StackSourceEnvironmentEncoding (dictionary variableKey)
end Env
/-- Complete47-role loop boundary; every parser/comparator/adder scratch not shown is physically empty. -/
def bank (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total:List Bool) :Stack→List Bool :=
  Sum.elim (Env.view (Env.dictionary i.ids) (Env.variableKey i.ids.length) i.chosen [] i.pfx [] [] [] [] [])
    (fun k=>match k with
      | .source=>tape i | .square=>i.square | .cube=>i.cube | .fourth=>i.fourth | .savedQuery=>i.query
      | .outerReader=>outer
      | .innerReader=>inner
      | .ownerLeft=>lo
      | .factorLeft=>lf
      | .ownerRight=>ro
      | .factorRight=>rf
      | .valid=>valid
      | .eqOutput=>comparison
      | .sumLeft=>sumLeft
      | .term=>term
      | .total=>total
      | _=>[])
/-- Actual outerReader update retains every other field in the literal loop bank. -/
theorem update_outer (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .outerReader) word=
      bank i word inner lo lf ro rf valid comparison sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual innerReader update retains every other field in the literal loop bank. -/
theorem update_inner (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .innerReader) word=
      bank i outer word lo lf ro rf valid comparison sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual ownerLeft update retains every other field in the literal loop bank. -/
theorem update_lo (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .ownerLeft) word=
      bank i outer inner word lf ro rf valid comparison sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual factorLeft update retains every other field in the literal loop bank. -/
theorem update_lf (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .factorLeft) word=
      bank i outer inner lo word ro rf valid comparison sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual ownerRight update retains every other field in the literal loop bank. -/
theorem update_ro (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .ownerRight) word=
      bank i outer inner lo lf word rf valid comparison sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual factorRight update retains every other field in the literal loop bank. -/
theorem update_rf (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .factorRight) word=
      bank i outer inner lo lf ro word valid comparison sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual valid update retains every other field in the literal loop bank. -/
theorem update_valid (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .valid) word=
      bank i outer inner lo lf ro rf word comparison sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual eqOutput update retains every other field in the literal loop bank. -/
theorem update_comparison (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .eqOutput) word=
      bank i outer inner lo lf ro rf valid word sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual sumLeft update retains every other field in the literal loop bank. -/
theorem update_sumLeft (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .sumLeft) word=
      bank i outer inner lo lf ro rf valid comparison word term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual term update retains every other field in the literal loop bank. -/
theorem update_term (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .term) word=
      bank i outer inner lo lf ro rf valid comparison sumLeft word total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Actual total update retains every other field in the literal loop bank. -/
theorem update_total (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    Function.update (bank i outer inner lo lf ro rf valid comparison sumLeft term total) (aux .total) word=
      bank i outer inner lo lf ro rf valid comparison sumLeft term word :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One endpoint classifier view shares the exact same retained47-role loop bank. -/
theorem edge_bank (i:Inputs) (outer inner lo lf ro rf valid comparison sumLeft term total word:List Bool) :
    SemiprimeD1StackSourceIncidenceView.view i.ids i.chosen i.pfx
      (fun k=>bank i outer inner lo lf ro rf valid comparison sumLeft term total (aux k)) [] [] [] word [] []=
      bank i outer inner lo lf ro rf valid word sumLeft term total :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidenceLoopView
