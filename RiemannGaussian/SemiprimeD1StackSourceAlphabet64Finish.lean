/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Loop
/-! # One actual final catalogue reversal preserves complete forward candidate/row order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Finish
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Rows SemiprimeD1StackSourceAlphabet64Loop
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackProcedureTrace
/-- Exact completed bank changes only the real catalogue output beyond the cleared row boundary. -/
def finished (base:Stack→List Bool) (a:Nat) (ws:List (List Bool)) :Stack→List Bool :=
  Function.update (boundary base [] []) (aux .output) (stream a ws++[false])
/-- One literal false push and ONE real final reversal restore all original candidate order. -/
theorem finish_run (base:Stack→List Bool) (a:Nat) (ws:List (List Bool)) (ho:base (aux .output)=[]) :
    Runs program (2*(stream a ws).length+4) .finishSeed
      (boundary base [] (stream a ws).reverse) .done (finished base a ws) :=by
  let bank:=boundary base [] (stream a ws).reverse
  let seeded:=Function.update bank (aux .output) [false]
  have h0:Runs program 1 .finishSeed bank .reverseCatalogue seeded:=by
    apply one_base program _ _ (.push (aux .output) false .reverseCatalogue) _ _ rfl
    · rfl
    · change Function.update bank (aux .output) (false::bank (aux .output))=seeded
      have hb:bank (aux .output)=[]:=ho
      rw [hb]
  have h1:=reverse_call .catalogue .reverseCatalogue .done rfl seeded
  change Runs program (2*(stream a ws).reverse.length+3) .reverseCatalogue seeded .done
    (Function.update (Function.update seeded (aux .history) []) (aux .output)
      ((stream a ws).reverse.reverse++[false])) at h1
  have he:Function.update (Function.update seeded (aux .history) []) (aux .output)
      ((stream a ws).reverse.reverse++[false])=finished base a ws:=by
    rw [List.reverse_reverse]
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h1
  have hh:=compose h0 h1
  simpa only [List.length_reverse,show 1+(2*(stream a ws).length+3)=2*(stream a ws).length+4 by omega] using hh
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Finish
