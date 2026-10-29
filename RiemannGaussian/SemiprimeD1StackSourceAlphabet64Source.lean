/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Acquisition
/-! # Whole actual source prefix: retained unary width, all binary powers and real enumeration -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Source
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackSourceAlphabet64Setup
open SemiprimeD1StackSourceAlphabet64Acquisition SemiprimeD1StackSourceAlphabet64Calls
open SemiprimeD1StackProcedureTrace
/-- Exact literal four-ONE seed boundary, with actual copied source markers. -/
def seedBank (a i:Nat) :Stack→List Bool :=Sum.elim (fun _=>[]) (fun k=>match k with
  | .source|.todo=>List.replicate a true | .square=>if 0 < i then [true] else []
  | .cube=>if 1 < i then [true] else [] | .fourth=>if 2 < i then [true] else []
  | .head=>if 3 < i then [true] else [] | _=>[])
/-- The seed table executes its four literal binary ONE pushes and last real jump. -/
theorem seed_run (a:Nat) :Runs program 5 (.seed 0) (seedBank a 0) (.fill true) (seedBank a 4) :=by
  have h0:Runs program 1 (.seed 0) (seedBank a 0) (.seed 1) (seedBank a 1):=by
    apply one_base program _ _ (.push (aux .square) true (.seed 1)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h1:Runs program 1 (.seed 1) (seedBank a 1) (.seed 2) (seedBank a 2):=by
    apply one_base program _ _ (.push (aux .cube) true (.seed 2)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h2:Runs program 1 (.seed 2) (seedBank a 2) (.seed 3) (seedBank a 3):=by
    apply one_base program _ _ (.push (aux .fourth) true (.seed 3)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h3:Runs program 1 (.seed 3) (seedBank a 3) (.seed 4) (seedBank a 4):=by
    apply one_base program _ _ (.push (aux .head) true (.seed 4)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h4:Runs program 1 (.seed 4) (seedBank a 4) (.fill true) (seedBank a 4):=by
    apply one_base program _ _ (.jump (.fill true)) _ _ rfl
    · rfl
    · rfl
  exact compose (compose (compose (compose h0 h1) h2) h3) h4
/-- Exact retained actual source and acquired binary-power fields; every other auxiliary is empty. -/
def readyAux (a:Nat) :Aux→List Bool
  | .source=>List.replicate a true | .square=>power (12*a) | .cube=>power (18*a)
  | .fourth=>power (24*a) | .head=>power (6*(4*a-1)) | _=>[]
/-- Actual6a-bit zero word is now physically present, with all scratch empty. -/
def ready (a:Nat) :Stack→List Bool :=Sum.elim
  (SemiprimeD1StackAssignmentLoop.data (List.replicate (6*a) false) [] [] [] []) (readyAux a)
/-- All source-marker and literal push stages execute from the single actual unary input word. -/
theorem setup_run (a:Nat) :∃q ≤ 95*a+10,
    Runs program q .start (input (List.replicate a true)) .enumerate (ready a) :=by
  have h0:=copy_call .width .start (.seed 0) rfl (input (List.replicate a true)) rfl rfl
  have he:Function.update (input (List.replicate a true)) (copyStack .width 1)
      (input (List.replicate a true) (copyStack .width 0))=seedBank a 0:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h0
  have h1:=seed_run a
  obtain ⟨q,hq,h2⟩:=fill_run (seedBank a 4) true a rfl
  have hready:fillResult (seedBank a 4) true a=ready a:=by
    funext k
    rcases k with k|k
    · cases k <;> first | rfl | exact List.append_nil _
    · cases k <;> rfl
  rw [hready] at h2
  have hall:=compose (compose h0 h1) h2
  refine ⟨_,?_,hall⟩
  change (5*(List.replicate a true).length+4)+5+q ≤ _
  rw [List.length_replicate]
  omega
/-- Exact raw-vector acquisition boundary retains the actual powers/width and empties enumerator work. -/
def enumerated (a:Nat) :Stack→List Bool :=Sum.elim
  (SemiprimeD1StackAssignmentLoop.data [] [] [] [] (SemiprimeD1TensorTapeCodec.vectorBits (words a))) (readyAux a)
/-- One literal whole unary-width source prefix REAL-calls the whole binary enumerator ONCE. -/
theorem prefix_run (a:Nat) :∃q ≤ 95*a+100*(6*a+1)*2^(6*a)+21,
    Runs program q .start (input (List.replicate a true)) .copyStream (enumerated a) :=by
  obtain ⟨q,hq,h0⟩:=setup_run a
  obtain ⟨e,he,h1⟩:=enumerate_call (6*a) (readyAux a)
  refine ⟨q+(e+1),by omega,compose h0 h1⟩
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Source
