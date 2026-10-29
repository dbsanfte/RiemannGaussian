/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeView
/-! # Actual five-word recursive activation save and restore
Every frame, parse, validity pop and recursive-entry cleanup executes the same
fixed controller. No activation record or continuation is a runtime structure.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeActivation
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModePrimitives SemiprimeD1StackWeightedModeView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual traces concatenate without introducing any controller opcode. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Exact current five-field byte mass; it excludes untouched older frames. -/
def mass (v:Words) :Nat:=v.weight.length+v.weights.length+v.budget.length+v.exponent.length+v.path.length
/-- Actual five-frame prefix followed by the untouched older activation records. -/
def savedFrame (v:Words) :List Bool:=frame v.weight
  (frame v.weights (frame v.budget (frame v.exponent (frame v.path v.frames))))
/-- Each real preserving-frame call has the exact word-view update. -/
theorem frame_view (site:Frame) (pc:Control) (next:Label)
    (hc:program (ctl pc)=.call (frameLabel site 0) next) (v:Words) (hs:v.frameScratch=[]) :
    Runs program (6*(store v (frameSource site)).length+5) (ctl pc) (store v) next
      (store (write v (frameTarget site) (frame (store v (frameSource site)) (store v (frameTarget site))))) :=by
  simpa only [store_write] using frame_call site pc next hc (store v) _ _ rfl rfl hs
/-- Five actual preserving calls save the complete activation in the required parse order. -/
theorem save_run (v:Words) (hs:v.frameScratch=[]) :
    Runs program (6*mass v+25) (ctl (.save 4)) (store v) (ctl .pathFrame)
      (store {v with frames:=savedFrame v}):=by
  let v1:Words:={v with frames:=frame v.path v.frames}
  let v2:Words:={v1 with frames:=frame v.exponent v1.frames}
  let v3:Words:={v2 with frames:=frame v.budget v2.frames}
  let v4:Words:={v3 with frames:=frame v.weights v3.frames}
  have h4:=frame_view (.save 4) (.save 4) (ctl (.save 3)) rfl v hs
  change Runs program (6*v.path.length+5) _ _ _ (store v1) at h4
  have h3:=frame_view (.save 3) (.save 3) (ctl (.save 2)) rfl v1 hs
  change Runs program (6*v.exponent.length+5) _ _ _ (store v2) at h3
  have h2:=frame_view (.save 2) (.save 2) (ctl (.save 1)) rfl v2 hs
  change Runs program (6*v.budget.length+5) _ _ _ (store v3) at h2
  have h1:=frame_view (.save 1) (.save 1) (ctl (.save 0)) rfl v3 hs
  change Runs program (6*v.weights.length+5) _ _ _ (store v4) at h1
  have h0:=frame_view (.save 0) (.save 0) (ctl .pathFrame) rfl v4 hs
  change Runs program (6*v.weight.length+5) _ _ _ (store {v with frames:=savedFrame v}) at h0
  have hh:=join h4 (join h3 (join h2 (join h1 h0)))
  have he:(6*v.path.length+5)+((6*v.exponent.length+5)+((6*v.budget.length+5)+
    ((6*v.weights.length+5)+(6*v.weight.length+5))))=6*mass v+25:=by unfold mass;omega
  rw [he] at hh
  exact hh
/-- Exact unparsed physical suffix after zero through five fields. -/
def suffix (fields:Fin 5→List Bool) (n:Nat) (tail:List Bool) :List Bool:=
  if n=0 then frame (fields 0) (frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) tail))))
  else if n=1 then frame (fields 1) (frame (fields 2) (frame (fields 3) (frame (fields 4) tail)))
  else if n=2 then frame (fields 2) (frame (fields 3) (frame (fields 4) tail))
  else if n=3 then frame (fields 3) (frame (fields 4) tail)
  else if n=4 then frame (fields 4) tail else tail
/-- Exactly the fields already restored by physical parser calls. -/
def restored (v:Words) (fields:Fin 5→List Bool) (n:Nat) (tail:List Bool) :Words:=
  {v with
    frames := suffix fields n tail
    weight := if 0 < n then fields 0 else []
    weights := if 1 < n then fields 1 else []
    budget := if 2 < n then fields 2 else []
    exponent := if 3 < n then fields 3 else []
    path := if 4 < n then fields 4 else []
    valid := []}
/-- The current unread word is the next physically framed field. -/
theorem restored_input (v:Words) (fields:Fin 5→List Bool) (i:Fin 5) (tail:List Bool) :
    store (restored v fields i.val tail) (parseInput (.restore i))=
      frame (fields i) (suffix fields (i.val+1) tail):=by fin_cases i <;> rfl
/-- Every restore parser writes into an ACTUALLY empty output word. -/
theorem restored_output (v:Words) (fields:Fin 5→List Bool) (i:Fin 5) (tail:List Bool) :
    store (restored v fields i.val tail) (parseOutput (.restore i))=[]:=by fin_cases i <;> rfl
/-- Actual field/validity writes advance the partial physical activation by exactly one field. -/
theorem restored_step (v:Words) (fields:Fin 5→List Bool) (i:Fin 5) (tail:List Bool) :
    Function.update (Function.update (Function.update
      (store (restored v fields i.val tail)) .frames (suffix fields (i.val+1) tail))
      (saved i) (fields i)) .valid []=store (restored v fields (i.val+1) tail):=by
  rw [store_write,store_write,store_write]
  fin_cases i <;> rfl
/-- One actual field parse and true-marker pop restore one activation field. -/
theorem restore_one (v:Words) (fields:Fin 5→List Bool) (i:Fin 5) (tail:List Bool)
    (hs:v.fieldScratch=[]) :
    Runs program (8*(fields i).length+8) (ctl (.restore i)) (store (restored v fields i.val tail))
      (restoreNext i) (store (restored v fields (i.val+1) tail)):=by
  have h0:=field_call (.restore i) (.restore i) (.restoreValid i) rfl
    (store (restored v fields i.val tail)) (fields i) (suffix fields (i.val+1) tail)
    (restored_input v fields i tail) (restored_output v fields i tail) hs rfl
  let s:=Function.update (Function.update (Function.update
      (store (restored v fields i.val tail)) .frames (suffix fields (i.val+1) tail))
      (saved i) (fields i)) .valid [true]
  change Runs program (8*(fields i).length+7) _ _ _ s at h0
  have h1:=pop_run (.restoreValid i) (ctl .abort) (ctl .abort) (restoreNext i) .valid s [true] rfl
    (Function.update_self _ _ _)
  have hh:=join h0 h1
  change Runs program ((8*(fields i).length+7)+1) _ _ _ (Function.update s .valid []) at hh
  dsimp only [s] at hh
  rw [Function.update_idem,restored_step] at hh
  simpa only [Nat.add_assoc,List.head?_cons,SemiprimeD1StackBytecode.choose] using hh
/-- Five actual parsers and five true validity pops consume exactly one saved activation. -/
theorem restore_run (v:Words) (fields:Fin 5→List Bool) (tail:List Bool) (hs:v.fieldScratch=[]) :
    Runs program (8*((fields 0).length+(fields 1).length+(fields 2).length+(fields 3).length+(fields 4).length)+40)
      (ctl (.restore 0)) (store (restored v fields 0 tail)) (ctl .copyWeight)
      (store (restored v fields 5 tail)):=by
  have h0:=restore_one v fields 0 tail hs
  have h1:=restore_one v fields 1 tail hs
  have h2:=restore_one v fields 2 tail hs
  have h3:=restore_one v fields 3 tail hs
  have h4:=restore_one v fields 4 tail hs
  have hh:=join h0 (join h1 (join h2 (join h3 h4)))
  have he:(8*(fields 0).length+8)+((8*(fields 1).length+8)+((8*(fields 2).length+8)+
      ((8*(fields 3).length+8)+(8*(fields 4).length+8))))=
      8*((fields 0).length+(fields 1).length+(fields 2).length+(fields 3).length+(fields 4).length)+40:=by omega
  change Runs program _ (ctl (.restore 0)) (store (restored v fields 0 tail)) (ctl .copyWeight)
    (store (restored v fields 5 tail)) at hh
  rw [he] at hh
  exact hh
/-- Actual saved-loop words match their original five numerical/tape fields. -/
theorem loop_saved (cat width:List Bool) (w:Nat) (ws:List Nat) (R e:Nat) (path frames hist out:List Bool) :
    savedFrame (loop cat width w ws R e path frames hist out)=activation w ws R e path frames:=rfl
/-- Physical save, path frame/tag and two real drains prepare the exact next recursive child. -/
theorem descend (cat width:List Bool) (w:Nat) (ws:List Nat) (R e:Nat) (path frames hist out:List Bool) :
    ∃t ≤ 20*(mass (loop cat width w ws R e path frames hist out)+1)+50,
      Runs program t (ctl (.save 4)) (store (loop cat width w ws R e path frames hist out))
        (ctl .child) (store (node cat width ws R (extend e path) (activation w ws R e path frames) hist out)):=by
  let v:=loop cat width w ws R e path frames hist out
  let fs:=activation w ws R e path frames
  let v1:Words:={v with frames:=fs}
  let v2:Words:={v1 with path:=frame (unary e) path}
  let v3:Words:={v2 with path:=extend e path}
  let v4:Words:={v3 with weight:=[]}
  have h0:=save_run v rfl
  change Runs program (6*mass v+25) _ _ _ (store v1) at h0
  have h1:=frame_view .path .pathFrame (ctl .pathTag) rfl v1 rfl
  change Runs program (6*(unary e).length+5) _ _ _ (store v2) at h1
  have h2:=push_run .pathTag (ctl .clearWeight) .path true (store v2) rfl
  rw [store_write] at h2
  change Runs program 1 _ _ _ (store v3) at h2
  have h3:=drain_loop .clearWeight (ctl .clearExponent) .weight rfl (store v3) (unary w) rfl
  rw [store_write] at h3
  change Runs program ((unary w).length+1) _ _ _ (store v4) at h3
  have h4:=drain_loop .clearExponent (ctl .child) .exponent rfl (store v4) (unary e) rfl
  rw [store_write] at h4
  change Runs program ((unary e).length+1) _ _ _
    (store (node cat width ws R (extend e path) fs hist out)) at h4
  refine ⟨(6*mass v+25)+((6*(unary e).length+5)+(1+(((unary w).length+1)+((unary e).length+1)))),?_,
    join h0 (join h1 (join h2 (join h3 h4)))⟩
  dsimp only [mass,v,loop,node,base]
  omega
end RiemannGaussian.SemiprimeD1StackWeightedModeActivation
