/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeEmit
import RiemannGaussian.SemiprimeD1StackWeightedModeSubtract
/-! # Whole real weighted-node entry, restoration, successor and failed return -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeRound
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModePrimitives SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeActivation SemiprimeD1StackWeightedModeCleanup
open SemiprimeD1StackWeightedModeEmit
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Every positive actual unary weight has a real marker to drive the finite guard. -/
theorem unary_head (w:Nat) (hw:0 < w) :(unary w).head?=some true:=by
  cases w with
  | zero=>omega
  | succ w=>rw [unary_succ];rfl
/-- The real next-weight parse and guard enter exponent zero of exactly that positive weight. -/
theorem enter (cat width:List Bool) (w:Nat) (ws:List Nat) (R:Nat) (path frames hist out:List Bool)
    (hw:0 < w) :
    Runs program (8*w+10) (ctl .visit) (store (node cat width (w::ws) R path frames hist out))
      (ctl (.save 4)) (store (loop cat width w ws R 0 path frames hist out)):=by
  let v:=node cat width (w::ws) R path frames hist out
  let v1:Words:={v with weights:=frame (unary w) (vector ws)}
  let v2:Words:={v1 with weights:=vector ws,weight:=unary w,valid:=[true]}
  let v3:Words:={v2 with valid:=[]}
  have h0:=pop_run .visit (ctl .abort) (ctl .tupleSeed) (ctl .weightRead) .weights (store v)
    (true::frame (unary w) (vector ws)) rfl rfl
  rw [store_write] at h0
  change Runs program 1 _ _ (ctl .weightRead) (store v1) at h0
  have h1:=field_call .weight .weightRead .weightValid rfl (store v1) (unary w) (vector ws) rfl rfl rfl rfl
  rw [store_write,store_write,store_write,unary_length] at h1
  change Runs program (8*w+7) _ _ _ (store v2) at h1
  have h2:=pop_run .weightValid (ctl .abort) (ctl .abort) (ctl .weightPositive) .valid (store v2) [true] rfl rfl
  rw [store_write] at h2
  change Runs program 1 _ _ (ctl .weightPositive) (store v3) at h2
  have h3:Runs program 1 (ctl .weightPositive) (store v3) (ctl (.save 4)) (store v3):=by
    apply one_base program _ _ (.peek .weight (ctl .abort) (ctl (.save 4)) (ctl (.save 4))) _ _ rfl
    · simp only [SemiprimeD1StackBytecode.execute,show store v3 .weight=unary w from rfl,unary_head w hw,
        SemiprimeD1StackBytecode.choose]
    · rfl
  have hh:=join h0 (join h1 (join h2 h3))
  change Runs program (1+((8*w+7)+(1+1))) _ _ _ (store (loop cat width w ws R 0 path frames hist out)) at hh
  convert hh using 1;omega
/-- Every actual child return restores the full five-word activation by real parsers. -/
theorem restore (cat width:List Bool) (w:Nat) (ws:List Nat) (R e:Nat) (path frames hist out:List Bool) :
    Runs program (8*mass (loop cat width w ws R e path frames hist out)+41) (ctl .afterChild)
      (store (base cat width (activation w ws R e path frames) hist out)) (ctl .copyWeight)
      (store (loop cat width w ws R e path frames hist out)):=by
  let v:=base cat width frames hist out
  let fields:Fin 5→List Bool:=![unary w,vector ws,unary R,unary e,path]
  have h0:Runs program 1 (ctl .afterChild) (store (restored v fields 0 frames))
      (ctl (.restore 0)) (store (restored v fields 0 frames)):=by
    exact one_base program _ _ (.jump (ctl (.restore 0))) _ _ rfl rfl rfl
  have h1:=restore_run v fields frames rfl
  have hh:=join h0 h1
  change Runs program (1+(8*((unary w).length+(vector ws).length+(unary R).length+(unary e).length+path.length)+40))
    (ctl .afterChild) (store (base cat width (activation w ws R e path frames) hist out)) (ctl .copyWeight)
    (store (loop cat width w ws R e path frames hist out)) at hh
  convert hh using 1
  dsimp only [mass,loop,node,base]
  omega
/-- A feasible successor is created only after actually subtracting its full positive weight. -/
theorem successor (cat width:List Bool) (w:Nat) (ws:List Nat) (R e:Nat) (path frames hist out:List Bool) :
    Runs program (7*w+6) (ctl .copyWeight) (store (loop cat width w ws (w+R) e path frames hist out))
      (ctl (.save 4)) (store (loop cat width w ws R (e+1) path frames hist out)):=by
  let v:=loop cat width w ws (w+R) e path frames hist out
  let v1:Words:={v with subTodo:=unary w}
  have h0:=copy_call .weight .copyWeight .subtract rfl (store v) (unary w) [] rfl rfl rfl
  rw [List.append_nil,store_write,unary_length] at h0
  change Runs program (5*w+4) _ _ _ (store v1) at h0
  have h1:=SemiprimeD1StackWeightedModeSubtract.success v1 w R e rfl rfl rfl
  have hh:=join h0 h1
  change Runs program ((5*w+4)+(2*w+2)) _ _ _ (store (loop cat width w ws R (e+1) path frames hist out)) at hh
  convert hh using 1;omega
/-- The sole failed next-exponent test clears all mutable words and returns, creating no child. -/
theorem failed_return (cat width:List Bool) (w:Nat) (ws:List Nat) (R e:Nat) (path frames hist out:List Bool)
    (hr:R < w) :
    ∃t ≤20*(mass (loop cat width w ws R e path frames hist out)+1)+50,
      Runs program t (ctl .copyWeight) (store (loop cat width w ws R e path frames hist out))
        (ctl .returning) (store (base cat width frames hist out)):=by
  have hw:R+1 ≤ w:=by omega
  obtain ⟨d,hd⟩:=Nat.exists_eq_add_of_le hw
  have hwd:w=R+d+1:=by omega
  let v:=loop cat width w ws R e path frames hist out
  let v1:Words:={v with subTodo:=unary w}
  let v2:Words:={v with subTodo:=[],budget:=[]}
  have h0:=copy_call .weight .copyWeight .subtract rfl (store v) (unary w) [] rfl rfl rfl
  rw [List.append_nil,store_write,unary_length] at h0
  change Runs program (5*w+4) _ _ _ (store v1) at h0
  have h1:=SemiprimeD1StackWeightedModeSubtract.failure v1 R d (by change unary w=unary (R+d+1);rw [hwd]) rfl
  change Runs program (2*R+d+3) _ _ _ (store v2) at h1
  have h2:=cleanup_run v2
  change Runs program (cleanupMass v2+9) _ _ _ (store (base cat width frames hist out)) at h2
  refine ⟨(5*w+4)+((2*R+d+3)+(cleanupMass v2+9)),?_,join h0 (join h1 h2)⟩
  dsimp only [cleanupMass,v2,v,mass,loop,node,base]
  simp only [unary_length,List.length_nil,Nat.add_zero]
  omega
/-- The empty suffix emits exactly the complete actual chosen path and executes real cleanup. -/
theorem leaf_visit (cat width:List Bool) (R:Nat) (chosen:List Nat) (frames hist out:List Bool) :
    ∃t ≤70*(R+(path chosen).length+1)+1,
      Runs program t (ctl .visit) (store (node cat width [] R (path chosen) frames hist out))
        (ctl .returning) (store (base cat width frames ((row (vector chosen)).reverse++hist) out)):=by
  let fields:=chosen.reverse.map unary
  let v:=node cat width [] R (path chosen) frames hist out
  have h0:=pop_run .visit (ctl .abort) (ctl .tupleSeed) (ctl .weightRead) .weights (store v) [false] rfl rfl
  rw [store_write] at h0
  change Runs program 1 _ _ (ctl .tupleSeed)
    (store {base cat width frames hist out with budget:=unary R,path:=vectorBits fields}) at h0
  obtain ⟨t,ht,h1⟩:=leaf_run cat width R fields frames hist out
  have htuple:vectorBits fields.reverse=vector chosen:=by
    simp only [fields,List.map_reverse,List.reverse_reverse,vector]
  rw [htuple] at h1
  refine ⟨1+t,by change 1+t ≤70*(R+(vectorBits fields).length+1)+1;omega,join h0 h1⟩
end RiemannGaussian.SemiprimeD1StackWeightedModeRound
