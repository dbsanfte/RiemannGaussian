/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsPrimitives

/-! # Actual linear byte join, retaining both whole acquired root sources
The first reversal exposes exactly the owner's final false marker. One real
pop removes it, and the second reversal prepends only owner record bytes to
the copied factor stream. Every bit read/write and real call is counted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecordsJoin
open SemiprimeD1StackRootNetworkRecords SemiprimeD1StackRootNetworkRecordsPrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl : Control→Label)
/-- Physically copy the factor stream into the actual eventual output accumulator. -/
theorem copy_factors (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre ys:List Bool)
    (hy:f F.output=ys) :
    Runs program (5*ys.length+4) (ctl .copyFactorOutput) (work f o number pre [] [] [])
      (ctl .copyOwnerOutput) (work f o number pre [] [] ys) := by
  have h:=copy_call .factorOutput .copyFactorOutput .copyOwnerOutput rfl
    (work f o number pre [] [] []) ys [] hy rfl rfl
  simpa only [copyTarget,List.append_nil,update_output] using h
/-- Physically copy the complete owner stream, including its actual last marker. -/
theorem copy_owners (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre xs ys:List Bool)
    (hx:o O.output=xs++[false]) :
    Runs program (5*(xs++[false]).length+4) (ctl .copyOwnerOutput) (work f o number pre [] [] ys)
      (ctl .reverseOwners) (work f o number pre (xs++[false]) [] ys) := by
  have h:=copy_call .ownerOutput .copyOwnerOutput .reverseOwners rfl
    (work f o number pre [] [] ys) (xs++[false]) [] hx rfl rfl
  simpa only [copyTarget,List.append_nil,update_left] using h
/-- First actual reversal exposes the acquired final marker and preserves all factor bytes. -/
theorem reverse_owners (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre xs ys:List Bool) :
    Runs program (2*(xs++[false]).length+3) (ctl .reverseOwners)
      (work f o number pre (xs++[false]) [] ys) (ctl .strip)
      (work f o number pre [] (false::xs.reverse) ys) := by
  have h:=reverse_call false .reverseOwners .strip rfl
    (work f o number pre (xs++[false]) [] ys) (xs++[false]) [] rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (work f o number pre (xs++[false]) [] ys) (aux .left) [])
      (aux .reverse) ((xs++[false]).reverse++[])) at h
  simpa only [update_left,update_reverse,List.reverse_append,List.reverse_singleton,
    List.singleton_append,List.append_nil] using h
/-- One actual marker pop; the bytes inside every framed field remain untouched. -/
theorem strip_owners (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre xs ys:List Bool) :
    Runs program 1 (ctl .strip) (work f o number pre [] (false::xs.reverse) ys)
      (ctl .append) (work f o number pre [] xs.reverse ys) := by
  have h:=strip_run (work f o number pre [] (false::xs.reverse) ys) xs.reverse rfl
  simpa only [update_reverse] using h
/-- Second actual reversal produces owner bytes followed by the whole factor stream. -/
theorem append_owners (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre xs ys:List Bool) :
    Runs program (2*xs.reverse.length+3) (ctl .append) (work f o number pre [] xs.reverse ys)
      (ctl .done) (work f o number pre [] [] (xs++ys)) := by
  have h:=reverse_call true .append .done rfl (work f o number pre [] xs.reverse ys) xs.reverse ys rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (work f o number pre [] xs.reverse ys) (aux .reverse) [])
      output (xs.reverse.reverse++ys)) at h
  simpa only [update_reverse,update_output,List.reverse_reverse] using h
/-- One whole same-program physical linear join, retaining all1798 acquired source cells. -/
theorem join_trace (f:F.Stack→List Bool) (o:O.Stack→List Bool) (number pre xs ys:List Bool)
    (hx:o O.output=xs++[false]) (hy:f F.output=ys) :
    Runs program (5*ys.length+9*xs.length+22) (ctl .copyFactorOutput)
      (work f o number pre [] [] []) (ctl .done) (work f o number pre [] [] (xs++ys)) := by
  have h0:=copy_factors f o number pre ys hy
  have h1:=copy_owners f o number pre xs ys hx
  have h2:=reverse_owners f o number pre xs ys
  have h3:=strip_owners f o number pre xs ys
  have h4:=append_owners f o number pre xs ys
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have he:((((5*ys.length+4)+(5*(xs++[false]).length+4))+(2*(xs++[false]).length+3))+1)+
      (2*xs.reverse.length+3)=5*ys.length+9*xs.length+22 := by
    simp only [List.length_append,List.length_cons,List.length_nil,List.length_reverse]
    omega
  simpa only [he] using h
end RiemannGaussian.SemiprimeD1StackRootNetworkRecordsJoin
