/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopePairPrimitives
/-! # All nine physical field parses, validity reads and exact cache updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopePairParse
open SemiprimeD1StackFactorScopePairs SemiprimeD1FactorScopePairEncoding
open SemiprimeD1StackFactorScopePairView SemiprimeD1StackFactorScopePairPrimitives
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- One actual parser call and its actual positive-validity pop. -/
theorem field_run (part : Fin 9) (base : S.Stack→List Bool) (w : Record) (tail raw : List Bool) :
    Runs program (8*(w part).length+8) (.local (.field part))
      (clean base (suffix w part.val tail) (parsed part.val w) raw)
      (nextField part) (clean base (suffix w (part.val+1) tail) (parsed (part.val+1) w) raw) := by
  have h0:=field_call part (clean base (suffix w part.val tail) (parsed part.val w) raw)
    (w part) (suffix w (part.val+1) tail)
    (suffix_step w part tail) (by change (if part.val<part.val then w part else [])=[];simp) rfl rfl
  unfold clean at h0
  rw [update_reader,update_cache,parsed_step,update_valid] at h0
  have h1 : Runs program 1 (.local (.valid part))
      (data base (suffix w (part.val+1) tail) (parsed (part.val+1) w) raw [] [] [true])
      (nextField part) (clean base (suffix w (part.val+1) tail) (parsed (part.val+1) w) raw) := by
    apply one_base program (.local (.valid part)) (nextField part)
      (.pop (aux .valid) (.local .abort) (.local .abort) (nextField part)) _ _ rfl
    · rfl
    · exact update_valid _ _ _ _ _ _ _ _
  have h:=h0.trans h1
  simpa only [clean,Nat.add_assoc,show 7+1=8 from rfl] using h
/-- Fixed nine-field parser, covering empty fields and every original payload byte. -/
theorem all_fields (base : S.Stack→List Bool) (w : Record) (tail raw : List Bool) :
    Runs program (8*mass w+72) (.local (.field 0))
      (clean base (record w tail) (fun _=>[]) raw)
      (.local .tag) (clean base tail w raw) := by
  have h0:=field_run 0 base w tail raw
  have h1:=field_run 1 base w tail raw
  have h2:=field_run 2 base w tail raw
  have h3:=field_run 3 base w tail raw
  have h4:=field_run 4 base w tail raw
  have h5:=field_run 5 base w tail raw
  have h6:=field_run 6 base w tail raw
  have h7:=field_run 7 base w tail raw
  have h8:=field_run 8 base w tail raw
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8)))))))
  have hm : mass w=(w 0).length+((w 1).length+((w 2).length+((w 3).length+((w 4).length+
      ((w 5).length+((w 6).length+((w 7).length+((w 8).length+0)))))))) := rfl
  have ht:(8*(w 0).length+8)+((8*(w 1).length+8)+((8*(w 2).length+8)+((8*(w 3).length+8)+
      ((8*(w 4).length+8)+((8*(w 5).length+8)+((8*(w 6).length+8)+((8*(w 7).length+8)+(8*(w 8).length+8))))))))=
      8*mass w+72 := by omega
  rw [ht] at h
  change Runs program (8*mass w+72) (.local (.field 0))
    (clean base (record w tail) (parsed 0 w) raw) (.local .tag) (clean base tail (parsed 9 w) raw) at h
  have hz:parsed 0 w=fun _=>[]:=by funext k;simp [parsed]
  rw [parsed_end,hz] at h
  exact h
end RiemannGaussian.SemiprimeD1StackFactorScopePairParse
