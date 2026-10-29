/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentView
import RiemannGaussian.SemiprimeD1TensorTapeCodec
/-! # Actual field-order reversal of the retained newest-first selected prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentReverse
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentPrimitives
open SemiprimeD1StackSourceEnvironmentView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- One actual outer-vector tag, complete field parser and actual true-valid pop. -/
theorem parse_step (old:Bool) (dict key q pfx tail reversed id found lookupReader out:List Bool) :
    Runs program (8*id.length+9) (ctl (if old then .readOld else .readNew))
      (view dict key [] q pfx (true::frame id tail) reversed found lookupReader out)
      (ctl (if old then .extendPrefix else .framePrefix))
      (view dict key id q pfx tail reversed found lookupReader out) :=by
  let b0:=view dict key [] q pfx (true::frame id tail) reversed found lookupReader out
  let b1:=view dict key [] q pfx (frame id tail) reversed found lookupReader out
  let b2:=Function.update (view dict key id q pfx tail reversed found lookupReader out) (lookupStack (.inr .valid)) [true]
  have h0:=pop_run (if old then .readOld else .readNew) (ctl .abort) (ctl (if old then .oldEOF else .newEOF))
    (ctl (if old then .parseOld else .parseNew)) (aux .reader) b0 (true::frame id tail)
    (by cases old <;> rfl) rfl
  change Runs program 1 _ _ (ctl (if old then .parseOld else .parseNew)) (Function.update b0 (aux .reader) (frame id tail)) at h0
  rw [show Function.update b0 (aux .reader) (frame id tail)=b1 from view_reader _ _ _ _ _ _ _ _ _ _ _] at h0
  have h1:=field_call (if old then .parseOld else .parseNew) (if old then .oldParsed else .newParsed)
    (by cases old <;> rfl) b1 id tail rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update b1 (aux .reader) tail) (aux .chosenID) id) (lookupStack (.inr .valid)) [true]) at h1
  dsimp only [b1] at h1
  rw [view_reader,view_chosenID] at h1
  change Runs program _ _ _ _ b2 at h1
  have h2:=pop_run (if old then .oldParsed else .newParsed) (ctl .abort) (ctl .abort)
    (ctl (if old then .extendPrefix else .framePrefix)) (lookupStack (.inr .valid)) b2 [true]
    (by cases old <;> rfl) rfl
  change Runs program 1 _ b2 (ctl (if old then .extendPrefix else .framePrefix))
    (Function.update b2 (lookupStack (.inr .valid)) []) at h2
  have he:Function.update b2 (lookupStack (.inr .valid)) []=view dict key id q pfx tail reversed found lookupReader out:=by
    funext k
    rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · rfl
  rw [he] at h2
  have h:=join (join h0 h1) h2
  have he:1+(8*id.length+7)+1=8*id.length+9:=by omega
  simpa only [he,b0] using h
/-- One real preserving Frame prepends the actual parsed field onto the reversed physical vector. -/
theorem reverse_step (dict key q pfx tail reversed id found lookupReader out:List Bool) :
    Runs program (15*id.length+16) (ctl .readNew)
      (view dict key [] q pfx (true::frame id tail) reversed found lookupReader out)
      (ctl .readNew) (view dict key [] q pfx tail (true::frame id reversed) found lookupReader out) :=by
  have h0:=parse_step false dict key q pfx tail reversed id found lookupReader out
  have h1:=frame_call .prefix .framePrefix .newTag rfl
    (view dict key id q pfx tail reversed found lookupReader out) id reversed rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (view dict key id q pfx tail reversed found lookupReader out)
    (aux .reversedPrefix) (frame id reversed)) at h1
  rw [view_reversedPrefix] at h1
  have h2:=push_run .newTag (ctl .clearNew) (aux .reversedPrefix) true
    (view dict key id q pfx tail (frame id reversed) found lookupReader out) rfl
  rw [show (view dict key id q pfx tail (frame id reversed) found lookupReader out) (aux .reversedPrefix)=frame id reversed from rfl,
    view_reversedPrefix] at h2
  have h3:=drain_loop .clearNew (ctl .readNew) (aux .chosenID) rfl
    (view dict key id q pfx tail (true::frame id reversed) found lookupReader out) id rfl
  rw [view_chosenID] at h3
  have h:=join (join (join h0 h1) h2) h3
  have he:((8*id.length+9)+(6*id.length+5)+1)+(id.length+1)=15*id.length+16:=by omega
  rw [he] at h
  exact h
/-- Exact sum of all actual reverse-field acquisition costs and the final tag/EOF reads. -/
def reverseClock (ids:List (List Bool)) :Nat :=(ids.map (fun id=>15*id.length+16)).sum+2
/-- The source reverses FIELDorder, rather than reversing candidate bits or using a native list reverse opcode. -/
theorem reverse_loop (dict key q pfx found lookupReader out:List Bool) (ids acc:List (List Bool)) :
    Runs program (reverseClock ids) (ctl .readNew)
      (view dict key [] q pfx (vectorBits ids) (vectorBits acc) found lookupReader out)
      (ctl .streamFirst) (view dict key [] q pfx [] (vectorBits (ids.reverse++acc)) found lookupReader out) :=by
  induction ids generalizing acc with
  | nil=>
    have h0:=pop_run .readNew (ctl .abort) (ctl .newEOF) (ctl .parseNew) (aux .reader)
      (view dict key [] q pfx [false] (vectorBits acc) found lookupReader out) [false] rfl rfl
    change Runs program 1 _ _ (ctl .newEOF) _ at h0
    rw [view_reader] at h0
    have h1:=peek_run .newEOF (ctl .streamFirst) (ctl .abort) (ctl .abort) (aux .reader)
      (view dict key [] q pfx [] (vectorBits acc) found lookupReader out) [] rfl rfl
    change Runs program 1 _ _ (ctl .streamFirst) _ at h1
    simpa only [reverseClock,List.map_nil,List.sum_nil,vectorBits,List.reverse_nil,List.nil_append] using join h0 h1
  | cons id ids ih=>
    have h0:=reverse_step dict key q pfx (vectorBits ids) (vectorBits acc) id found lookupReader out
    have h1:=ih (id::acc)
    have h:=join h0 h1
    have he:ids.reverse++id::acc=(id::ids).reverse++acc:=by simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    rw [he] at h
    have hc:15*id.length+16+reverseClock ids=reverseClock (id::ids):=by
      unfold reverseClock
      simp only [List.map_cons,List.sum_cons]
      omega
    simpa only [hc,vectorBits] using h
/-- Actual field reversal has a linear whole-vector byte clock including padded ID words. -/
theorem reverseClock_le (ids:List (List Bool)) :reverseClock ids≤20*(vectorBits ids).length :=by
  have hs:(ids.map (fun id=>15*id.length+16)).sum=15*(ids.map List.length).sum+16*ids.length:=by
    induction ids with
    | nil=>rfl
    | cons id ids ih=>simp only [List.map_cons,List.sum_cons,List.length_cons,ih];omega
  unfold reverseClock
  rw [hs,SemiprimeD1TensorTapeCodec.vectorBits_length]
  omega
/-- Two real word reversals transfer the acquired OLDEST-FIRSTvector and physically clear its work words. -/
theorem transfer_stream (dict key q pfx stream found lookupReader out:List Bool) :
    Runs program (4*stream.length+6) (ctl .streamFirst)
      (view dict key [] q pfx [] stream found lookupReader out)
      (ctl .readOld) (view dict key [] q pfx stream [] found lookupReader out) :=by
  have h0:=reverse_call .streamFirst .streamFirst .streamSecond rfl
    (view dict key [] q pfx [] stream found lookupReader out) stream [] rfl rfl
  simp only [List.append_nil] at h0
  have h1:=reverse_call .streamSecond .streamSecond .readOld rfl
    (Function.update (Function.update (view dict key [] q pfx [] stream found lookupReader out) (aux .reversedPrefix) [])
      (aux .copyWork) stream.reverse) stream.reverse [] rfl rfl
  simp only [List.append_nil,List.reverse_reverse] at h1
  have he:Function.update (Function.update
      (Function.update (Function.update (view dict key [] q pfx [] stream found lookupReader out) (aux .reversedPrefix) [])
        (aux .copyWork) stream.reverse) (aux .copyWork) []) (aux .reader) stream=
      view dict key [] q pfx stream [] found lookupReader out:=by
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> rfl
  change Runs program _ _ _ _ (Function.update (Function.update
      (Function.update (Function.update (view dict key [] q pfx [] stream found lookupReader out) (aux .reversedPrefix) [])
        (aux .copyWork) stream.reverse) (aux .copyWork) []) (aux .reader) stream) at h1
  rw [he] at h1
  have h:=join h0 h1
  have hc:(2*stream.length+3)+(2*stream.length+3)=4*stream.length+6:=by omega
  simpa only [List.length_reverse,hc] using h
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentReverse
