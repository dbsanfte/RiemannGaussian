/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesView
/-! # Actual n-marker width allocation and complete factor-counting prescan
Every bounded counter bit is physically allocated; every factor, including an
empty row, has its complete actual field parsed/drained and pushes one marker.
No source count, arity or counter width is supplied by an evaluator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesSetup
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrencesView SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Actual input source has exactly its two physical words and no derived work/key/count. -/
theorem input_data (rows number:List Bool) :
    input rows number=data rows number [] [] [] [] [] [] [] [] [] [] :=by
  funext k;cases k <;> rfl
/-- A real n marker is consumed and one actual counter-zero cell is pushed. -/
theorem width_step (rows number counter:List Bool) (n:Nat) :
    Runs program 2 (ctl .widthLoop)
      (data rows number [] [] [] (List.replicate (n+1) true) counter [] [] [] [] [])
      (ctl .widthLoop) (data rows number [] [] [] (List.replicate n true) (false::counter) [] [] [] [] []) :=by
  have h0:Runs program 1 (ctl .widthLoop)
      (data rows number [] [] [] (List.replicate (n+1) true) counter [] [] [] [] []) (ctl .widthPush)
      (data rows number [] [] [] (List.replicate n true) counter [] [] [] [] []) :=by
    apply one_base program (ctl .widthLoop) (ctl .widthPush)
      (.pop .todo (ctl .preCopy) (ctl .abort) (ctl .widthPush)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h1:Runs program 1 (ctl .widthPush)
      (data rows number [] [] [] (List.replicate n true) counter [] [] [] [] []) (ctl .widthLoop)
      (data rows number [] [] [] (List.replicate n true) (false::counter) [] [] [] [] []) :=by
    apply one_base program (ctl .widthPush) (ctl .widthLoop) (.push .counter false (ctl .widthLoop)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  exact join h0 h1
/-- Exactly the actual supplied n marker cells allocate n actual binary counter bits. -/
theorem width_loop (rows number:List Bool) (n:Nat) (counter:List Bool) :
    Runs program (2*n+1) (ctl .widthLoop)
      (data rows number [] [] [] (List.replicate n true) counter [] [] [] [] []) (ctl .preCopy)
      (data rows number [] [] [] [] (List.replicate n false++counter) [] [] [] [] []) :=by
  induction n generalizing counter with
  | zero=>
    apply one_base program (ctl .widthLoop) (ctl .preCopy)
      (.pop .todo (ctl .preCopy) (ctl .abort) (ctl .widthPush)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | succ n ih=>
    have h:=join (width_step rows number counter n) (ih (false::counter))
    have he:List.replicate n false++false::counter=List.replicate (n+1) false++counter:=by
      calc
        _=(List.replicate n false++List.replicate 1 false)++counter:=by
          simp only [List.replicate_succ,List.replicate_zero,List.append_assoc,List.singleton_append]
        _= _:=by rw [←List.replicate_add]
    simpa only [he,show 2*(n+1)+1=2+(2*n+1) from by omega] using h
/-- One preserving n copy and literal zero seed precede the actual marker-driven width loop. -/
theorem source_width (rows:List Bool) (n:Nat) :
    Runs program (7*n+6) (ctl .start) (initial rows (List.replicate n true)).data (ctl .preCopy)
      (data rows (List.replicate n true) [] [] [] [] (List.replicate (n+1) false) [] [] [] [] []) :=by
  let number:=List.replicate n true
  let b0:=data rows number [] [] [] [] [] [] [] [] [] []
  let b1:=data rows number [] [] [] number [] [] [] [] [] []
  let b2:=data rows number [] [] [] number [false] [] [] [] [] []
  have h0:=copy_call .number .start .seedZero rfl b0 number [] rfl rfl rfl
  simp only [List.append_nil] at h0
  change Runs program (5*number.length+4) (ctl .start) b0 (ctl .seedZero) (Function.update b0 .todo number) at h0
  rw [show Function.update b0 .todo number=b1 from data_todo _ _ _ _ _ _ _ _ _ _ _ _ _] at h0
  have h1:Runs program 1 (ctl .seedZero) b1 (ctl .widthLoop) b2:=by
    apply one_base program (ctl .seedZero) (ctl .widthLoop) (.push .counter false (ctl .widthLoop)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h2:=width_loop rows number n [false]
  have he:List.replicate n false++[false]=List.replicate (n+1) false:=by
    simpa only [List.replicate_succ,List.replicate_zero,List.append_nil] using (List.replicate_add n 1 false).symm
  rw [he] at h2
  have h:=join (join h0 h1) h2
  have hin:(initial rows number).data=b0:=input_data rows number
  rw [hin]
  have hn:number.length=n:=List.length_replicate
  change Runs program ((5*number.length+4)+1+(2*n+1)) _ _ _ _ at h
  simpa only [hn,show (5*n+4)+1+(2*n+1)=7*n+6 from by omega] using h
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesSetup
