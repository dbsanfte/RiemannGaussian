/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEuclidGCDCalls
/-! # Physically acquired byte fuel and actual initial Euclid operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackEuclidGCDSetup
open SemiprimeD1StackEuclidGCD SemiprimeD1StackEuclidGCDEncoding SemiprimeD1StackEuclidGCDCalls
open SemiprimeD1StackProcedureTrace
/-- Every real byte pop executes both literal true-marker pushes; the EOF is charged too. -/
theorem scan_run (right:Bool) (w:Words) (xs:List Bool) :
    Runs program (3*xs.length+1) (.scan right) (bank {w with scan:=xs})
      (if right then .initialX else .copyFuelRight)
      (bank {w with scan:=[],fuel:=List.replicate (2*xs.length) true++w.fuel}) :=by
  induction xs generalizing w with
  | nil=>
    have h:=P.pop_run (.scan right) (if right then .initialX else .copyFuelRight)
      (.pushOne right) (.pushOne right) (aux .scan) (bank {w with scan:=[]}) [] rfl rfl
    rw [update_scan] at h
    exact h
  | cons b xs ih=>
    have h0:=P.pop_run (.scan right) (if right then .initialX else .copyFuelRight)
      (.pushOne right) (.pushOne right) (aux .scan) (bank {w with scan:=b::xs}) (b::xs) rfl rfl
    rw [update_scan] at h0
    have hchoose:SemiprimeD1StackBytecode.choose (if right then Label.initialX else .copyFuelRight)
        (.pushOne right) (.pushOne right) (b::xs).head?=Label.pushOne right:=by cases b <;> rfl
    rw [hchoose] at h0
    have h1:=P.push_run (.pushOne right) (.pushTwo right) (aux .fuel) true (bank {w with scan:=xs}) rfl
    change Runs _ _ _ _ _ (Function.update (bank _) (aux .fuel) (true::w.fuel)) at h1
    rw [update_fuel] at h1
    have h2:=P.push_run (.pushTwo right) (.scan right) (aux .fuel) true
      (bank {w with scan:=xs,fuel:=true::w.fuel}) rfl
    change Runs _ _ _ _ _ (Function.update (bank _) (aux .fuel) (true::true::w.fuel)) at h2
    rw [update_fuel] at h2
    have h3:=ih {w with fuel:=true::true::w.fuel}
    have h:=P.join (P.join (P.join h0 h1) h2) h3
    have he:List.replicate (2*xs.length) true++true::true::w.fuel=
        List.replicate (2*(b::xs).length) true++w.fuel:=by
      rw [show 2*(b::xs).length=2*xs.length+2 by simp only [List.length_cons];omega,
        List.replicate_add,List.append_assoc]
      rfl
    change Runs _ _ _ _ _ (bank {w with scan:=[],fuel:=List.replicate (2*xs.length) true++true::true::w.fuel}) at h
    rw [he] at h
    convert h using 1
    simp only [List.length_cons]
    omega
/-- Literal total source clock through the first clean Euclid loop boundary. -/
def setupTime (left right:List Bool) :Nat:=
  1+(5*left.length+4)+(3*left.length+1)+(5*right.length+4)+(3*right.length+1)+
    (5*left.length+4)+(5*right.length+4)+(2*right.length+3)+
      (SemiprimeD1StackReduceExecution.trimTime right.reverse+1)
/-- The source pays four preserving input copies, actual scans and the actual initial trim. -/
theorem setup_run (left right:List Bool) :
    Runs program (setupTime left right) .start (input left right) .loop
      (bank (loopWords left right (List.replicate (SemiprimeD1StackEuclidGCDSpec.fuelLength left right) true)
        left (SemiprimeD1StackSourceEnvironmentEncoding.normalize right))) :=by
  rw [initial_bank]
  have h0:=P.push_run .start .copyFuelLeft (aux .fuel) true
    (bank {originalLeft:=left,originalRight:=right}) rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .fuel) [true]) at h0
  rw [update_fuel] at h0
  have h1:=P.copy_call .fuelLeft .copyFuelLeft (.scan false) rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=[true]}) left [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .scan) (left++[])) at h1
  rw [List.append_nil,update_scan] at h1
  have h2:=scan_run false {originalLeft:=left,originalRight:=right,fuel:=[true]} left
  have h3:=P.copy_call .fuelRight .copyFuelRight (.scan true) rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=List.replicate (2*left.length) true++[true]})
    right [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (aux .scan) (right++[])) at h3
  rw [List.append_nil,update_scan] at h3
  have h4:=scan_run true {originalLeft:=left,originalRight:=right, fuel:=List.replicate (2*left.length) true++[true]} right
  let fuel:=List.replicate (2*right.length) true++(List.replicate (2*left.length) true++[true])
  have h5:=P.copy_call .initialX .initialX .initialY rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel}) left [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .input)) (left++[])) at h5
  rw [List.append_nil,update_x] at h5
  have h6:=P.copy_call .initialY .initialY .reverseInitial rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,x:=left}) right [] rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank _) (dividerStack (.inr .divisor)) (right++[])) at h6
  rw [List.append_nil,update_y] at h6
  have h7:=P.reverse_call .initialY .reverseInitial .trimInitial rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,x:=left,y:=right}) right [] rfl rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank _) (dividerStack (.inr .divisor)) [])
    (aux .trimScratch) (right.reverse++[])) at h7
  rw [List.append_nil,update_y,update_trimScratch] at h7
  have h8:=P.trim_call .divisor .trimInitial .loop rfl
    (bank {originalLeft:=left,originalRight:=right,fuel:=fuel,x:=left,trimScratch:=right.reverse}) right.reverse [] rfl rfl rfl rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank _) (aux .trimScratch) [])
    (dividerStack (.inr .divisor)) (SemiprimeD1StackReduceExecution.trimReverse right.reverse++[])) at h8
  rw [List.append_nil,update_trimScratch,update_y] at h8
  have h:=P.join (P.join (P.join (P.join (P.join (P.join (P.join (P.join h0 h1) h2) h3) h4) h5) h6) h7) h8
  have hf:fuel=List.replicate (SemiprimeD1StackEuclidGCDSpec.fuelLength left right) true:=by
    change List.replicate (2*right.length) true++(List.replicate (2*left.length) true++List.replicate 1 true)=_
    rw [←List.replicate_add,←List.replicate_add]
    congr 1
    unfold SemiprimeD1StackEuclidGCDSpec.fuelLength
    omega
  simpa only [setupTime,hf,loopWords,SemiprimeD1StackSourceEnvironmentEncoding.normalize] using h
end RiemannGaussian.SemiprimeD1StackEuclidGCDSetup
