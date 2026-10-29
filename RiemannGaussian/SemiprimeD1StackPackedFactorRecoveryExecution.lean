/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryViews
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoverySources
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCount
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryDiscriminant
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryArithmetic
/-! # Complete SAME59-role recovery traces through real final factor validation
All arithmetic facts here specify actual component words. They are discharged
for EVERY semiprime by the original packed-scalar readout, never passed as data
or supplied verdicts to the fixed program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryExecution
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackPackedFactorRecoveryViews
open SemiprimeD1StackPackedFactorRecoverySources SemiprimeD1StackProcedureTrace SemiprimeBitArithmetic
namespace V
export SemiprimeD1StackPackedFactorRecoveryValidation (result validate_run time productWord)
end V
namespace H
export SemiprimeD1StackPackedFactorRecoveryHalves (phase phase_result minus_run plus_run compact_run minusTime plusTime)
end H
/-- The actual readout sum; it is never an input word. -/
def sumWord (bits scalar : List Bool) : List Bool := SemiprimeD1StackPackedMomentReadoutEncoding.moment bits scalar true
/-- Entire actual readout bank is retained unchanged by all subsequent recovery stages. -/
def retained (bits scalar : List Bool) : R.Stack→List Bool := SemiprimeD1StackPackedMomentReadoutEncoding.result bits scalar
/-- Same exact stopped source encoding for either actual arithmetic branch. -/
def stopped (data : Stack→List Bool) : C.State Stack Label := ⟨none,none,none,data,[]⟩
/-- The explicit four empty auxiliary words are the actual original source allocation. -/
theorem initial_bank (bits scalar : List Bool) :
    (initial bits scalar).data=bank (R.input bits scalar) (fun _=>[]) (words [] [] [] []) := by
  change bank _ (fun _=>[]) (fun _=>[])=_
  congr 1
  funext k;cases k <;> rfl
/-- Arithmetic correctness discharges the four real comparison-result FALSEs. -/
theorem checks (n small large : List Bool) (hs : 2≤bitValue small) (hl : 2≤bitValue large)
    (hp : bitValue small*bitValue large=bitValue n) :
    SemiprimeD1StackWordLessExecution.answer small [false,true]=false ∧
    SemiprimeD1StackWordLessExecution.answer large [false,true]=false ∧
    SemiprimeD1StackWordLessExecution.answer (V.productWord small large) n=false ∧
    SemiprimeD1StackWordLessExecution.answer n (V.productWord small large)=false := by
  have h2 : bitValue [false,true]=2 := rfl
  have hv : bitValue (V.productWord small large)=bitValue n := by rw [V.productWord,mulBits_correct,hp]
  exact ⟨SemiprimeD1StackPackedFactorRecoveryArithmetic.no_borrow small [false,true] (h2.symm ▸ hs),
    SemiprimeD1StackPackedFactorRecoveryArithmetic.no_borrow large [false,true] (h2.symm ▸ hl),
    SemiprimeD1StackPackedFactorRecoveryArithmetic.no_borrow _ _ (by omega),
    SemiprimeD1StackPackedFactorRecoveryArithmetic.no_borrow _ _ (by omega)⟩
/-- Exact final square-case data, including unused EMPTY whole33 bank. -/
def squareResult (bits scalar : List Bool) : Stack→List Bool :=
  V.result (retained bits scalar) (fun _=>[]) (fun _=>[]) (sumWord bits scalar) (sumWord bits scalar)
/-- Own square-case whole clock: actual readout, exact count parser, copies, validation and halt. -/
def squareBound (bits scalar : List Bool) : ℕ :=
  SemiprimeD1StackPackedMomentReadoutCost.polynomial bits scalar+1+9+2+
    ((5*(sumWord bits scalar).length+4)+(5*(sumWord bits scalar).length+4))+
      V.time bits (sumWord bits scalar) (sumWord bits scalar)+1
/-- Whole real square-case source, including all physical factor checks and true halt. -/
theorem square_run (bits scalar : List Bool)
    (hc : (retained bits scalar) (R.aux .count)=[true])
    (hs : 2≤bitValue (sumWord bits scalar))
    (hp : bitValue (sumWord bits scalar)*bitValue (sumWord bits scalar)=bitValue bits) :
    ∃t ≤ squareBound bits scalar,SemiprimeD1StackCalls.run program t (initial bits scalar)=some (stopped (squareResult bits scalar)) := by
  let r:=retained bits scalar
  let s:=sumWord bits scalar
  obtain ⟨a,ha,h0⟩:=readout_call bits scalar (fun _=>[]) (words [] [] [] [])
  have h1:=SemiprimeD1StackPackedFactorRecoveryCount.copy_count r (fun _=>[]) [true] hc
  change Runs program 9 _ _ _ _ at h1
  have h2:=SemiprimeD1StackPackedFactorRecoveryCount.one_run r (fun _=>[])
  have h3:=SemiprimeD1StackPackedFactorRecoveryCount.square_run r (fun _=>[]) s rfl
  obtain ⟨f0,f1,f2,f3⟩:=checks bits s s hs hs hp
  have h4:=V.validate_run r (fun _=>[]) (fun _=>[]) bits s s rfl f0 f1 f2 f3
  rw [validation_clean,clean_zero] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  obtain ⟨finish,hf,ht⟩:=h [] (initial bits scalar) ⟨rfl,initial_bank bits scalar,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (squareResult bits scalar) [] finish ht
  refine ⟨a+9+2+((5*s.length+4)+(5*s.length+4))+V.time bits s s+1,?_,?_⟩
  · unfold squareBound
    dsimp only [s]
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
    exact hh
/-- Exact final distinct-case bank; the acquired whole SQ metadata/root are retained literally. -/
def distinctResult (bits scalar lo hi : List Bool) : Stack→List Bool :=
  let d:=discriminant bits (sumWord bits scalar)
  V.result (retained bits scalar) (SemiprimeD1StackBinarySquareRootEncoding.retained d [])
    (SemiprimeD1StackBinarySquareRootEncoding.words [] (rootWord bits (sumWord bits scalar)))
    (SemiprimeD1StackReduceExecution.trimReverse lo.reverse) (SemiprimeD1StackReduceExecution.trimReverse hi.reverse)
/-- Own distinct whole clock is the sum of the SAME actual source and arithmetic stages. -/
def distinctBound (bits scalar lo hi : List Bool) : ℕ :=
  let s:=sumWord bits scalar
  let d:=discriminant bits s
  let root:=rootWord bits s
  SemiprimeD1StackPackedMomentReadoutCost.polynomial bits scalar+1+14+3+
    SemiprimeD1StackPackedFactorRecoveryDiscriminant.time bits s+(100000000*(d.length+1)^4+1)+
      H.minusTime s root lo+H.plusTime s root hi+
        (SemiprimeD1StackPackedFactorRecoveryCompaction.time lo+SemiprimeD1StackPackedFactorRecoveryCompaction.time hi)+
          V.time bits (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)
            (SemiprimeD1StackReduceExecution.trimReverse hi.reverse)+1
/-- Whole real distinct-case recovery: no supplied root/discriminant/factor enters the machine. -/
theorem distinct_run (bits scalar lo hi : List Bool)
    (hc : (retained bits scalar) (R.aux .count)=[false,true])
    (hd : (discriminantReport bits (sumWord bits scalar)).borrow=false)
    (hm : (minusReport (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).borrow=false)
    (hlo : (minusReport (sumWord bits scalar) (rootWord bits (sumWord bits scalar))).result.bits=false::lo)
    (hhi : plusWord (sumWord bits scalar) (rootWord bits (sumWord bits scalar))=false::hi)
    (hs : 2≤bitValue (SemiprimeD1StackReduceExecution.trimReverse lo.reverse))
    (hl : 2≤bitValue (SemiprimeD1StackReduceExecution.trimReverse hi.reverse))
    (hp : bitValue (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)*
      bitValue (SemiprimeD1StackReduceExecution.trimReverse hi.reverse)=bitValue bits) :
    ∃t ≤ distinctBound bits scalar lo hi,
      SemiprimeD1StackCalls.run program t (initial bits scalar)=some (stopped (distinctResult bits scalar lo hi)) := by
  let r:=retained bits scalar
  let s:=sumWord bits scalar
  let d:=discriminant bits s
  let root:=rootWord bits s
  let m:=SemiprimeD1StackBinarySquareRootEncoding.retained d []
  let v:=SemiprimeD1StackBinarySquareRootEncoding.words [] root
  let small:=SemiprimeD1StackReduceExecution.trimReverse lo.reverse
  let large:=SemiprimeD1StackReduceExecution.trimReverse hi.reverse
  obtain ⟨a,ha,h0⟩:=readout_call bits scalar (fun _=>[]) (words [] [] [] [])
  have h1:=SemiprimeD1StackPackedFactorRecoveryCount.copy_count r (fun _=>[]) [false,true] hc
  change Runs program 14 _ _ _ _ at h1
  have h2:=SemiprimeD1StackPackedFactorRecoveryCount.two_run r (fun _=>[])
  have h3:=SemiprimeD1StackPackedFactorRecoveryDiscriminant.prepare_run r bits s rfl rfl hd
  obtain ⟨b,hb,h4⟩:=squareRoot_call d r (words [] [] [] [])
  rw [←H.phase_result] at h4
  have h5:=H.minus_run r m s root lo rfl hm hlo
  have h6:=H.plus_run r m s root lo hi rfl hhi
  have h7:=H.compact_run r m root lo hi rfl
  obtain ⟨f0,f1,f2,f3⟩:=checks bits small large hs hl hp
  have h8:=V.validate_run r m v bits small large rfl f0 f1 f2 f3
  rw [validation_clean,←phase_clean] at h8
  have h:=join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8
  obtain ⟨finish,hf,ht⟩:=h [] (initial bits scalar) ⟨rfl,initial_bank bits scalar,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (distinctResult bits scalar lo hi) [] finish ht
  refine ⟨a+14+3+SemiprimeD1StackPackedFactorRecoveryDiscriminant.time bits s+b+
    H.minusTime s root lo+H.plusTime s root hi+
      (SemiprimeD1StackPackedFactorRecoveryCompaction.time lo+SemiprimeD1StackPackedFactorRecoveryCompaction.time hi)+
        V.time bits small large+1,?_,?_⟩
  · unfold distinctBound
    dsimp only [s,d,root,small,large] at hb ⊢
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
    exact hh
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryExecution
