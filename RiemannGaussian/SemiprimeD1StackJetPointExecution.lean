/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPoint
import RiemannGaussian.SemiprimeD1StackProcedureInclusion

/-! # Executed component adapters for the physical convolution controller
The source of every copy is the actual reached Boolean-stack bank. These lemmas
compose real included procedures; none installs a coefficient or routing answer.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetPointExecution
open SemiprimeD1StackJetPoint
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)

/-- Literal source and target registers of every declared copy are distinct. -/
theorem copy_source_ne_target (site : Transfer) : copySource site ≠ copyTarget site := by
  cases site <;> decide
/-- Every physical copy scratch register is disjoint from its source. -/
theorem copy_source_ne_work (site : Transfer) : copySource site ≠ aux .copyWork := by
  cases site <;> decide
/-- Every physical copy scratch register is disjoint from its destination. -/
theorem copy_target_ne_work (site : Transfer) : copyTarget site ≠ aux .copyWork := by
  cases site <;> decide

/-- Real copy-call execution at any of the nine literal controller sites.
The source word is read from the actual state; output and scratch emptiness are
ordinary internal loop invariants, not supplied output values or time bounds. -/
theorem copy_call (site : Transfer) (pc next : Label) (data : Stack → List Bool)
    (hcode : program pc=.call (.copy site 0) next)
    (ht : data (copyTarget site)=[]) (hw : data (aux .copyWork)=[]) :
    Runs program (5*(data (copySource site)).length+4) pc data next
      (Function.update data (copyTarget site) (data (copySource site))) := by
  let word:=data (copySource site)
  let result:=Function.update data (copyTarget site) word
  have hst:=copy_source_ne_target site
  have hsw:=copy_source_ne_work site
  have htw:=copy_target_ne_work site
  apply SemiprimeD1StackProcedureTrace.included_call program (copyStack site) (Label.copy site)
    (copyStack_injective site) SemiprimeD1StackCopy.code (0:Fin 9) (fun _=>rfl)
    pc next hcode (5*word.length+3) (SemiprimeD1StackCopy.state 0 none word [] [])
    (SemiprimeD1StackCopy.done word word) data result
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none
  · constructor
    · intro k
      fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,word,ht,hw]
    · intro k hk
      rfl
  · constructor
    · intro k
      fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,
        result,word,Function.update_of_ne hst,Function.update_of_ne htw.symm,hw]
    · intro k hk
      have hn : k ≠ copyTarget site := fun he=>hk 1 (by simpa [copyStack] using he.symm)
      exact Function.update_of_ne hn _ _

/-- Physical persistent tapes at the coefficient-controller boundary. -/
structure Cache where
  /-- Original first encoded coefficient vector. -/
  a : List Bool
  /-- Original second encoded coefficient vector. -/
  b : List Bool
  /-- Original physically encoded positive axes. -/
  axes : List Bool
  /-- Retained physical precision marker counter. -/
  width : List Bool
  /-- Retained physically acquired rank marker counter. -/
  rank : List Bool
  /-- Retained physical output-index marker counter. -/
  target : List Bool

/-- Clean loop invariant: only actual cached tapes, counters and accumulator live. -/
def resting (c : Cache) (i j acc : List Bool) : Stack → List Bool
  | .inr (.inl (.inr false)) => c.width
  | .inr (.inr (.inr .a)) => c.a
  | .inr (.inr (.inr .b)) => c.b
  | .inr (.inr (.inr .axes)) => c.axes
  | .inr (.inr (.inr .rank)) => c.rank
  | .inr (.inr (.inr .i)) => i
  | .inr (.inr (.inr .j)) => j
  | .inr (.inr (.inr .target)) => c.target
  | .inr (.inr (.inr .acc)) => acc
  | _ => []

/-- The actual two reader outputs occupy the real multiplier's input registers. -/
def loaded (c : Cache) (i j acc left right : List Bool) : Stack → List Bool :=
  Function.update (Function.update (resting c i j acc)
    (mulStack (.inl SemiprimeD1StackMultiplier.input)) left)
    (mulStack (.inl SemiprimeD1StackMultiplier.factor)) right

/-- The literal multiplier inclusion has disjoint registers. -/
theorem mulStack_injective : Function.Injective mulStack := by
  intro a b h
  simpa only [mulStack,Sum.inr.injEq,Sum.inl.injEq] using h

/-- Both cached vector reads feed the actual nested multiplier/reducer; no
native product or coefficient answer is supplied to the executed procedure. -/
theorem multiply_call (c : Cache) (i j acc left right : List Bool) :
    Runs program (SemiprimeD1StackJetScalarMulExecution.totalTime left right c.width+1)
      .multiply (loaded c i j acc left right) .add
      (Function.update (resting c i j acc) product
        (SemiprimeD1StackJetScalarMulExecution.result left right c.width)) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program mulStack Label.scalarMul
    mulStack_injective SemiprimeD1StackJetScalarMul.program .start (fun _=>rfl)
    .multiply .add rfl _
    (SemiprimeD1StackJetScalarMul.state (some .start) none none left right [] [] [] [] [] [] [] c.width [])
    (SemiprimeD1StackJetScalarMul.state none none none [] [] [] [] [] []
      (SemiprimeD1StackJetScalarMulExecution.result left right c.width) [] [] c.width [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackJetScalarMulExecution.source_run left right c.width
  · constructor
    · intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp [loaded,resting,mulStack,SemiprimeD1StackJetScalarMul.state,
            SemiprimeD1StackJetScalarMul.store,SemiprimeD1StackMultiplier.payload,
            SemiprimeD1StackMultiplier.input,SemiprimeD1StackMultiplier.factor]
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · intro k hk
      rfl
  · constructor
    · intro k
      rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp [resting,mulStack,product,SemiprimeD1StackJetScalarMul.reduceStack,
            SemiprimeD1StackJetScalarMul.state,SemiprimeD1StackJetScalarMul.store,
            SemiprimeD1StackMultiplier.payload]
        · rcases k with k|k
          · fin_cases k <;> rfl
          · cases k <;> rfl
      · cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> rfl
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl

/-- Outside its declared accumulator register the clean invariant is unchanged. -/
theorem resting_acc_other (c : Cache) (i j a b : List Bool) (k : Stack)
    (hk : k ≠ aux .acc) : resting c i j a k=resting c i j b k := by
  rcases k with k|k
  · cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | exact False.elim (hk rfl)

/-- The acquired product is consumed by the actual modular adder, preserving
all persistent cached input bytes and clearing both binary operands. -/
theorem add_call (c : Cache) (i j acc word : List Bool) :
    Runs program (SemiprimeD1StackJetScalarAddExecution.totalTime word acc c.width+1)
      .add (Function.update (resting c i j acc) product word) .retain
      (Function.update (resting c i j []) newAcc
        (SemiprimeD1StackJetScalarAddExecution.result word acc c.width)) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program addStack Label.scalarAdd
    addStack_injective SemiprimeD1StackJetScalarAdd.program .start (fun _=>rfl)
    .add .retain rfl _
    (SemiprimeD1StackJetScalarAdd.state (some .start) none none word acc [] [] c.width [])
    (SemiprimeD1StackJetScalarAdd.state none none none [] [] []
      (SemiprimeD1StackJetScalarAddExecution.result word acc c.width) c.width [])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackJetScalarAddExecution.source_run word acc c.width
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> simp [addStack,product,newAcc,addBank,aux,resting,mulStack,SemiprimeD1StackJetScalarMul.reduceStack,
          SemiprimeD1StackJetScalarAdd.state,SemiprimeD1StackJetScalarAdd.store]
      · cases k <;> rfl
    · intro k hk
      rfl
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> simp [addStack,product,newAcc,addBank,aux,resting,mulStack,SemiprimeD1StackJetScalarMul.reduceStack,
          SemiprimeD1StackJetScalarAdd.state,SemiprimeD1StackJetScalarAdd.store]
      · cases k <;> rfl
    · intro k hk
      have hprod : k ≠ product := fun he=>hk (.inl .left) he.symm
      have hnew : k ≠ newAcc := fun he=>hk (.inl .output) he.symm
      have hacc : k ≠ aux .acc := fun he=>hk (.inl .right) he.symm
      rw [Function.update_of_ne hnew,Function.update_of_ne hprod]
      exact resting_acc_other c i j [] acc k hacc

/-- Clearing the real temporary sum consumes every physical output cell. -/
theorem clear_new (data : Stack → List Bool) (he : data newAcc=[]) (word : List Bool) :
    Runs program (word.length+1) .clearNew (Function.update data newAcc word) .inner data := by
  induction word with
  | nil =>
    have hd : Function.update data newAcc []=data := by
      rw [←he,Function.update_eq_self]
    rw [hd]
    apply one_base program .clearNew .inner (.pop newAcc .inner .clearNew .clearNew) data data rfl
    · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose,he]
    · simpa only [SemiprimeD1StackBytecode.execute,he,List.tail_nil] using hd
  | cons bit word ih =>
    have hs : Runs program 1 .clearNew (Function.update data newAcc (bit::word)) .clearNew
        (Function.update data newAcc word) := by
      apply one_base program .clearNew .clearNew (.pop newAcc .inner .clearNew .clearNew) _ _ rfl
      · cases bit <;> simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
      · simp [SemiprimeD1StackBytecode.execute]
    have hh:=runs_trans program _ _ _ _ _ _ _ _ hs ih
    simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

/-- Literal accumulator replacement in the clean physical state. -/
theorem resting_acc_update (c : Cache) (i j a b : List Bool) :
    Function.update (resting c i j a) (aux .acc) b=resting c i j b := by
  funext k
  by_cases hk : k=aux .acc
  · subst k
    rfl
  · rw [Function.update_of_ne hk]
    exact resting_acc_other c i j a b k hk

/-- Actual copyback and temporary cleanup, with no silently discarded result. -/
theorem retain_call (c : Cache) (i j word : List Bool) :
    Runs program (6*word.length+5) .retain
      (Function.update (resting c i j []) newAcc word) .inner (resting c i j word) := by
  have hcopy:=copy_call .accumulator .retain .clearNew
    (Function.update (resting c i j []) newAcc word) rfl (by rfl) (by rfl)
  have hsource : (Function.update (resting c i j []) newAcc word) (copySource .accumulator)=word := rfl
  rw [hsource] at hcopy
  have hne : newAcc ≠ aux .acc := by decide
  have hdata : Function.update (Function.update (resting c i j []) newAcc word) (copyTarget .accumulator) word=
      Function.update (resting c i j word) newAcc word := by
    change Function.update (Function.update (resting c i j []) newAcc word) (aux .acc) word=_
    rw [Function.update_comm hne,resting_acc_update]
  rw [hdata] at hcopy
  have hclear:=clear_new (resting c i j word) (by rfl) word
  have hh:=runs_trans program _ _ _ _ _ _ _ _ hcopy hclear
  simpa only [show (5*word.length+4)+(word.length+1)=6*word.length+5 by omega] using hh

/-- Exact retained transition count of the linked binary arithmetic path. -/
def pipelineTime (left right acc width : List Bool) : ℕ :=
  let product:=SemiprimeD1StackJetScalarMulExecution.result left right width
  let sum:=SemiprimeD1StackJetScalarAddExecution.result product acc width
  (SemiprimeD1StackJetScalarMulExecution.totalTime left right width+1)+
    (SemiprimeD1StackJetScalarAddExecution.totalTime product acc width+1)+(6*sum.length+5)

/-- Complete actual product/sum/copyback path inside the coefficient loop.
Every arithmetic result is obtained from its literal linked finite procedure. -/
theorem pipeline_run (c : Cache) (i j acc left right : List Bool) :
    Runs program (pipelineTime left right acc c.width) .multiply (loaded c i j acc left right) .inner
      (resting c i j (SemiprimeD1StackJetScalarAddExecution.result
        (SemiprimeD1StackJetScalarMulExecution.result left right c.width) acc c.width)) := by
  exact runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (multiply_call c i j acc left right)
      (add_call c i j acc (SemiprimeD1StackJetScalarMulExecution.result left right c.width)))
    (retain_call c i j _)

/-- A fixed polynomial for every executed binary arithmetic path. -/
def pipelineBudget (left right acc precision : ℕ) : ℕ :=
  2000*(left+right+precision+3)^3+30*(2*precision+acc+2)+6*precision+7

/-- The concrete linked scalar path has no external clock or fit premise. -/
theorem pipelineTime_le (left right acc width : List Bool) :
    pipelineTime left right acc width ≤ pipelineBudget left.length right.length acc.length width.length := by
  have hm:=SemiprimeD1StackJetScalarMulExecution.totalTime_le left right width
  have hc:=SemiprimeD1StackJetScalarMulExecution.timeBound_le_cube left.length right.length width.length
  have ha:=SemiprimeD1StackJetScalarAddExecution.totalTime_le
    (SemiprimeD1StackJetScalarMulExecution.result left right width) acc width
  have hp : (SemiprimeD1StackJetScalarMulExecution.result left right width).length ≤ width.length :=
    SemiprimeD1JetScalarBits.mul_length _ _ _
  have hs : (SemiprimeD1StackJetScalarAddExecution.result
      (SemiprimeD1StackJetScalarMulExecution.result left right width) acc width).length ≤ width.length :=
    SemiprimeD1JetScalarBits.add_length _ _ _
  unfold SemiprimeD1StackJetScalarAddExecution.timeBound at ha
  dsimp only [pipelineTime,pipelineBudget]
  omega

end RiemannGaussian.SemiprimeD1StackJetPointExecution
