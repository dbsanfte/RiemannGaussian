/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCopies
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCompaction
/-! # Physical S-minus-root and S-plus-root halves, including borrow/parity pops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryHalves
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackPackedFactorRecoveryCopies (adder_left adder_right)
end P
/-- All acquired metadata and root output are retained throughout both real numerators. -/
def phase (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (root small large : List Bool) (a : A.Stack→List Bool) : Stack→List Bool :=
  view r m a (fun _=>[]) (fun _=>[]) (SemiprimeD1StackBinarySquareRootEncoding.words [] root)
    (words small large [] [])
/-- The actual frozen square-root halt is exactly this clean retained-root phase. -/
theorem phase_result (r : R.Stack→List Bool) (d : List Bool) :
    phase r (SemiprimeD1StackBinarySquareRootEncoding.retained d [])
      (SemiprimeD1StackBinarySquareRootArithmetic.output d) [] [] (A.store [] [] [] [])=
      bank r (SemiprimeD1StackBinarySquareRootEncoding.result d) (words [] [] [] []) := by
  funext k
  rcases k with k|k|k
  · rfl
  · rcases k with k|k|k|k|k
    · rfl
    · cases k <;> rfl
    · rfl
    · rfl
    · rfl
  · rfl
/-- Own exact lower-half cost, including both actual FALSE pops and output drain. -/
def minusTime (s root lo : List Bool) : ℕ :=
  (5*s.length+4)+(5*root.length+4)+subtractTime s root+1+1+(5*lo.length+4)+(lo.length+1)
/-- Actual lower numerator, borrow read, parity pop, copy and drain retain every cache. -/
theorem minus_run (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (s root lo : List Bool) (hs : r (R.aux .sum)=s)
    (hb : (minusReport s root).borrow=false) (hn : (minusReport s root).result.bits=false::lo) :
    Runs program (minusTime s root lo) (ctl (.copy .minusLeft)) (phase r m root [] [] (A.store [] [] [] []))
      (ctl (.copy .plusLeft)) (phase r m root lo [] (A.store [] [] [] [])) := by
  let x : X.Stack→List Bool:=fun _=>[]
  let w : W.Stack→List Bool:=fun _=>[]
  let v:=SemiprimeD1StackBinarySquareRootEncoding.words [] root
  let u:=words [] [] [] []
  have h0:=P.adder_left .minusLeft (ctl (.copy .minusLeft)) (ctl (.copy .minusRight))
    r m x w v u [] [] [] [] s rfl rfl hs rfl
  simp only [List.append_nil] at h0
  have h1:=P.adder_right .minusRight (ctl (.copy .minusRight)) (ctl .minus)
    r m x w v u s [] [] [] root rfl rfl rfl rfl
  simp only [List.append_nil] at h1
  have h2:=subtract_call r m x w v u s root (ctl .minus) (ctl .minusBorrow) rfl
  change Runs program _ _ _ _ (phase r m root [] [] (A.store [] [] [] ((minusReport s root).borrow::(minusReport s root).result.bits))) at h2
  rw [hb,hn] at h2
  have h3:=pop_false (ctl .minusBorrow) (ctl .minusParity) (ctl (.abort 0)) (ctl (.abort 0))
    (adder .output) (phase r m root [] [] (A.store [] [] [] (false::false::lo))) (false::lo) rfl rfl
  rw [phase,view_adder,SemiprimeD1StackAdder.store_output] at h3
  have h4:=pop_false (ctl .minusParity) (ctl (.copy .small)) (ctl (.abort 0)) (ctl (.abort 0))
    (adder .output) (phase r m root [] [] (A.store [] [] [] (false::lo))) lo rfl rfl
  rw [phase,view_adder,SemiprimeD1StackAdder.store_output] at h4
  have h5:=copy_call .small (ctl (.copy .small)) (ctl .clearMinus) rfl
    (phase r m root [] [] (A.store [] [] [] lo)) lo [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .small) (lo++[])) at h5
  rw [List.append_nil,phase,view_aux,words_update] at h5
  have h6:=drain_call (ctl .clearMinus) (ctl (.copy .plusLeft)) (adder .output)
    (phase r m root lo [] (A.store [] [] [] lo)) lo rfl rfl
  rw [phase,view_adder,SemiprimeD1StackAdder.store_output] at h6
  exact join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6
/-- Own exact upper-half cost includes its actual parity pop and every cleanup cell. -/
def plusTime (s root hi : List Bool) : ℕ :=
  (5*s.length+4)+(5*root.length+4)+addTime s root+1+(5*hi.length+4)+(hi.length+1)
/-- Actual upper numerator and low-bit pop, preserving the already acquired lower half. -/
theorem plus_run (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (s root lo hi : List Bool) (hs : r (R.aux .sum)=s) (hn : plusWord s root=false::hi) :
    Runs program (plusTime s root hi) (ctl (.copy .plusLeft)) (phase r m root lo [] (A.store [] [] [] []))
      (ctl (.reverse false)) (phase r m root lo hi (A.store [] [] [] [])) := by
  let x : X.Stack→List Bool:=fun _=>[]
  let w : W.Stack→List Bool:=fun _=>[]
  let v:=SemiprimeD1StackBinarySquareRootEncoding.words [] root
  let u:=words lo [] [] []
  have h0:=P.adder_left .plusLeft (ctl (.copy .plusLeft)) (ctl (.copy .plusRight))
    r m x w v u [] [] [] [] s rfl rfl hs rfl
  simp only [List.append_nil] at h0
  have h1:=P.adder_right .plusRight (ctl (.copy .plusRight)) (ctl .plus)
    r m x w v u s [] [] [] root rfl rfl rfl rfl
  simp only [List.append_nil] at h1
  have h2:=add_call r m x w v u s root (ctl .plus) (ctl .plusParity) rfl
  change Runs program _ _ _ _ (phase r m root lo [] (A.store [] [] [] (plusWord s root))) at h2
  rw [hn] at h2
  have h3:=pop_false (ctl .plusParity) (ctl (.copy .large)) (ctl (.abort 0)) (ctl (.abort 0))
    (adder .output) (phase r m root lo [] (A.store [] [] [] (false::hi))) hi rfl rfl
  rw [phase,view_adder,SemiprimeD1StackAdder.store_output] at h3
  have h4:=copy_call .large (ctl (.copy .large)) (ctl .clearPlus) rfl
    (phase r m root lo [] (A.store [] [] [] hi)) hi [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .large) (hi++[])) at h4
  rw [List.append_nil,phase,view_aux,words_update] at h4
  have h5:=drain_call (ctl .clearPlus) (ctl (.reverse false)) (adder .output)
    (phase r m root lo hi (A.store [] [] [] hi)) hi rfl rfl
  rw [phase,view_adder,SemiprimeD1StackAdder.store_output] at h5
  exact join (join (join (join (join h0 h1) h2) h3) h4) h5
/-- Both physically obtained halves are actually compacted before validation. -/
theorem compact_run (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (root lo hi : List Bool) (hp : m (SemiprimeD1StackPackedRootMetadata.aux .base)=[]) :
    Runs program (SemiprimeD1StackPackedFactorRecoveryCompaction.time lo+SemiprimeD1StackPackedFactorRecoveryCompaction.time hi)
      (ctl (.reverse false)) (phase r m root lo hi (A.store [] [] [] []))
      (ctl (.copy .checkSmall))
      (phase r m root (SemiprimeD1StackReduceExecution.trimReverse lo.reverse)
        (SemiprimeD1StackReduceExecution.trimReverse hi.reverse) (A.store [] [] [] [])) := by
  have h0:=SemiprimeD1StackPackedFactorRecoveryCompaction.compact_call false
    (phase r m root lo hi (A.store [] [] [] [])) lo rfl hp rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .small) _) at h0
  rw [phase,view_aux,words_update] at h0
  have h1:=SemiprimeD1StackPackedFactorRecoveryCompaction.compact_call true
    (phase r m root (SemiprimeD1StackReduceExecution.trimReverse lo.reverse) hi (A.store [] [] [] [])) hi rfl hp rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .large) _) at h1
  rw [phase,view_aux,words_update] at h1
  exact join h0 h1
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryHalves
