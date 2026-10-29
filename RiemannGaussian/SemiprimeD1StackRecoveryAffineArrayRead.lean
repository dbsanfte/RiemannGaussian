/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadLoop
/-! # Whole actual array access includes both restoring copies and every real parser/EOF step -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineArrayRead
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineReadBuffers SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineReadCount (unary)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join copy_call)
end T
/-- The two real copies and same actual count/parser loop determine this own source clock. -/
def runBound (xs:List SemiprimeRationalBits.RationalWord) (n:Nat):Nat:=
  (5*(vector xs).length+4)+(5*n+4)+SemiprimeD1StackRecoveryAffineReadLoop.runBound xs n
/-- Actual array and actual byte-index remain retained; private reader/count words are again EMPTY. -/
theorem source_run (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (ha:w.added .array=vector xs) (hk:w.added .k=unary n)
    (hr:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[])
    (hc:w.auxiliary .copyScratch=[]) (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (runBound xs n) (.local (.inner part)) (bank w)
      (.local (.factor part)) (bank (putReg w .numBase (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs n))):=by
  have hself:buffers w [] []=w:=by simpa only [hr,ht] using buffers_self w
  have h0:=T.copy_call .array (.local (.inner part)) (.local (.readIndex part)) rfl
    (bank (buffers w [] [])) (vector xs) [] ha rfl hc
  change Runs program _ _ _ _ (Function.update (bank (buffers w [] [])) (aux .reader) (vector xs++[])) at h0
  rw [List.append_nil,update_reader] at h0
  have h1:=T.copy_call .readIndex (.local (.readIndex part)) (.local (.readCount part)) rfl
    (bank (buffers w (vector xs) [])) (unary n) [] hk rfl hc
  change Runs program _ _ _ _ (Function.update (bank (buffers w (vector xs) [])) (aux .readTodo) (unary n++[])) at h1
  rw [List.append_nil,update_todo] at h1
  have h2:=SemiprimeD1StackRecoveryAffineReadLoop.read_run part w xs n hn hd hs hv
  have h:=T.join (T.join h0 h1) h2
  rw [hself] at h
  simpa only [runBound,unary,List.length_replicate] using h
/-- The actual copied/read coefficient is exactly the authoritative zero-extended array byte word. -/
theorem source_run_original (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (ha:w.added .array=vector xs) (hk:w.added .k=unary n)
    (hr:w.added .reader=[]) (ht:w.added .readTodo=[])
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[])
    (hc:w.auxiliary .copyScratch=[]) (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (runBound xs n) (.local (.inner part)) (bank w)
      (.local (.factor part)) (bank (putReg w .numBase (SemiprimeJetBits.wordAt xs.toArray n))):=by
  rw [←SemiprimeD1StackRecoveryAffineReadLoop.wordAt_original]
  exact source_run part w xs n ha hk hr ht hn hd hc hs hv
end RiemannGaussian.SemiprimeD1StackRecoveryAffineArrayRead
