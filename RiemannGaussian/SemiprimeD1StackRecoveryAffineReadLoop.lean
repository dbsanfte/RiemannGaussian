/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadRow
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadMissing
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadCount
/-! # Actual EOF-limited coefficient traversal and literal legacy zero extension -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadLoop
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineReadBuffers SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryAffineReadCount (unary)
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join)
end T
/-- Exact byte-level zero-extended array interpretation, used only in proof statements. -/
def wordAt:List SemiprimeRationalBits.RationalWord→Nat→SemiprimeRationalBits.RationalWord
  | [],_=>SemiprimeRationalBits.zeroWord
  | x::_,0=>x
  | _::xs,n+1=>wordAt xs n
/-- Own sum of actual count/tag/parser/cache/tail/EOF steps, with no native-clock transport. -/
def runBound:List SemiprimeRationalBits.RationalWord→Nat→Nat
  | [],0=>6
  | [],n+1=>n+6
  | x::xs,0=>8*((signed x).length+x.denominator.length)+19+(vector xs).length
  | x::xs,n+1=>9*((signed x).length+x.denominator.length)+20+runBound xs n
/-- Every array access executes the actual finite parser/count loop and clears both private reader words. -/
theorem read_run (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (runBound xs n) (.local (.readCount part)) (bank (buffers w (vector xs) (unary n)))
      (.local (.factor part)) (bank (putReg (buffers w [] []) .numBase (wordAt xs n))):=by
  induction xs generalizing n with
  | nil=>
    cases n with
    | zero=>
      have h0:=SemiprimeD1StackRecoveryAffineReadCount.zero_run part w (vector [])
      have h1:=SemiprimeD1StackRecoveryAffineReadCount.eof_run part true w []
      have h2:=SemiprimeD1StackRecoveryAffineReadMissing.missing_run part w [] hn hd
      exact T.join (T.join h0 h1) h2
    | succ n=>
      have h0:=SemiprimeD1StackRecoveryAffineReadCount.succ_run part w (vector []) n
      have h1:=SemiprimeD1StackRecoveryAffineReadCount.eof_run part false w (unary n)
      have h2:=SemiprimeD1StackRecoveryAffineReadMissing.missing_run part w (unary n) hn hd
      have h:=T.join (T.join h0 h1) h2
      change Runs program (n+6) _ _ _ (bank (putReg (buffers w [] []) .numBase SemiprimeRationalBits.zeroWord))
      convert h using 1
      simp only [unary,List.length_replicate]
      omega
  | cons x xs ih=>
    cases n with
    | zero=>
      have h0:=SemiprimeD1StackRecoveryAffineReadCount.zero_run part w (vector (x::xs))
      have h1:=SemiprimeD1StackRecoveryAffineReadRow.take_run part w x (vector xs) [] hn hd hs hv
      have h:=T.join h0 h1
      change Runs program (8*((signed x).length+x.denominator.length)+19+(vector xs).length) _
        (bank (buffers w (vector (x::xs)) [])) _ (bank (putReg (buffers w [] []) .numBase x))
      convert h using 1
      omega
    | succ n=>
      have h0:=SemiprimeD1StackRecoveryAffineReadCount.succ_run part w (vector (x::xs)) n
      have h1:=SemiprimeD1StackRecoveryAffineReadRow.skip_run part w x (vector xs) (unary n) hn hd hs hv
      have h2:=ih n
      have h:=T.join (T.join h0 h1) h2
      change Runs program (9*((signed x).length+x.denominator.length)+20+runBound xs n) _ _ _
        (bank (putReg (buffers w [] []) .numBase (wordAt xs n)))
      convert h using 1
      omega
/-- Exact acquired-array bytes agree with the original array getter, including missing entries. -/
theorem wordAt_original (xs:List SemiprimeRationalBits.RationalWord) (n:Nat):
    wordAt xs n=SemiprimeJetBits.wordAt xs.toArray n:=by
  simp only [SemiprimeJetBits.wordAt,List.getElem?_toArray]
  induction xs generalizing n with
  | nil=>rfl
  | cons x xs ih=>cases n with
    | zero=>rfl
    | succ n=>exact ih n
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadLoop
