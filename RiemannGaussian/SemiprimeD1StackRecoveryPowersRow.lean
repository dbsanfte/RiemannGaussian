/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryPowersOperationOutput
/-! # Actual two-field rational row logging without accumulated-tail recopy -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryPowersRow
open SemiprimeD1StackRecoveryPowers
open SemiprimeD1StackRecoveryPowersView hiding Stack
open SemiprimeD1StackRecoveryPowersSpec (signed row)
open SemiprimeD1StackRecoveryPowersOperationInput SemiprimeD1StackProcedureTrace
/-- Exact elapsed cost of TWO real frames, the row tag and its consuming reverse. -/
def timeBound (x:SemiprimeRationalBits.RationalWord):Nat:=
  (6*x.denominator.length+5)+(6*(signed x).length+5)+1+(2*(row x).length+3)
/-- The row is logged in reverse while all actual input/current words are retained. -/
theorem row_run (w:Words) (x:SemiprimeRationalBits.RationalWord)
    (hn:w.added .currentSigned=signed x) (hd:w.added .currentDen=x.denominator)
    (hr:w.added .row=[]) (hs:w.added .frameScratch=[]):
    Runs program (timeBound x) (.local (.frame true)) (bank w) (.local .next)
      (bank (put w .history ((row x).reverse++w.added .history))):=by
  let framedDen:=SemiprimeSourceHistogramKeyBits.frame x.denominator []
  let framed:=SemiprimeSourceHistogramKeyBits.frame (signed x) framedDen
  let w1:=put w .row framedDen
  let w2:=put w1 .row framed
  let w3:=put w2 .row (row x)
  have h0:=PTrace.frame_call true (.local (.frame true)) (.local (.frame false)) rfl
    (bank w) x.denominator [] hd hr hs
  change Runs _ _ _ _ _ (Function.update (bank w) (aux .row) framedDen) at h0
  rw [update_added] at h0
  have h1:=PTrace.frame_call false (.local (.frame false)) (.local .tag) rfl
    (bank w1) (signed x) framedDen hn (by change w1.added .row=framedDen; simp [w1,put]) hs
  change Runs _ _ _ _ _ (Function.update (bank w1) (aux .row) framed) at h1
  rw [update_added] at h1
  have h2:=PTrace.push_run (.local .tag) (.local .log) (aux .row) true (bank w2) rfl
  rw [update_added] at h2
  have he:(true::w2.added .row)=row x:=rfl
  change Runs program 1 _ _ _ (bank (put w2 .row (true::w2.added .row))) at h2
  rw [he] at h2
  have h3:=PTrace.reverse_call false (.local .log) (.local .next) rfl
    (bank w3) (row x) (w.added .history) (by change w3.added .row=row x; simp [w3,put]) rfl
  change Runs _ _ _ _ _ (Function.update (Function.update (bank w3) (aux .row) [])
    (aux .history) ((row x).reverse++w.added .history)) at h3
  rw [update_added,update_added] at h3
  have hend:put (put w3 .row []) .history ((row x).reverse++w.added .history)=
      put w .history ((row x).reverse++w.added .history):=by
    dsimp only [put,w3,w2,w1]
    congr 1
    funext k
    cases k <;> simp [hr]
  change Runs program _ _ _ _ (bank (put (put w3 .row []) .history ((row x).reverse++w.added .history))) at h3
  rw [hend] at h3
  exact PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
/-- Actual row time is linear in the exact stored scalar field widths. -/
theorem timeBound_eq (x:SemiprimeRationalBits.RationalWord):
    timeBound x=10*x.numerator.magnitude.length+10*x.denominator.length+30:=by
  rw [timeBound,SemiprimeD1StackRecoveryPowersSpec.row_length]
  simp only [signed,List.length_cons]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryPowersRow
