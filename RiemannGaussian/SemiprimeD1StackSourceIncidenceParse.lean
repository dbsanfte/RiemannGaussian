/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceLoopView
/-! # Actual two-field occurrence parsing and physically consumed validity flags -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceParse
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Records
export SemiprimeD1StackOwnerLookup (records)
end Records
/-- The actual inner reader consumes the pair tag, both complete endpoint frames and both true-valid singletons. -/
theorem read_inner (i:Inputs) (outer lo lf ro rf acc:List Bool) (rows:List (List Bool×List Bool)) :
    Runs program (8*(ro.length+rf.length)+17) .innerHeader (bank i outer (Records.records ((ro,rf)::rows) []) lo lf [] [] [] [] [] [] acc) .ownerCall
      (bank i outer (Records.records rows []) lo lf ro rf [] [] [] [] acc) :=by
  have h0:=pop_run .innerHeader .abort .innerEOF (.parse true .owner) (aux .innerReader)
    (bank i outer (Records.records ((ro,rf)::rows) []) lo lf [] [] [] [] [] [] acc) (true::frame ro (frame rf (Records.records rows []))) rfl rfl
  change Runs program 1 _ _ _ (Function.update (bank i outer (Records.records ((ro,rf)::rows) []) lo lf [] [] [] [] [] [] acc) (aux .innerReader) (frame ro (frame rf (Records.records rows [])))) at h0
  rw [update_inner] at h0
  have h1:=parse_call true .owner (bank i outer (frame ro (frame rf (Records.records rows []))) lo lf [] [] [] [] [] [] acc) ro (frame rf (Records.records rows [])) rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update (bank i outer (frame ro (frame rf (Records.records rows []))) lo lf [] [] [] [] [] [] acc) (aux .innerReader) (frame rf (Records.records rows [])))
      (aux .ownerRight) ro) (aux .valid) [true]) at h1
  rw [update_inner,update_ro,update_valid] at h1
  have h2:=pop_run (.valid true .owner) .abort .abort (.parse true .factor) (aux .valid)
    (bank i outer (frame rf (Records.records rows [])) lo lf ro [] [true] [] [] [] acc) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (bank i outer (frame rf (Records.records rows [])) lo lf ro [] [true] [] [] [] acc) (aux .valid) []) at h2
  rw [update_valid] at h2
  have h3:=parse_call true .factor (bank i outer (frame rf (Records.records rows [])) lo lf ro [] [] [] [] [] acc) rf (Records.records rows []) rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update (bank i outer (frame rf (Records.records rows [])) lo lf ro [] [] [] [] [] acc) (aux .innerReader) (Records.records rows []))
      (aux .factorRight) rf) (aux .valid) [true]) at h3
  rw [update_inner,update_rf,update_valid] at h3
  have h4:=pop_run (.valid true .factor) .abort .abort .ownerCall (aux .valid)
    (bank i outer (Records.records rows []) lo lf ro rf [true] [] [] [] acc) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (bank i outer (Records.records rows []) lo lf ro rf [true] [] [] [] acc) (aux .valid) []) at h4
  rw [update_valid] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have he:1+(8*ro.length+7)+1+(8*rf.length+7)+1=8*(ro.length+rf.length)+17:=by omega
  simpa only [he,SemiprimeD1StackBytecode.choose,List.head?_cons] using h
/-- The actual outer reader consumes the pair tag, both complete endpoint frames and both true-valid singletons. -/
theorem read_outer (i:Inputs) (lo lf acc:List Bool) (rows:List (List Bool×List Bool)) :
    Runs program (8*(lo.length+lf.length)+17) .outerHeader (bank i (Records.records ((lo,lf)::rows) []) [] [] [] [] [] [] [] [] [] acc) .copyInner
      (bank i (Records.records rows []) [] lo lf [] [] [] [] [] [] acc) :=by
  have h0:=pop_run .outerHeader .abort .outerEOF (.parse false .owner) (aux .outerReader)
    (bank i (Records.records ((lo,lf)::rows) []) [] [] [] [] [] [] [] [] [] acc) (true::frame lo (frame lf (Records.records rows []))) rfl rfl
  change Runs program 1 _ _ _ (Function.update (bank i (Records.records ((lo,lf)::rows) []) [] [] [] [] [] [] [] [] [] acc) (aux .outerReader) (frame lo (frame lf (Records.records rows [])))) at h0
  rw [update_outer] at h0
  have h1:=parse_call false .owner (bank i (frame lo (frame lf (Records.records rows []))) [] [] [] [] [] [] [] [] [] acc) lo (frame lf (Records.records rows [])) rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update (bank i (frame lo (frame lf (Records.records rows []))) [] [] [] [] [] [] [] [] [] acc) (aux .outerReader) (frame lf (Records.records rows [])))
      (aux .ownerLeft) lo) (aux .valid) [true]) at h1
  rw [update_outer,update_lo,update_valid] at h1
  have h2:=pop_run (.valid false .owner) .abort .abort (.parse false .factor) (aux .valid)
    (bank i (frame lf (Records.records rows [])) [] lo [] [] [] [true] [] [] [] acc) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (bank i (frame lf (Records.records rows [])) [] lo [] [] [] [true] [] [] [] acc) (aux .valid) []) at h2
  rw [update_valid] at h2
  have h3:=parse_call false .factor (bank i (frame lf (Records.records rows [])) [] lo [] [] [] [] [] [] [] acc) lf (Records.records rows []) rfl rfl rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update (bank i (frame lf (Records.records rows [])) [] lo [] [] [] [] [] [] [] acc) (aux .outerReader) (Records.records rows []))
      (aux .factorLeft) lf) (aux .valid) [true]) at h3
  rw [update_outer,update_lf,update_valid] at h3
  have h4:=pop_run (.valid false .factor) .abort .abort .copyInner (aux .valid)
    (bank i (Records.records rows []) [] lo lf [] [] [true] [] [] [] acc) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (bank i (Records.records rows []) [] lo lf [] [] [true] [] [] [] acc) (aux .valid) []) at h4
  rw [update_valid] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have he:1+(8*lo.length+7)+1+(8*lf.length+7)+1=8*(lo.length+lf.length)+17:=by omega
  simpa only [he,SemiprimeD1StackBytecode.choose,List.head?_cons] using h
end RiemannGaussian.SemiprimeD1StackSourceIncidenceParse
