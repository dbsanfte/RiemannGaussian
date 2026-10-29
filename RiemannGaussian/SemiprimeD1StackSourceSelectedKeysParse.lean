/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysView
/-! # Actual pair-tag/two-field occurrence parser and both true-validity pops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysParse
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysPrimitives SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Records
export SemiprimeD1StackOwnerLookup (records)
end Records
/-- The original pair tag, both endpoint key fields and both validity singletons are all physically consumed. -/
theorem read_row (i:Inputs) (own fac hist:List Bool) (rows:List (List Bool×List Bool)) :
    Runs program (8*(own.length+fac.length)+17) .header
      (view i [] [] [] (Records.records ((own,fac)::rows) []) [] [] [] [] [] [] hist []) (.copyQuery .owner)
      (view i [] [] [] (Records.records rows []) own fac [] [] [] [] hist []) :=by
  have h0:=pop_run .header .abort .eof (.parse .owner) (aux .reader)
    (view i [] [] [] (Records.records ((own,fac)::rows) []) [] [] [] [] [] [] hist [])
    (true::frame own (frame fac (Records.records rows []))) rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (view i [] [] [] (Records.records ((own,fac)::rows) []) [] [] [] [] [] [] hist [])
      (aux .reader) (frame own (frame fac (Records.records rows [])))) at h0
  rw [update_reader] at h0
  have h1:=parse_call .owner (view i [] [] [] (frame own (frame fac (Records.records rows []))) [] [] [] [] [] [] hist [])
    own (frame fac (Records.records rows [])) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (Function.update
    (view i [] [] [] (frame own (frame fac (Records.records rows []))) [] [] [] [] [] [] hist [])
      (aux .reader) (frame fac (Records.records rows []))) (aux .ownerKey) own) (aux .valid) [true]) at h1
  rw [update_reader,update_own,update_valid] at h1
  have h2:=pop_run (.valid .owner) .abort .abort (.parse .factor) (aux .valid)
    (view i [] [] [] (frame fac (Records.records rows [])) own [] [] [] [true] [] hist []) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (view i [] [] [] (frame fac (Records.records rows [])) own [] [] [] [true] [] hist []) (aux .valid) []) at h2
  rw [update_valid] at h2
  have h3:=parse_call .factor (view i [] [] [] (frame fac (Records.records rows [])) own [] [] [] [] [] hist [])
    fac (Records.records rows []) rfl rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update (Function.update
    (view i [] [] [] (frame fac (Records.records rows [])) own [] [] [] [] [] hist [])
      (aux .reader) (Records.records rows [])) (aux .factorKey) fac) (aux .valid) [true]) at h3
  rw [update_reader,update_fac,update_valid] at h3
  have h4:=pop_run (.valid .factor) .abort .abort (.copyQuery .owner) (aux .valid)
    (view i [] [] [] (Records.records rows []) own fac [] [] [true] [] hist []) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update
    (view i [] [] [] (Records.records rows []) own fac [] [] [true] [] hist []) (aux .valid) []) at h4
  rw [update_valid] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  have ht:1+(8*own.length+7)+1+(8*fac.length+7)+1=8*(own.length+fac.length)+17:=by omega
  simpa only [ht,SemiprimeD1StackBytecode.choose,List.head?_cons] using h
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysParse
