/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCounter
/-! # Reusable actual binary increment entry with a genuine final return -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCounterEntry
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyCounter
open SemiprimeD1StackProcedureTrace
/-- Only the actual input word and fresh seven counter operands constrain this real-ret entry; all other physical words are retained. -/
theorem source_run (before:Stack→List Bool) (word:List Bool)
    (hw:before oldCount=word) (hn:before (aux .incNext)=[])
    (hi:before (aux .incScratch)=[]) (ht:before (aux .trimScratch)=[])
    (ho:before (aux .count)=[]) (hc:before (lookupStack (.inl .left))=[]) (hf:before (lookupStack (.inl .right))=[]) :
    ∃q≤40*(word.length+1)+1,SemiprimeD1StackCalls.run program q
      (⟨some .increment,none,none,before,[]⟩:C.State Stack Label)=some
      ⟨none,none,none,Function.update (Function.update before oldCount []) (aux .count)
        (SemiprimeD1StackSourceEnvironmentEncoding.successor word),[]⟩ :=by
  obtain ⟨q,hq,hr⟩:=counter_run before word hw hn hi ht ho hc hf
  obtain ⟨finish,hfin,hAt⟩:=hr [] ⟨some .increment,none,none,before,[]⟩ ⟨rfl,rfl,rfl⟩
  refine ⟨q+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
  change SemiprimeD1StackCalls.step program finish=_
  simp only [SemiprimeD1StackCalls.step,hAt.1,Option.map_some,program,SemiprimeD1StackCalls.execute,hAt.2.1,hAt.2.2]
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCounterEntry
