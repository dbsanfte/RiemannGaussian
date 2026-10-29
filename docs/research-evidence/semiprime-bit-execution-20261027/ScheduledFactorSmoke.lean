import RiemannGaussian.SemiprimeScheduledFactorExecution
open RiemannGaussian SemiprimeMacroGraph SemiprimeMacroParameters
open SemiprimePublicAcquiredExecution SemiprimeScheduledFactorExecution
private def signal : BitSignal (firstAxis (bitLength 1)) (secondAxis (bitLength 1)) (digitCount (bitLength 1)) :=
  .inl (.input ⟨0,by decide⟩ ⟨0,by decide⟩,⟨0,by decide⟩)
private def equalityIndex := (vertexEnumeration 1).equivFin.symm (.inr signal)
#eval ((indexedEntry 1 (by decide) equalityIndex (fun _ => false)).accepted,
  (indexedEntry 1 (by decide) equalityIndex (fun _ => false)).clock)
#eval ((indexedEntry 1 (by decide) equalityIndex (fun i => decide (i.val=0))).accepted,
  (indexedEntry 1 (by decide) equalityIndex (fun i => decide (i.val=0))).clock)
#eval SemiprimeAcquiredPrefixSearch.selectedBits [(⟨0,by decide⟩,true),(⟨1,by decide⟩,false)] (⟨0,by decide⟩ : Fin 2)
#eval (run 0,run 1,run 2,run 9,run 15)
#eval (decide (fastGuard 1),decide (fastGuard 2),decide (fastGuard 9))
