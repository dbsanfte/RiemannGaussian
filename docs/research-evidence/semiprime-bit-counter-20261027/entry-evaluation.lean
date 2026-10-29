import RiemannGaussian.SemiprimeMacroEntryExecution
open RiemannGaussian.SemiprimeMacroEntryExecution
open RiemannGaussian.SemiprimeMacroGraph
#eval binaryDecode (fun i : Fin 4 => i.val=0 || i.val=3)
#eval (decodeRun (fun i : Fin 4 => i.val=0 || i.val=3))
#eval publicEntry 15 (by decide) (.inputCheck 0) (fun _ => true)
#eval publicEntry 15 (by decide) (.inputCheck 0) (fun _ => false)
#eval publicEntry 15 (by decide) (.first (.inl 0) ⟨0,by decide⟩) (fun _ => false)
#eval publicEntry 15 (by decide) (.second (.inr ()) ⟨0,by decide⟩) (fun _ => false)
