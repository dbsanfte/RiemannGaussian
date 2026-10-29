import RiemannGaussian.SemiprimeMacroEntryBitCheck
open RiemannGaussian.SemiprimeMacroEntryBitCheck
open RiemannGaussian.SemiprimeMacroGraph
#eval (publicBitEntry 15 (by decide) (.inputCheck 0) (fun _ => true)).accepted
#eval (publicBitEntry 15 (by decide) (.inputCheck 0) (fun _ => false)).accepted
#eval (publicBitEntry 15 (by decide) (.input 0 ⟨0,by decide⟩) (fun _ => false)).accepted
#eval (publicBitEntry 15 (by decide) (.first (.inl 0) ⟨0,by decide⟩) (fun _ => false)).accepted
#eval (publicBitEntry 15 (by decide) (.second (.inr ()) ⟨0,by decide⟩) (fun _ => false)).accepted
#eval (publicBitEntry 15 (by decide) (.product ⟨0,by decide⟩) (fun _ => true)).accepted
#eval (publicBitEntry 15 (by decide) (.carry ⟨0,by decide⟩) (fun i => decide (i.val<2))).accepted
#eval (publicBitEntry 15 (by decide) (.carry ⟨0,by decide⟩) (fun _ => false)).accepted
