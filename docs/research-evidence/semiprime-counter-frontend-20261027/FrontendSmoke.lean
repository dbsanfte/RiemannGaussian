import RiemannGaussian.SemiprimeMacroFiniteEnumerations
import RiemannGaussian.SemiprimeMixedRadix
open RiemannGaussian
#eval (SemiprimeMacroFiniteEnumerations.words 1 4 1).values.length
#eval (SemiprimeMacroFiniteEnumerations.edges 1 4 1).values.length
#eval (SemiprimeMacroFiniteEnumerations.subdividedVertices 1 4 1).values.length
#eval (SemiprimeMacroFiniteEnumerations.incidences 1 4 1).values.length
#eval List.ofFn (fun i => (SemiprimeMixedRadix.decode 2 (fun i => if i.val=0 then 2 else 3) ⟨5,by decide⟩ i).val)
#eval (SemiprimeMixedRadix.nested 2 (fun _=>1) (fun _ _=>3)).symm (fun _ _=>⟨2,by decide⟩)
