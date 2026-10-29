import RiemannGaussian.SemiprimeEncodedRowSelection
set_option autoImplicit false
set_option maxRecDepth 10000
open RiemannGaussian SemiprimeEncodedRowSelection

-- Exact inclusive endpoints and negative sign, from actual scalar extraction.
#eval ([((0 : ℤ),0),(-1,0),(4,2),(-4,2)].map fun p => let out := encode p.2 p.1; (out.word.numerator.negative,out.word.numerator.magnitude,out.word.value,out.stages,out.work))

-- Actual integer-input -> encoded cache -> physical selector; no word advice.
#eval (let out := select (m := 1) (n := 1) (fun _ _ => (⟨-1,7⟩ : IntRun)) 0; (out.selected.map Fin.val,out.integers,out.sourceCalls,out.sourceWork,out.digitWork,out.preparationWork,out.selectorWork,out.work))

-- No callback can run when the column type is empty; both integer rows retained.
#eval (let out := select (m := 2) (n := 0) (fun _ v => Fin.elim0 v) 0; (out.selected.map Fin.val,out.integers,out.sourceCalls,out.work))
