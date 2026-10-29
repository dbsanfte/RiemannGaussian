import RiemannGaussian.SemiprimeRowSelectionBits
set_option autoImplicit false
set_option maxRecDepth 10000
open RiemannGaussian
open SemiprimeRationalBits SemiprimeRowSelectionBits SemiprimeMaterializedSelectionTemporaries

def one : RationalWord := ⟨⟨false,[true]⟩,[true]⟩
def minusZero : RationalWord := ⟨⟨true,[false,false]⟩,[true]⟩

-- Actual complete physical loop, including dot arithmetic and pivot normalization.
-- Controls are not factoring-success or scaling evidence.
#eval (let out := SemiprimeRowSelectionBits.run (m := 2) 1 (List.replicate (selectorWidth 1 0) false) [[zeroWord],[one]] (List.finRange 2); (out.state.selected.map Fin.val,out.clock,out.state.rows.map List.length))

-- Physical numerator scans correctly ignore a signed padded zero.
#eval ((scan [minusZero,one] (List.finRange 2)).pivot.map Fin.val)

-- Entire zero-column loop, with actual input-row reads and no hidden pivot.
#eval (let out := SemiprimeRowSelectionBits.run (m := 2) 0 (List.replicate (selectorWidth 0 0) false) [[],[]] (List.finRange 2); (out.state.selected.map Fin.val,out.clock,out.state.rows.length))
