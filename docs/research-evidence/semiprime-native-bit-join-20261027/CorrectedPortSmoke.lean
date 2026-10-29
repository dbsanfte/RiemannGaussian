import RiemannGaussian.SemiprimeCorrectedPortBitsBounds
open RiemannGaussian SemiprimeRationalBits SemiprimeJetBits SemiprimeCorrectedPortBits
private def twoWord : RationalWord := ⟨⟨false,[false,true]⟩,[true]⟩
private def source : Fin 1 → Array RationalWord := fun _ => #[oneWord,twoWord]
private def template := List.replicate 8 false
#eval decode (shiftRow template (source 0) twoWord 1 3).words
#eval decode (acquireCorrectedFin template source twoWord 1 3 (fun _ => false) (fun _ => true)).words
#eval (acquireCorrectedFin template source twoWord 1 3 (fun _ => true) (fun _ => true)).clock
