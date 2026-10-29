import RiemannGaussian.SemiprimeWordFoldBounds
open RiemannGaussian SemiprimeRationalBits SemiprimeJetBits SemiprimeWordFoldArithmetic
private def template := List.replicate 8 false
private def body : JetReport := ⟨#[oneWord,negOneWord],7⟩
private def callback (i : Fin 3) : JetReport := if i.val=1 then scale template 2 body true else body
#eval decode (sumCodes template 2 3 callback).words
#eval decode (gate 2 ⟨false,11⟩ (fun _ => body)).words
#eval (gate 2 ⟨false,11⟩ (fun _ => body)).clock
#eval decode (gate 2 ⟨true,11⟩ (fun _ => body)).words
#eval (gate 2 ⟨true,11⟩ (fun _ => body)).clock
#eval decode (productList template 2 [0,1] (fun (_ : Nat) => body)).words
