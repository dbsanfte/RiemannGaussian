import RiemannGaussian.SemiprimeAcquiredHermiteBits
open RiemannGaussian
open SemiprimeJetBits SemiprimeAcquiredHermiteBits
-- Exact tiny interpolation controls, without any factoring/coverage campaign.
#eval (reconstruct (List.replicate 20 false) 0 1 (fun t => Fin.elim0 t)).word.value
#eval (reconstruct (List.replicate 20 false) 1 2 (fun _ => ⟨#[oneWord,oneWord],9⟩)).word.value
#eval (reconstruct (List.replicate 20 false) 2 1
  (fun t => ⟨#[if t.val=0 then oneWord else negOneWord],9⟩)).word.value
#eval (reconstruct (List.replicate 20 false) 2 1
  (fun t => ⟨#[if t.val=0 then oneWord else negOneWord],9⟩)).clock
