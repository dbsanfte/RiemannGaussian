import RiemannGaussian.SemiprimeMaterializedSourceAcquisition
open RiemannGaussian OAI.Algorithms.SubexponentialSAT
#eval show (Array (Array (Array ℚ))) × ℕ from Id.run do
  let keys := (SemiprimeFiniteEnumerations.universal 2 1).values
  let fallback : MulticolorTypes.UniversalType 2 1 1 := ⟨fun _ => 0,fun _ _ => 0⟩
  let producer := fun i : Fin 4 =>
    (⟨(keys[i.val]?).getD fallback,i.val+1⟩ :
      SemiprimeMaterializedSourceUniversal.Run (MulticolorTypes.UniversalType 2 1 1))
  let out := SemiprimeMaterializedSourceAcquisition.acquire 1 (List.finRange 4)
    (fun _ : Fin 4 => (0 : Fin 1)) keys producer
  return (out.value,out.work)
