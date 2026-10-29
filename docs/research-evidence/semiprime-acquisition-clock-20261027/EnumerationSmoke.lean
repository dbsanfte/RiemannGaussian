import RiemannGaussian.SemiprimePaidFiniteEnumerations
open RiemannGaussian
#eval show (List (Nat × Nat)) × Nat × List (List Nat) × Nat × Nat × Nat from Id.run do
  let result := SemiprimePaidFiniteEnumerations.indexed 2 2 2 2
    (fun e => if e.val=0 then 1 else 2)
  let data := result.value
  return (data.incidences.values.map (fun i => (i.1.val,i.2.val)),
    data.types.values.length,
    data.wordTail.map (fun w => (List.finRange 2).map (fun i => (w i).val)),
    data.terms.values.length,data.indices.values.length,result.work)
