import RiemannGaussian.SemiprimeCachedSourceCounter
open RiemannGaussian
#eval show ℚ × ℕ from Id.run do
  let result := SemiprimeCachedSourceCounter.count (n:=1) (F:=1) (r:=1) (Q:=1)
    (fun _ => 1) (fun _ _ => (0 : Fin 1)) (1 : ℚ) 0 2 1
    (fun _ input => (⟨if input 0 then 1 else 0,1,0⟩ : SemiprimeLocalArrayFrontend.EntryReport))
  return (result.value,result.work)
