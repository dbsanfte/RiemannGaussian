import RiemannGaussian.SemiprimeFiniteEnumerations
open RiemannGaussian.SemiprimeFiniteEnumerations
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
set_option autoImplicit false

def smokeWords := indexedWords 2 1 2 2 (fun _ => 2) (fun _ i => i) (1/4)
def smokePacking := indexedPacking 2 1 2 2 (fun _ => 2) (fun _ i => i) (1/4)
#eval (indexed 2 1 2 2 (fun _ => 2)).incidences.values.map (fun i => (i.1.val,i.2.val))
#eval (indexed 2 1 2 2 (fun _ => 2)).types.values.length
#eval (indexed 2 1 2 2 (fun _ => 2)).terms.values.length
#eval (fin 2).values.map (fun v => (fin 2).values.map (fun t => (smokeWords (.inl v) t).val))
#eval smokePacking.blockCount
#eval smokePacking.leftovers.map (fun i => (i.1.val,i.2.val))
