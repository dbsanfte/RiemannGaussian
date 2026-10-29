import RiemannGaussian.SemiprimeNativeInputBits
open RiemannGaussian
open SemiprimeRationalWordAcquisition
open SemiprimeRationalBits
-- Structural endpoint/denominator controls; not a factoring benchmark.
#eval ((encode 3 (-8)).word.value,(encode 3 (1/8)).word.value,
  (encode 3 (1/8)).stages,(encode 3 (1/8)).work)
-- Actual original search -> source array -> encoded source cache, one trivial cell.
#eval let arity : Fin 1 → Nat := fun _ => 1
  let en := SemiprimeFiniteEnumerations.indexed 1 1 1 1 arity
  let owner := fun _ : (e : Fin 1) × Fin (arity e) => (0 : Fin 1)
  let out := SemiprimeSourceWordAcquisition.acquire owner Sigma.fst en 1 0 1
  (out.words.map (fun a => a.map (fun row => row.map RationalWord.value)),
    out.sourceWork,out.encodingWork,out.work)
