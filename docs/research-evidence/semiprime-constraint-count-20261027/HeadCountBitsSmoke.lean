import RiemannGaussian.SemiprimeSourceHeadCountBitsBounds
open RiemannGaussian
#eval let bank := SemiprimeSourceWordBank.acquire 2 1
  let powers := SemiprimeSourceCountPowers.acquire 2 1
  let env := (SemiprimeSourceWordIdEnvironment.initial SemiprimeSourceWordBank.defaultID bank.ids).value
  let q : Fin 1 := ⟨0,by decide⟩
  let out := [SemiprimeSourceHeadCountBits.count bank env powers q 0 0 [],
    SemiprimeSourceHeadCountBits.count bank env powers q 0 1 [0],
    SemiprimeSourceHeadCountBits.count bank env powers q 0 1 [],
    SemiprimeSourceHeadCountBits.count bank env powers q 2 3 []]
  (out.map (fun x => SemiprimeBitArithmetic.bitValue x.bits),out.all (fun x => decide (0 < x.clock)))
