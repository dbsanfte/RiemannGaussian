import RiemannGaussian.SemiprimeSourceCompactWordBank
open RiemannGaussian SemiprimeBitArithmetic

#eval let ids := SemiprimeSourceCompactWordIds.acquire 8
      (ids.value.map bitValue,ids.value.map List.length,ids.work)
#eval let bank := SemiprimeSourceCompactWordBank.acquire 2 2
      (bank.rows.map (fun row => row.map SemiprimeRationalBits.RationalWord.value),
       bank.ids.map bitValue,bank.ids.map List.length,bank.clock)
#eval let bank := SemiprimeSourceCompactWordBank.acquire 2 0
      (bank.rows.length,bank.ids,bank.clock)
#eval let bank := SemiprimeSourceCompactWordBank.acquire 1 3
      (bank.rows.length,bank.ids,bank.rows.map List.length)
