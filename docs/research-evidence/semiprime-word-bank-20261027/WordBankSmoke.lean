import RiemannGaussian.SemiprimeSourceWordBankIndexed
import RiemannGaussian.SemiprimeSourceWordBankAcquisitionBudget
open RiemannGaussian
#eval let bank := SemiprimeSourceWordBank.acquire 2 2
  (bank.rows.map (List.map SemiprimeRationalBits.RationalWord.value),
   bank.ids.map SemiprimeBitArithmetic.bitValue,
   (SemiprimeSourceWordBank.readRow bank (SemiprimeSourceOffsetInputsCore.natBits 2).bits).value.map
      SemiprimeRationalBits.RationalWord.value,
   decide (bank.clock > 0))
#eval let bank := SemiprimeSourceWordBank.acquire 1 0
  (bank.rows.map List.length,bank.ids.map SemiprimeBitArithmetic.bitValue)
