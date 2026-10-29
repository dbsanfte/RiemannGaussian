import RiemannGaussian.SemiprimeSourceWordIdCountsClock
open RiemannGaussian SemiprimeBitArithmetic
open SemiprimeMaterializedScoreEnvironment (ScoreProgram)
-- Pure acquired-bank/Boolean-ID runtime: no source Word function is constructed.
def programs : List (ScoreProgram 1) := [.incidence 0 1 0 1,.head 0 0 1]
#eval let bank:=SemiprimeSourceWordBank.acquire 2 1
      let out:=SemiprimeSourceWordIdCounts.sequential bank [] programs 2 []
      (bitValue out.incidence,bitValue out.head)
#eval let bank:=SemiprimeSourceWordBank.acquire 2 1
      let weights:=SemiprimeSourceScoreWeightAcquisition.acquire 1 1 2 1 1
      let out:=SemiprimeSourceWordIdCounts.score bank weights [] programs 2 []
      bitValue out.word.numerator.magnitude
