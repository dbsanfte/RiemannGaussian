import RiemannGaussian.SemiprimeSourceClassifiedCountsClock
open RiemannGaussian
#eval let bank := SemiprimeSourceWordBank.acquire 2 1
  let powers := SemiprimeSourceCountPowers.acquire 2 1
  let weights := SemiprimeSourceScoreWeightAcquisition.acquire 1 1 2 1 1
  let q : Fin 1 := ⟨0,by decide⟩
  let programs := [SemiprimeMaterializedScoreEnvironment.ScoreProgram.incidence 0 1 0 1,
    .head q 0 1]
  let fresh := SemiprimeSourceClassifiedCounts.score bank powers weights
    SemiprimeSourceWordBank.defaultID programs 2 []
  let old := SemiprimeSourceWordIdCounts.score bank weights
    SemiprimeSourceWordBank.defaultID programs 2 []
  (fresh.word.value,old.word.value)
