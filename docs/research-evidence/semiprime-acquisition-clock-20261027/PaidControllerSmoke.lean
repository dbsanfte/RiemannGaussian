import RiemannGaussian.SemiprimePaidScheduledController
open RiemannGaussian
private def positive (fixed : List (Nat × Bool)) : SemiprimePaidPrefixController.Run Nat :=
  ⟨1,10+fixed.length⟩
private def empty (_ : List (Nat × Bool)) : SemiprimePaidPrefixController.Run Nat := ⟨0,7⟩
#eval let r := SemiprimePaidPrefixController.search positive [0,1]; (r.values,r.queries,r.work)
#eval let r := SemiprimePaidPrefixController.search empty [0,1]; (r.values,r.queries,r.work)
#eval let r := SemiprimePaidScheduledController.run 0; (r.value,r.queries,r.work)
#eval let r := SemiprimePaidScheduledController.run 4; (r.value,r.queries,r.work)
private def inputValues : List (Fin (SemiprimePublicAcquiredExecution.wireCount 4) × Bool) :=
  [((SemiprimePublicAcquiredExecution.edgeEnumeration 4).equivFin.symm
    (SemiprimePaidFactorDecoder.inputWire 4 0 0 (by decide) ⟨1,by decide⟩),true)]
#eval let r := SemiprimePaidFactorDecoder.decode 4 inputValues 0;
  (r.value,SemiprimePublicAcquiredExecution.decodeOperand 4 inputValues 0,r.work)
