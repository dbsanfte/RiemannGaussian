import RiemannGaussian.SemiprimeMaterializedSourceWords
open RiemannGaussian
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SqrtLog
private def en := SemiprimeFiniteEnumerations.sourceEnumerations
  (SemiprimeFiniteEnumerations.fin 2) (SemiprimeFiniteEnumerations.fin 2)
  (SemiprimeFiniteEnumerations.fin 1) 2 1
private def owner (i : Fin 2) := i
private def factor (_ : Fin 2) : Fin 1 := 0
private def acquired := SemiprimeMaterializedSourceWords.producer owner factor
  en.wordFirst en.wordTail en.terms.values en.indices.values 1 1
private def old := Packing.computedWords owner factor en.wordFirst en.wordTail
  en.terms.values en.indices.values (r := 2) 1 1
#eval (acquired.work,((acquired.value 0).value.head 0).val,
  ((acquired.value 1).value.head 0).val,((acquired.value 0).value.slot 0 0).val)
#eval decide (∀ i : Fin 2, (acquired.value i).value = Packing.incidenceType owner factor old i)
