import RiemannGaussian.SemiprimeFullSetupCounter
open RiemannGaussian
private def emptyArity : Fin 0 → Nat := Fin.elim0
private def emptyCoordinate (e : Fin 0) : Fin (emptyArity e) → Fin 0 := Fin.elim0 e
private def emptyEntry (e : Fin 0) : (Fin (emptyArity e) → Bool) → SemiprimeLocalArrayFrontend.EntryReport := Fin.elim0 e
#eval (let out := SemiprimeFullSetupCounter.count (n:=0) (F:=0) (r:=1) (Q:=1) emptyArity emptyCoordinate 0 0 0 1 emptyEntry; (out.value, out.work))
