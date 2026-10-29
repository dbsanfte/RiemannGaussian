import RiemannGaussian.SemiprimeTernaryLocal
import RiemannGaussian.SemiprimeTernaryLocalPaid
open RiemannGaussian
open SemiprimeTernaryLocalPaid
private def backend (op : Opcode) (a b : ZMod 17) : OperationResult (ZMod 17) :=
  ⟨meaning op a b,2⟩
private def checker (a : Fin 2 → Bool) : Bool × ℕ := (a 0 && a 1,4)
#eval let p := preparePort backend (3 : ZMod 17)
  (p.yes.val,p.no.val,p.operations,p.reads,p.work)
#eval let k := booleanKernel backend (3 : ZMod 17) 15 2 5
  (k.value.val,k.calls,k.reads,k.work)
#eval let out := evaluate backend 2 (ofBoolean checker) ![3,4]
  (out.value.val,out.work,out.callbacks,out.operations,out.reads,out.depth)
#eval let out := evaluate backend 0 (fun _ => (⟨5,7⟩ : Entry (ZMod 17))) Fin.elim0
  (out.value.val,out.work,out.callbacks,out.operations,out.reads,out.depth)
private def table (a : Fin 2 → Bool) : ZMod 17 := if a 0 && a 1 then 1 else 0
#eval List.ofFn (fun i : Fin 3 => List.ofFn (fun j : Fin 3 =>
  (SemiprimeTernaryLocal.evaluate (9 : ZMod 17) 2 table ![(i.val : ZMod 17),(j.val : ZMod 17)]).val))
#eval (SemiprimeTernaryLocal.evaluate (9 : ZMod 17) 2 table ![3,4]).val
