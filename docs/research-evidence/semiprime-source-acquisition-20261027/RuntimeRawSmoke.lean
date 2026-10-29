import RiemannGaussian.SemiprimeRuntimeDesignAcquisition
open RiemannGaussian SemiprimeRuntimeDesignAcquisition SemiprimeLocalArrayFrontend
private def raw : RawDesign 1 1 where
  r := 1
  head := fun _ => 0
  assigned := fun _ => 0
  count := fun _ => 2
  rows := fun _ _ _ => 1
  W := fun _ => 1
private def arity (_ : Fin 1) : ℕ := 1
private def runtime := build raw
#eval (runtime.r, List.ofFn (fun g : Fin runtime.r => (runtime.h g,runtime.m g)))
private def run (T : (e : Fin 1) → (Fin (arity e) → Bool) → EntryReport) :=
  SemiprimeNodeArrayExecution.count 2 2 0 (fun _ => runtime) (fun _ _ _ => #[1]) T
#eval (run (fun _ a => ⟨if a ⟨0,by change 0 < 1; decide⟩ then 1 else 0,1,1⟩)).value
#eval (run (fun _ _ => ⟨1,1,1⟩)).value
#eval (run (fun _ _ => ⟨0,1,1⟩)).value
