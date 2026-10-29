import RiemannGaussian.SemiprimeSourceConstraintAcquisition
open RiemannGaussian
open SemiprimeFiniteEnumerations SemiprimeSourceConstraintAcquisition

def nativeEnum := indexed 2 1 2 2 (fun _=>2)
def nativeOwner (i : (e : Fin 1) × Fin ((fun _ : Fin 1=>2) e)) : Fin 2 := i.2
def nativeFactor (i : (e : Fin 1) × Fin ((fun _ : Fin 1=>2) e)) : Fin 1 := i.1
#eval (rowIndices nativeOwner nativeFactor nativeEnum (1/4)).values.length
#eval (fin 2).values.map (fun v => (head nativeOwner nativeFactor nativeEnum (1/4) 0 v).val)
#eval List.ofFn (fun j : Fin (rowIndices nativeOwner nativeFactor nativeEnum (1/4)).values.length =>
  List.ofFn (fun v : Fin 2 => matrix nativeOwner nativeFactor nativeEnum (1/4) 1 0 0 j v))
