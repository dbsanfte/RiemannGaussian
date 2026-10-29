import RiemannGaussian.SemiprimeSourceHistogramPortKeys
set_option autoImplicit false
open RiemannGaussian
open SemiprimeSourceHistogramPortKeys SemiprimeBitArithmetic

def smokeArity (_ : Fin 2) : ℕ := 2

def smokeOwner (i : (e : Fin 2)×Fin (smokeArity e)) : Fin 3 :=
  ⟨(i.1.val+i.2.val)%3,Nat.mod_lt _ (by decide)⟩

#eval let out := acquireOriginal 3 2 1 smokeArity smokeOwner
      out.records.map (fun row =>
        (row.ownerCode,row.factorCode,bitValue row.ownerKey,bitValue row.factorKey,
          row.ownerKey.length,row.factorKey.length))

#eval ((encodeKey 0).bits,(encodeKey 1).bits,(encodeKey 8).bits)

#eval let out := acquireOriginal 3 2 0 smokeArity smokeOwner
      out.clock ≤ budget 3 2 0 4

#eval let owner : ((_e : Fin 0)×Fin (0:ℕ))→Fin 0 := fun i => Fin.elim0 i.1
      let out := acquireOriginal 0 0 0 (fun _ => 0) owner
      (out.records.length,out.metadata.indices.length)
