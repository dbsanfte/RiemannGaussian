import RiemannGaussian.SemiprimeSourceArrayAcquisition
open RiemannGaussian SemiprimeFiniteEnumerations SemiprimeSourceArrayAcquisition
set_option autoImplicit false

def smokeEn := indexed 2 1 2 2 (fun _ => 2)
def smokeOwner : ((_e : Fin 1) × Fin 2) → Fin 2 := fun i => i.2
def smokeSource := acquire smokeOwner Sigma.fst smokeEn (1/4) 1
#eval smokeSource
#eval read (n := 2) smokeEn.incidences smokeSource ⟨0,0⟩ 0
#eval read (n := 2) smokeEn.incidences smokeSource ⟨0,0⟩ 1
#eval read (n := 2) smokeEn.incidences smokeSource ⟨0,1⟩ 1
