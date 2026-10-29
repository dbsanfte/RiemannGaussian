import RiemannGaussian.SemiprimeCardinalInputBits
open RiemannGaussian.SemiprimeCardinalInputBits
#eval let out := acquire 3 2 ⟨1, by decide⟩
  (out.slopes.map (fun w => w.value), out.x.value, out.clock)
