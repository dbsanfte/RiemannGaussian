import RiemannGaussian.SemiprimeSourceHistogramScalesBounds
open RiemannGaussian SemiprimeBitArithmetic
#eval let out := SemiprimeSourceHistogramScales.acquire 2 2 3 (List.replicate 3 ()) (List.replicate 2 ())
      ([out.alphabet,out.square,out.fourth,out.head,out.weights.incidence,out.weights.head].map bitValue,
       [out.alphabet,out.square,out.fourth,out.head,out.weights.incidence,out.weights.head].map List.length,out.clock)
#eval let out := SemiprimeSourceHistogramScales.acquire 1 0 0 ([] : List Unit) ([] : List Unit)
      ([out.alphabet,out.square,out.fourth,out.head,out.weights.incidence,out.weights.head].map bitValue,
       [out.alphabet,out.square,out.fourth,out.head,out.weights.incidence,out.weights.head].map List.length)
