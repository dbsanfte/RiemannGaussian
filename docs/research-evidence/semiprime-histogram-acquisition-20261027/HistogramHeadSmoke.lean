import RiemannGaussian.SemiprimeSourceHistogramHeadOriginal
open RiemannGaussian
open SemiprimeBitArithmetic SemiprimeSourceHistogramHeadBits
#eval let cache := SemiprimeSourceHistogramRowKeys.acquireCaches 2 2
  let fixed := [[true],[]]
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  let vertices := (acquireVertices 2).value
  [(2,0),(1,1),(0,2)].map (fun p =>
    let result := acquire cache dict p.1 p.2 vertices
    (bitValue result.head.fixed,bitValue result.head.free,
     bitValue result.histogram.bits,result.head.keys.length,result.clock))
