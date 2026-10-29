import RiemannGaussian.SemiprimeSourceHistogramSquaresBounds
open RiemannGaussian
open SemiprimeBitArithmetic SemiprimeSourceHistogramSquares

def keys : List (List Bool) := [[],[false],[],[false,true],[false]]
#eval (List.range 6).map (fun n => bitValue (acquire (keys.take n)).bits)
#eval let out := acquire keys
      (bitValue out.bits,
       [[],[false],[false,true],[true]].map (fun key =>
         bitValue (SemiprimeSourceHistogramTrie.lookup out.trie key).bits),out.clock,
       SemiprimeSourceHistogramTrie.nodes out.trie)
#eval (bitValue (acquire []).bits,(acquire []).clock)
