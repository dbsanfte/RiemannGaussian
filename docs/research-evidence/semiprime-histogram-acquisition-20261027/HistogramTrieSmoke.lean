import RiemannGaussian.SemiprimeSourceHistogramTrieStore
open RiemannGaussian SemiprimeSourceHistogramTrie SemiprimeBitArithmetic
#eval let a := bump .empty []
  let b := bump a.trie [false]
  let c := bump b.trie []
  let d := bump c.trie [false,true]
  let e := bump d.trie [false]
  ([a.old,b.old,c.old,d.old,e.old].map bitValue,
    [[],[false],[false,true],[true]].map (fun k => bitValue (lookup e.trie k).bits),nodes e.trie)
#eval let a := SemiprimeSourceHistogramTrieStore.put .empty [] [false,false]
  let b := SemiprimeSourceHistogramTrieStore.put a.trie [false] [true,false]
  ((lookup b.trie []).bits,(lookup b.trie [false]).bits,(lookup b.trie [true]).bits)
#eval let a := SemiprimeSourceCompactBits.increment [true,false,false,false]
  (a.bits,bitValue a.bits)
