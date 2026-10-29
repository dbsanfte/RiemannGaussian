import RiemannGaussian.SemiprimeSourceHistogramRowKeys
open RiemannGaussian
open SemiprimeSourceHistogramRows SemiprimeSourceHistogramRowKeys
open SemiprimeSourceHistogramTrie SemiprimeBitArithmetic
#eval let cache := acquireCaches 2 2
  cache.source.bank.ids.map (fun id =>
    (id,(readRow cache.source.dictionary id).bits,
     (readKeys cache.source.dictionary cache.coordinates id).keys))
#eval let cache := acquireCaches 2 2
  (cache.source.bank.ids.length,cache.coordinates.length,nodes cache.source.dictionary.trie,cache.clock)
