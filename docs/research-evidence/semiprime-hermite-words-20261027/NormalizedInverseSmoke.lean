import RiemannGaussian.SemiprimeNormalizedInverseBitsBounds
open RiemannGaussian
open SemiprimeJetBits SemiprimeNormalizedInverseBits
-- Tiny exact algebra controls; these are not coverage or factoring tests.
#eval (build (List.replicate 16 false) #[oneWord,negOneWord] 0).words.size
#eval decode (build (List.replicate 16 false) #[oneWord,negOneWord] 1).words
#eval decode (build (List.replicate 16 false) #[oneWord,negOneWord] 3).words
#eval decode (build (List.replicate 16 false) #[oneWord,oneWord] 3).words
#eval (build (List.replicate 16 false) #[oneWord,oneWord] 3).clock
