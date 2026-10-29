import RiemannGaussian.SemiprimeLocalBitsBounds
open RiemannGaussian SemiprimeLocalBits SemiprimeLocalBitsBounds
open SemiprimeJetBits SemiprimeRationalBits

def half : RationalWord := ⟨⟨false,[true]⟩,[false,true]⟩
def third : RationalWord := ⟨⟨false,[true]⟩,[true,true]⟩
def ports (i : Fin 2) : Array RationalWord :=
  if i.val=0 then #[half,oneWord,zeroWord] else #[third,negOneWord,zeroWord]
def andEntry (eta : Fin 2 → Bool) : EntryWord := ⟨⟨false,[eta 0 && eta 1]⟩,4⟩
#eval let run := localEvaluateBits (List.replicate (bufferWidth 3 2) false) 3 2 andEntry ports
  ((decode run.words).toList,run.clock)
