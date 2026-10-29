import RiemannGaussian.SemiprimeScalarWordSum
open RiemannGaussian SemiprimeRationalBits SemiprimeScalarWordSum

def half : RationalWord := ⟨⟨false,[true]⟩,[false,true]⟩
def minusThird : RationalWord := ⟨⟨true,[true]⟩,[true,true]⟩
def sixth : RationalWord := ⟨⟨false,[true]⟩,[false,true,true]⟩
def f (i : Nat) : RationalReport := if i=1 then ⟨minusThird,8⟩ else ⟨sixth,9⟩
#eval (let r := sumFrom (List.replicate 20 false) f 2 1 ⟨half,5⟩; (r.word.value,r.word.value==1/3,decide (r.clock≥22)))
#eval (let r := sumFrom (List.replicate 20 false) f 1 1 ⟨half,5⟩; (r.word.value,r.word.value==1/6))
#eval (let r := sumFrom [] f 0 999 ⟨half,5⟩; (r.word.value,r.clock))
#eval (let r := sumFrom (List.replicate 20 false) (fun _=>⟨minusThird,7⟩) 3 0 ⟨SemiprimeJetBits.oneWord,2⟩; (r.word.value,r.word.value==0,decide (r.clock≥23)))
