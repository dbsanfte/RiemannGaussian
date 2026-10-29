import RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds
open RiemannGaussian
open SemiprimeRationalBits SemiprimeJetBits SemiprimeHermiteEvaluationBits

def half : RationalWord := ⟨⟨false,[true]⟩,[false,true]⟩
def minusTwo : RationalWord := ⟨⟨true,[false,true]⟩,[true]⟩
def three : RationalWord := ⟨⟨false,[true,true]⟩,[true]⟩
def minusThird : RationalWord := ⟨⟨true,[true]⟩,[true,true]⟩
def minusOne : RationalWord := negOneWord
#eval (let r := evalPrefix (List.replicate 24 false) #[half,minusTwo,three] minusTwo 3; (r.word.value,r.power.value,r.word.value==33/2,r.power.value== -8))
#eval (let r := affineValue (List.replicate 24 false) minusOne [half,minusThird]; (r.word.value,r.word.value==2/3))
#eval (let r := affineValue (List.replicate 24 false) minusTwo [half,minusThird]; (r.word.value,r.word.value==0))
#eval (let r := evalPrefix (List.replicate 24 false) #[half] minusTwo 3; (r.word.value,r.power.value,r.word.value==1/2,r.power.value== -8))
#eval (let e := evalPrefix [] #[] zeroWord 0; let a := affineValue [] zeroWord []; (e.word.value,e.power.value,a.word.value))
