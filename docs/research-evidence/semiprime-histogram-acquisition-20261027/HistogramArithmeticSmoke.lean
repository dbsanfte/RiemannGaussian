import RiemannGaussian.SemiprimeSourceHistogramArithmeticBounds
open RiemannGaussian SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceHistogramArithmetic

def cache := SemiprimeSourceHistogramScales.acquire 2 2 3 [()] [(),()]
def hist (f g : SemiprimeSourceIncidenceHistogram.Feature) :=
  if f=1 ∨ g=2 ∨ g=3 then SemiprimeSourceHistogramSquares.acquire []
  else SemiprimeSourceHistogramSquares.acquire [[]]
def q := SemiprimeSourceHistogramCountInput.count [(),()]
def p := SemiprimeSourceHistogramCountInput.count [()]
def f := SemiprimeSourceHistogramCountInput.count [()]
def C := fromState (SemiprimeSourceHistogramSquares.acquire [[false],[true]])
#eval (term (coefficients cache.alphabet) hist (3,0)).word.value
#eval let I := incidence cache hist
      let H := head cache q p f C
      let out := weighted cache I H
      (I.word.value,H.word.value,out.word.value,
       bitValue out.word.denominator,I.clock,H.clock,out.clock)
#eval let free := SemiprimeSourceHistogramCountInput.count ([] : List Unit)
      let fixed := SemiprimeSourceHistogramCountInput.count [(),()]
      let C0 := fromState (SemiprimeSourceHistogramSquares.acquire [[false],[false],[true],[true]])
      (head cache q fixed free C0).word.value
