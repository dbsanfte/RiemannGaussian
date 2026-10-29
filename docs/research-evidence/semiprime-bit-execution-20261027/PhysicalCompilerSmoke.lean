import RiemannGaussian.SemiprimePolynomialCodeBits
set_option autoImplicit false
open RiemannGaussian
open SemiprimeRationalBits SemiprimeDotBits SemiprimeJetBits
open SemiprimePolynomialCodeBits
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

def line : PolynomialCode RationalWord := .add (.constant oneWord) (.mul (.constant negOneWord) .indeterminate)
def square : PolynomialCode RationalWord := .mul line line

theorem square_constants_valid : ConstantsValid square := by
  change ((oneWord.Valid ∧ negOneWord.Valid ∧ True) ∧ (oneWord.Valid ∧ negOneWord.Valid ∧ True))
  exact ⟨⟨oneWord_valid,negOneWord_valid,True.intro⟩,⟨oneWord_valid,negOneWord_valid,True.intro⟩⟩

#eval (decode (addBits (List.replicate 8 false) #[oneWord,negOneWord] #[negOneWord,oneWord] 3).words).toList
#eval (decode (scaleBits (List.replicate 8 false) #[oneWord,negOneWord] negOneWord 3).words).toList
#eval (decode (multiplyBits (List.replicate 8 false) #[oneWord,negOneWord] #[oneWord,negOneWord] 4).words).toList
#eval requiredWidth 4 square
#eval (decode (compile (List.replicate (requiredWidth 4 square) false) 4 square).words).toList
#eval ((compile (List.replicate (requiredWidth 4 square) false) 4 square).clock,
  nodes square*nodeCost 4 (requiredWidth 4 square))
-- Deliberately insufficient width: confirms fitting has real semantics and cannot be omitted.
#eval (decode (addBits [false] #[oneWord] #[oneWord] 1).words).toList
