/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1FreshJetBits
import RiemannGaussian.SemiprimeD1JetBlockBits
import RiemannGaussian.SemiprimeD1JetPolynomialCoefficient

/-! # Acquired fresh-axis block extraction of finite old-jet polynomials
Only dimension-function equality is transported. This is proof-side plumbing;
no evaluation of a nilpotent quotient at a nonzero point is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1JetBlockPolynomial
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetBoxIndex SemiprimeD1JetInterpretation
open SemiprimeD1JetAlgebra
noncomputable section

/-- Equal dimension functions give the identical concrete quotient ring. -/
def dimensionEquiv {σ R : Type*} [CommRing R] (a b : σ→ℕ) (h : a=b) :
    Algebra a R ≃+* Algebra b R :=
  RingEquiv.cast (R:=fun d : σ→ℕ=>Algebra d R) h

/-- Canonical coordinate extraction is invariant under dimension-function equality. -/
theorem dimensionEquiv_coefficient {σ R : Type*} [CommRing R] (a b : σ→ℕ) (h : a=b)
    (e : σ→₀ℕ) (he : InBox a e) (f : Algebra a R) :
    coefficient b e (h ▸ he) (dimensionEquiv a b h f)=coefficient a e he f := by
  subst b
  rfl

/-- Equal-dimension transport preserves the literal series projection. -/
theorem dimensionEquiv_project {σ R : Type*} [CommRing R] (a b : σ→ℕ) (h : a=b)
    (f : MvPowerSeries σ R) : dimensionEquiv a b h (project a f)=project b f := by
  subst b
  rfl

/-- Canonical coefficients agree after a proved equality of their exponent indices. -/
theorem coefficient_congr {σ R : Type*} [CommRing R] (dim : σ→ℕ)
    (e d : σ→₀ℕ) (he : InBox dim e) (hd : InBox dim d) (f : Algebra dim R) (h : e=d) :
    coefficient dim e he f=coefficient dim d hd f := by
  have hs : (⟨e,he⟩ : {e // InBox dim e})=⟨d,hd⟩:=Subtype.ext h
  exact congrArg (fun x : {e // InBox dim e}=>coefficient dim x.val x.property f) hs

/-- Actual list-dimension view of the abstract fresh-axis ring. -/
def actualView (old : Context) (q p : ℕ) :
    Algebra (outerDims q (dims old.axes)) (ZMod (2^p)) ≃+*
      Carrier (SemiprimeD1FreshJetBits.context old q p) :=
  dimensionEquiv (R:=ZMod (2^p)) _ _ (SemiprimeD1JetEmbedding.dims_cons q old.axes).symm

/-- Old quotient coefficients embed in the actually acquired list-dimension context. -/
def actualEmbedding (old : Context) (q p : ℕ) :
    Carrier (SemiprimeD1JetBlockBits.oldContext old p)→+*
      Carrier (SemiprimeD1FreshJetBits.context old q p) :=
  (actualView old q p).toRingHom.comp (outerEmbedding (R:=ZMod (2^p)) q (dims old.axes))

/-- Actual fresh word acquisition is exactly the transported abstract fresh generator. -/
theorem acquiredFresh_eq (old : Context) (q p : ℕ) (hpos : old.Positive) (hq : 0<q) :
    interpret (SemiprimeD1FreshJetBits.context old q p)
      (SemiprimeD1FreshJetBits.acquireFresh old q p).words=
      actualView old q p (fresh (R:=ZMod (2^p)) q (dims old.axes)) := by
  rw [SemiprimeD1FreshJetBits.fresh_value old q p hpos hq]
  symm
  exact dimensionEquiv_project (R:=ZMod (2^p)) _ _ (SemiprimeD1JetEmbedding.dims_cons q old.axes).symm (MvPowerSeries.X 0)

/-- Actual finite polynomial evaluation at the acquired fresh jet is its transported abstract value. -/
theorem eval_acquired (old : Context) (q p : ℕ) (hpos : old.Positive) (hq : 0<q)
    (F : Polynomial (Carrier (SemiprimeD1JetBlockBits.oldContext old p))) :
    F.eval₂ (actualEmbedding old q p)
      (interpret (SemiprimeD1FreshJetBits.context old q p)
        (SemiprimeD1FreshJetBits.acquireFresh old q p).words)=
      actualView old q p (F.eval₂ (outerEmbedding (R:=ZMod (2^p)) q (dims old.axes)) (fresh (R:=ZMod (2^p)) q (dims old.axes))) := by
  rw [acquiredFresh_eq old q p hpos hq]
  exact (Polynomial.hom_eval₂ F (outerEmbedding (R:=ZMod (2^p)) q (dims old.axes)) (actualView old q p).toRingHom
    (fresh (R:=ZMod (2^p)) q (dims old.axes))).symm

/-- The actual canonical block of finite evaluation is EXACTLY F.coeffj in the entire old jet ring.
No degree, domain, field, coefficient-answer or nonzero-point evaluation premise is used. -/
theorem block_polynomial (old : Context) (q p j : ℕ) (hpos : ∀q∈old.axes,0<q) (hj : j<q)
    (F : Polynomial (Carrier (SemiprimeD1JetBlockBits.oldContext old p))) :
    SemiprimeD1JetBlockBits.blockValue old q p j hpos hj
      (F.eval₂ (actualEmbedding old q p)
        (interpret (SemiprimeD1FreshJetBits.context old q p)
          (SemiprimeD1FreshJetBits.acquireFresh old q p).words))=F.coeff j := by
  apply SemiprimeD1JetAlgebra.ext (R:=ZMod (2^p)) (dims old.axes)
  intro e he
  let i:=(boxEquiv old.axes hpos).symm ⟨e,he⟩
  have hindex : exponent old.axes i.val=e :=
    congrArg Subtype.val ((boxEquiv old.axes hpos).apply_symm_apply ⟨e,he⟩)
  have hi : i.val<old.rank:=i.isLt
  let b:=SemiprimeD1JetBlockBits.blockExponent old j (exponent old.axes i.val)
  have hb:=SemiprimeD1JetBlockBits.block_inBox old q j i.val hpos hj hi
  have hpoly:=SemiprimeD1JetPolynomialCoefficient.polynomial_coefficient (R:=ZMod (2^p)) q (dims old.axes) j hj
    (exponent old.axes i.val) (exponent_inBox old.axes i.val hpos hi) F
  have ht:=dimensionEquiv_coefficient (R:=ZMod (2^p)) (outerDims q (dims old.axes)) (dims (q::old.axes))
    (SemiprimeD1JetEmbedding.dims_cons q old.axes).symm b
    (SemiprimeD1JetPolynomialCoefficient.block_inBox q (dims old.axes) j hj
      (exponent old.axes i.val) (exponent_inBox old.axes i.val hpos hi))
    (F.eval₂ (outerEmbedding (R:=ZMod (2^p)) q (dims old.axes)) (fresh (R:=ZMod (2^p)) q (dims old.axes)))
  have hx:=SemiprimeD1JetBlockBits.blockValue_coefficient old q p j i.val hpos hj hi
    (F.eval₂ (actualEmbedding old q p)
      (interpret (SemiprimeD1FreshJetBits.context old q p)
        (SemiprimeD1FreshJetBits.acquireFresh old q p).words))
  have hev:=eval_acquired old q p hpos (Nat.zero_lt_of_lt hj) F
  have hc:=congrArg (fun f : Carrier (SemiprimeD1FreshJetBits.context old q p)=>
    coefficient (dims (q::old.axes)) b hb f) hev
  have hidx : coefficient (dims old.axes) (exponent old.axes i.val)
      (exponent_inBox old.axes i.val hpos hi)
      (SemiprimeD1JetBlockBits.blockValue old q p j hpos hj
        (F.eval₂ (actualEmbedding old q p)
          (interpret (SemiprimeD1FreshJetBits.context old q p)
            (SemiprimeD1FreshJetBits.acquireFresh old q p).words)))=
      coefficient (dims old.axes) (exponent old.axes i.val)
        (exponent_inBox old.axes i.val hpos hi) (F.coeff j) :=
    hx.trans (hc.trans (ht.trans hpoly))
  exact (coefficient_congr (R:=ZMod (2^p)) _ _ _ _ he _ hindex).symm.trans
    (hidx.trans (coefficient_congr (R:=ZMod (2^p)) _ _ _ _ he _ hindex))

/-- Physical block extraction composes with a proved child-program refinement.
F and the equality are proof-side; the runtime receives only the acquired word vector. -/
theorem extractRun_polynomial (old : Context) (q p j : ℕ)
    (input : SemiprimeD1JetAffineCoefficient.JetRun) (hpos : ∀q∈old.axes,0<q) (hj : j<q)
    (F : Polynomial (Carrier (SemiprimeD1JetBlockBits.oldContext old p)))
    (hvalue : interpret (SemiprimeD1JetBlockBits.newContext old q p) input.words=
      F.eval₂ (actualEmbedding old q p)
        (interpret (SemiprimeD1FreshJetBits.context old q p)
          (SemiprimeD1FreshJetBits.acquireFresh old q p).words)) :
    interpret (SemiprimeD1JetBlockBits.oldContext old p)
      (SemiprimeD1JetBlockBits.extractRun old j input).words=F.coeff j := by
  exact (SemiprimeD1JetBlockBits.extractRun_value old q p j input hpos hj).trans
    ((congrArg (SemiprimeD1JetBlockBits.blockValue old q p j hpos hj) hvalue).trans
      (block_polynomial old q p j hpos hj F))

end
end RiemannGaussian.SemiprimeD1JetBlockPolynomial
