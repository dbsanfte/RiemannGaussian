/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScorePrefixHeight
import RiemannGaussian.SemiprimeMaterializedSourceWords
import RiemannGaussian.SemiprimePaidFiniteEnumerations

/-! # Actual source offset power and rational scratch bounds
These bounds concern the literal finite power loop and the fixed expression
executed by offsetRun. Inputs are original score scales, never intermediate
representations or desired output heights. Primitive simulation remains separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceOffsetHeight
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking
open SemiprimeJetArrayHeight SemiprimeSourceScorePrefixHeight
open SemiprimeMaterializedSourceWords

/-- Every cached power and every next multiplication is bounded by the actual target power. -/
theorem power_prefix_bound (r Q k : ℕ) (hr : 0<r) (hk : k≤2*Q) :
    (powNatRun r k).value≤r^(2*Q) ∧
      (k<2*Q → (powNatRun r k).value*r≤r^(2*Q)) := by
  rw [powNatRun_value]
  refine ⟨Nat.pow_le_pow_right hr hk,?_⟩
  intro h
  rw [← pow_succ]
  exact Nat.pow_le_pow_right hr (by omega)

/-- The actual loop has linear recursion depth and the already-paid step count. -/
theorem power_prefix_work (r Q k : ℕ) (hk : k≤2*Q) : (powNatRun r k).work≤4*Q+1 := by
  rw [powNatRun_work]
  omega

/-- Multiplication by an original integer dimension preserves the common denominator. -/
theorem multiply_nat {q : ℚ} (d B C : ℕ) (hq : Representation q d B) :
    Representation (q*(C:ℚ)) d (B*C) := by
  have hc : Representation (C:ℚ) 1 C := ⟨(C:ℤ),by simp,by simp⟩
  simpa only [Nat.mul_one] using representation_mul hq hc

/-- A positive known denominator factor clears a branch without changing its value. -/
theorem extend_factor {q : ℚ} (d B C : ℕ) (hC : 0<C) (hq : Representation q d B) :
    Representation q (d*C) (B*C) := by
  have hOne : Representation (1:ℚ) C C := by
    refine ⟨(C:ℤ),?_,by simp⟩
    simp only [Int.cast_natCast]
    exact (div_self (by exact_mod_cast hC.ne')).symm
  simpa only [mul_one] using representation_mul hq hOne

/-- A fixed polynomial covers each exact numerator and denominator envelope. -/
def height (d B M n r Q U : ℕ) : ℕ :=
  d+B+d^2+B^2+B^2*M+B^2*M*M+d^2*U+B^2*Q+B^2*Q*n+B^2*Q*n*n+
    d^2*r+d^2*U*r+(B^2*M*M*r+B^2*Q*n*n*U)+U+r+M+n+Q+2

/-- Literal scalar stages of the executed fixed offset expression, in dependency order.
This is a proof-side list of scratch values, not another runtime implementation. -/
def scratch (M n r Q U : ℕ) (x y : ℚ) : List ℚ :=
  [x,y,(M:ℚ),(n:ℚ),(r:ℚ),(Q:ℚ),(U:ℚ),
    y*y,y*y*(M:ℚ),y*y*(M:ℚ)*(M:ℚ),y*y*(M:ℚ)*(M:ℚ)/(U:ℚ),
    x*x,x*x*(Q:ℚ),x*x*(Q:ℚ)*(n:ℚ),x*x*(Q:ℚ)*(n:ℚ)*(n:ℚ),
    x*x*(Q:ℚ)*(n:ℚ)*(n:ℚ)/(r:ℚ),
    y*y*(M:ℚ)*(M:ℚ)/(U:ℚ)+x*x*(Q:ℚ)*(n:ℚ)*(n:ℚ)/(r:ℚ)]

/-- Every ACTUAL fixed offset scratch value has a derived normalized rational bound. -/
theorem scratch_bound (d B M n r Q U : ℕ) (x y : ℚ)
    (hd : 0<d) (hr : 0<r) (hU : 0<U)
    (hx : Representation x d B) (hy : Representation y d B) :
    ∀ q∈scratch M n r Q U x y,
      q.den≤height d B M n r Q U ∧ q.num.natAbs≤height d B M n r Q U := by
  have hy2 : Representation (y*y) (d^2) (B^2) := by simpa only [pow_two] using representation_mul hy hy
  have hx2 : Representation (x*x) (d^2) (B^2) := by simpa only [pow_two] using representation_mul hx hx
  have hym := multiply_nat _ _ M hy2
  have hymm := multiply_nat _ _ M hym
  have hyu := divide_representation _ _ U hymm
  have hxq := multiply_nat _ _ Q hx2
  have hxqn := multiply_nat _ _ n hxq
  have hxqnn := multiply_nat _ _ n hxqn
  have hxr := divide_representation _ _ r hxqnn
  have hyleft := extend_factor _ _ r hr hyu
  have hxright := extend_factor _ _ U hU hxr
  have hxright' : Representation (x*x*(Q:ℚ)*(n:ℚ)*(n:ℚ)/(r:ℚ)) (d^2*U*r) (B^2*Q*n*n*U) := by
    convert hxright using 1; ring
  have hsum := representation_add hyleft hxright'
  have cap {q : ℚ} {D N : ℕ} (hD : 0<D) (hq : Representation q D N)
      (hDb : D≤height d B M n r Q U) (hNb : N≤height d B M n r Q U) :
      q.den≤height d B M n r Q U ∧ q.num.natAbs≤height d B M n r Q U := by
    have hh := representation_reduced_bound hD hq
    exact ⟨hh.1.trans hDb,hh.2.trans hNb⟩
  have hpow : 0<d^2 := pow_pos hd _
  have hbase : 0<height d B M n r Q U := by unfold height; omega
  have hnats (c : ℕ) (hc : c≤height d B M n r Q U) :
      (c:ℚ).den≤height d B M n r Q U ∧ (c:ℚ).num.natAbs≤height d B M n r Q U := by
    exact cap (by decide : 0<1) ⟨(c:ℤ),by simp,by simp⟩ (by omega) hc
  intro q hq
  simp only [scratch,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cap hd hx (by unfold height; omega) (by unfold height; omega)
  · exact cap hd hy (by unfold height; omega) (by unfold height; omega)
  · exact hnats M (by unfold height; omega)
  · exact hnats n (by unfold height; omega)
  · exact hnats r (by unfold height; omega)
  · exact hnats Q (by unfold height; omega)
  · exact hnats U (by unfold height; omega)
  · exact cap hpow hy2 (by unfold height; omega) (by unfold height; omega)
  · exact cap hpow hym (by unfold height; omega) (by unfold height; omega)
  · exact cap hpow hymm (by unfold height; omega) (by unfold height; omega)
  · exact cap (Nat.mul_pos hpow hU) hyu (by unfold height; omega) (by unfold height; omega)
  · exact cap hpow hx2 (by unfold height; omega) (by unfold height; omega)
  · exact cap hpow hxq (by unfold height; omega) (by unfold height; omega)
  · exact cap hpow hxqn (by unfold height; omega) (by unfold height; omega)
  · exact cap hpow hxqnn (by unfold height; omega) (by unfold height; omega)
  · exact cap (Nat.mul_pos hpow hr) hxr (by unfold height; omega) (by unfold height; omega)
  · exact cap (Nat.mul_pos (Nat.mul_pos hpow hU) hr) hsum
      (by unfold height; omega) (by unfold height; omega)

/-- The bound covers the literal offsetRun result as one of its actual stages. -/
theorem offset_bound (d B M n r Q : ℕ) (x y : ℚ) (hd : 0<d) (hr : 0<r)
    (hx : Representation x d B) (hy : Representation y d B) :
    (offsetRun M n r Q x y).value.den≤height d B M n r Q (r^(2*Q)) ∧
      (offsetRun M n r Q x y).value.num.natAbs≤height d B M n r Q (r^(2*Q)) := by
  apply scratch_bound d B M n r Q (r^(2*Q)) x y hd hr (pow_pos hr _) hx hy
  simp only [offsetRun,powNatRun_value,scratch,List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- The ACTUAL complete word candidate list has size L=r^Q. -/
theorem caller_word_length {I V E : Type} {r Q : ℕ}
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) :
    (en.wordFirst::en.wordTail).length=r^Q := by
  let words : FiniteEnumeration (Word r Q) := ⟨en.wordFirst::en.wordTail,en.words_nodup,en.words_complete⟩
  exact words.length_eq_card.trans (card_word r Q)

/-- The universal type bank has size U=r^(2Q), DISTINCT from the word alphabet. -/
theorem caller_universal_length {I V E : Type} {r Q : ℕ}
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) :
    en.types.values.length=r^(2*Q) := by
  rw [en.types.length_eq_card,card_universalType]
  congr 1
  omega

/-- Both actual caller banks are nonempty under the original nonzero group parameter. -/
theorem caller_bank_positive {I V E : Type} {r Q : ℕ} [NeZero r]
    (en : SemiprimeSourceLayout.Enumerations I V E r Q) :
    0<en.types.values.length ∧ 0<(en.wordFirst::en.wordTail).length := by
  rw [caller_universal_length,caller_word_length]
  exact ⟨pow_pos (NeZero.pos r) _,pow_pos (NeZero.pos r) _⟩

/-- The exact x/y arguments in all original source/constraint callers have
closed scheduled input bounds, without canonical-numerator advice. -/
theorem caller_scale_representations {I E : Type} {n r Q : ℕ} [NeZero r]
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0<lam) :
    let eps : ℚ := 1/((r*lam:ℕ):ℚ)
    let D := r*lam*(r^(2*Q))*(2*r)
    let B := en.incidences.values.length*(2*r)+n*(r*lam)*(r^(2*Q))
    Representation (eps*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ)) D B ∧
      Representation ((n:ℚ)/(2*(r:ℚ))) D B := by
  dsimp only
  rw [caller_universal_length]
  exact scheduled_scale_representations _ n r lam (r^(2*Q)) (NeZero.pos r) hlam (pow_pos (NeZero.pos r) _)

/-- Every original scheduled caller's actual offset scratch is bounded solely
from finite dimensions and the supplied original enumeration, not intermediate values. -/
theorem caller_offset_scratch_bound {I E : Type} {n r Q : ℕ} [NeZero r]
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0<lam) :
    let eps : ℚ := 1/((r*lam:ℕ):ℚ)
    let x := eps*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ)
    let y := (n:ℚ)/(2*(r:ℚ))
    let D := r*lam*(r^(2*Q))*(2*r)
    let B := en.incidences.values.length*(2*r)+n*(r*lam)*(r^(2*Q))
    ∀ q∈scratch en.incidences.values.length n r Q (r^(2*Q)) x y,
      q.den≤height D B en.incidences.values.length n r Q (r^(2*Q)) ∧
      q.num.natAbs≤height D B en.incidences.values.length n r Q (r^(2*Q)) := by
  have hs := caller_scale_representations en lam hlam
  apply scratch_bound _ _ _ n r Q _ _ _
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (NeZero.pos r) hlam)
      (pow_pos (NeZero.pos r) _)) (Nat.mul_pos (by decide) (NeZero.pos r))) (NeZero.pos r) (pow_pos (NeZero.pos r) _)
    hs.1 hs.2

/-- Positive scheduled epsilon forces positive lambda; this is the exact
positivity fact used when the original executable guard has passed. -/
theorem lambda_pos_of_epsilon_pos (r lam : ℕ)
    (h : (0:ℚ)<1/((r*lam:ℕ):ℚ)) : 0<lam := by
  by_contra hc
  have hz : lam=0 := by omega
  subst lam
  norm_num at h

/-- Before normalization, every elementary rational numerator/denominator
cross-product formed from ACTUAL offset operands has a polynomial bound too.
This is a numerical scratch invariant, not a claim about a tape interpreter. -/
theorem raw_cross_products_bound (d B M n r Q U : ℕ) (x y : ℚ)
    (hd : 0<d) (hr : 0<r) (hU : 0<U)
    (hx : Representation x d B) (hy : Representation y d B)
    (a b : ℚ) (ha : a∈scratch M n r Q U x y) (hb : b∈scratch M n r Q U x y) :
    let H := height d B M n r Q U
    a.num.natAbs*b.num.natAbs≤H^2 ∧
    a.den*b.den≤H^2 ∧ a.num.natAbs*b.den≤H^2 ∧
    a.den*b.num.natAbs≤H^2 ∧
    a.num.natAbs*b.den+b.num.natAbs*a.den≤2*H^2 := by
  have ha' := scratch_bound d B M n r Q U x y hd hr hU hx hy a ha
  have hb' := scratch_bound d B M n r Q U x y hd hr hU hx hy b hb
  have hnn := Nat.mul_le_mul ha'.2 hb'.2
  have hdd := Nat.mul_le_mul ha'.1 hb'.1
  have hnd := Nat.mul_le_mul ha'.2 hb'.1
  have hdn := Nat.mul_le_mul ha'.1 hb'.2
  have hdn' := Nat.mul_le_mul hb'.2 ha'.1
  simp only [pow_two]
  exact ⟨hnn,hdd,hnd,hdn,by omega⟩

/-- Explicit common denominator of the actual offset, from original source scales. -/
def offsetDenominator (d r Q : ℕ) : ℕ := d^2*r^(2*Q)*r
/-- Explicit numerator envelope of the actual offset. -/
def offsetNumerator (B M n r Q : ℕ) : ℕ := B^2*M*M*r+B^2*Q*n*n*r^(2*Q)

/-- The actual offset's representation is derived directly, before canonical
rational reduction; no offset representation is a premise. -/
theorem offset_representation (d B M n r Q : ℕ) (x y : ℚ) (hr : 0<r)
    (hx : Representation x d B) (hy : Representation y d B) :
    Representation (offsetRun M n r Q x y).value
      (offsetDenominator d r Q) (offsetNumerator B M n r Q) := by
  have hy2 : Representation (y*y) (d^2) (B^2) := by simpa only [pow_two] using representation_mul hy hy
  have hx2 : Representation (x*x) (d^2) (B^2) := by simpa only [pow_two] using representation_mul hx hx
  have hym := multiply_nat _ _ M hy2
  have hymm := multiply_nat _ _ M hym
  have hleft := extend_factor _ _ r hr (divide_representation _ _ (r^(2*Q)) hymm)
  have hxq := multiply_nat _ _ Q hx2
  have hxqn := multiply_nat _ _ n hxq
  have hxqnn := multiply_nat _ _ n hxqn
  have hright := extend_factor _ _ (r^(2*Q)) (pow_pos hr _) (divide_representation _ _ r hxqnn)
  have hright' : Representation (x*x*(Q:ℚ)*(n:ℚ)*(n:ℚ)/(r:ℚ))
      (offsetDenominator d r Q) (B^2*Q*n*n*r^(2*Q)) := by
    convert hright using 1; unfold offsetDenominator; ring
  simpa only [offsetRun,powNatRun_value,offsetDenominator,offsetNumerator] using representation_add hleft hright'

/-- Exact actual scheduled caller offset representation, with no intermediate
or canonical numerator/denominator premise. -/
theorem caller_offset_representation {I E : Type} {n r Q : ℕ} [NeZero r]
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0<lam) :
    let eps : ℚ := 1/((r*lam:ℕ):ℚ)
    let x := eps*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ)
    let y := (n:ℚ)/(2*(r:ℚ))
    let D := r*lam*(r^(2*Q))*(2*r)
    let B := en.incidences.values.length*(2*r)+n*(r*lam)*(r^(2*Q))
    Representation (offsetRun en.incidences.values.length n r Q x y).value
      (offsetDenominator D r Q) (offsetNumerator B en.incidences.values.length n r Q) := by
  have h := caller_scale_representations en lam hlam
  exact offset_representation _ _ _ n r Q _ _ (NeZero.pos r) h.1 h.2

end RiemannGaussian.SemiprimeSourceOffsetHeight
