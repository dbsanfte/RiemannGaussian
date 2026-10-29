/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryGridBitsBounds

/-! # Physical cached powers and right-recursive local weight sums
Every scalar normalization/GCD and coefficient payload lookup is executed on
physical words. Address digits and typed loop tests remain native metadata
stages, explicitly retained apart from the Boolean arithmetic clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryScalarWeightBits
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeBitArithmetic
open SemiprimeD1RecoveryPowerBits SemiprimeD1RecoveryGridBits
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryWeightRun
open SemiprimeD1WireKernelOriginal SemiprimeD1JetRecoveryGrid
open SemiprimeD1HermiteDenominatorHeight SemiprimeD1HermiteWeightHeight
open SemiprimeD1HermiteDenominatorBits SemiprimeD1RecoveryWeightRunState

/-- Actual scalar word with distinctly retained physical and native reports. -/
structure WordReport where
  /-- Actual physical output rational. -/
  word : RationalWord
  /-- Actual arithmetic, GCD/division and payload scans/copies. -/
  clock : ℕ
  /-- Actual typed address generation and index/control stages. -/
  metadataWork : ℕ

/-- Acquire actual address digits and perform a literal paid physical memory scan. -/
def read (q : ℕ) (memory : List RationalWord) (i : ℕ) : WordReport :=
  let address:=SemiprimeEncodedRowSelection.digits (q+1) i
  let out:=SemiprimeSourceMemoryBits.readWord memory address.bits
  ⟨out.word,out.clock,address.work+3⟩

/-- Physical cache lookup refines the actual native coefficient access. -/
theorem read_value (q : ℕ) (memory : List RationalWord) (a : Array ℚ) (i : ℕ)
    (hm : memory.map RationalWord.value=a.toList) (hi : i < q) :
    (read q memory i).word.value=coefficient a i := by
  have he : i < 2^(q+1) := hi.trans_le
    ((SemiprimeD1HermiteDenominatorBits.self_le_two_power q).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)))
  have hd:=SemiprimeEncodedRowSelection.digits_value (q+1) i he
  change (SemiprimeSourceMemoryBits.readWord memory (SemiprimeEncodedRowSelection.digits (q+1) i).bits).word.value=_
  rw [SemiprimeSourceMemoryBits.readWord_word,hd]
  have hget:=congrArg (fun xs : List ℚ => (xs[i]?).getD 0) hm
  simp only [List.getElem?_map,Array.getElem?_toList] at hget
  unfold coefficient
  rw [← hget]
  cases memory[i]? <;> simp [SemiprimeRationalBits.zeroWord,RationalWord.value,
    SemiprimeBitIndexClipping.SignedWord.value,SemiprimeBitArithmetic.bitValue]

/-- Actual memory legality gives lookup legality, including the zero default. -/
theorem read_valid (q : ℕ) (memory : List RationalWord) (i : ℕ)
    (hm : ∀x∈memory,x.Valid) : (read q memory i).word.Valid :=
  SemiprimeSourceMemoryBits.readWord_valid _ _ hm

/-- Actual physical source widths give lookup widths, without output advice. -/
theorem read_width (q : ℕ) (memory : List RationalWord) (i W : ℕ)
    (hW : 0 < W) (hm : ∀x∈memory,Width x W) : Width (read q memory i).word W :=
  SemiprimeSourceMemoryBits.readWord_width _ _ W (by omega) hm

/-- Every visited address and payload bit is charged. -/
theorem read_clock (q : ℕ) (memory : List RationalWord) (i W : ℕ)
    (hm : ∀x∈memory,Width x W) :
    (read q memory i).clock ≤ (memory.length+1)*(8*W+15*(q+1)+30) := by
  exact SemiprimeSourceMemoryBits.readWord_clock _ _ W (q+1) (by omega)
    (by rw [SemiprimeEncodedRowSelection.digits_length]) hm

/-- Actual address digit acquisition report, not an assumed address-cost oracle. -/
theorem read_metadataWork (q : ℕ) (memory : List RationalWord) (i : ℕ) :
    (read q memory i).metadataWork=4*(q+1)+4 := by
  simp only [read,SemiprimeEncodedRowSelection.digits_work]

/-- Actual original right-recursive local coefficient sum on physical caches. -/
def sum (template : List Bool) (q j : ℕ) (inverse powers : List RationalWord) : List ℕ → WordReport
  | [] => ⟨SemiprimeRationalBits.zeroWord,3,1⟩
  | k::ks =>
    let tail:=sum template q j inverse powers ks
    if j ≤ k then
      let left:=read q inverse (k-j)
      let right:=read q powers k
      let product:=executeOperation .mul left.word right.word template
      let out:=executeOperation .add product.word tail.word template
      ⟨out.word,tail.clock+left.clock+right.clock+product.clock+out.clock+7,
        tail.metadataWork+left.metadataWork+right.metadataWork+4⟩
    else ⟨tail.word,tail.clock+3,tail.metadataWork+3⟩

/-- Each actual local weight multiplies the physically acquired Ezero once. -/
def weight (template : List Bool) (q j : ℕ) (scalar : RationalWord)
    (inverse powers : List RationalWord) (keys : List ℕ) : WordReport :=
  let total:=sum template q j inverse powers keys
  let out:=executeOperation .mul scalar total.word template
  ⟨out.word,total.clock+out.clock+3,total.metadataWork+2⟩

/-- Exact original normalization cap for ANY actually visited retained-index list. -/
theorem sum_fits (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j : ℕ) (keys : List ℕ)
    (hk : ∀k∈keys,k < nodeMultiplicity a h u t.val) (hl : keys.length ≤ nodeMultiplicity a h u t.val)
    (W : ℕ) (hW : sumExponent a h u t.val < W) :
    Fits (sumWeights j (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) (nodeMultiplicity a h u t.val)).value keys).value W := by
  let q:=nodeMultiplicity a h u t.val
  let D:=sourceDenominator a h u t.val
  let V:=inverseBase q D (sourceNumerator a h u t.val)
  have hr:=representation_reduced_bound (pow_pos (Nat.mul_pos (sourceDenominator_pos a h u t.val)
      (by unfold size; positivity)) q) (sum_representation a h u t hq j keys hk)
  have hi:=inverse_power_bounds a h u t
  have hN : (size a)^q=2^((a+1)*q) := by unfold size; rw [← pow_mul]
  have hlen : keys.length ≤ 2^q := hl.trans (self_le_two_power q)
  have hd : (D*size a)^q ≤ 2^(inverseExponent a h u t.val+(a+1)*q) := by
    rw [mul_pow,hN,pow_add]
    exact Nat.mul_le_mul_right _ hi.1
  have hn : keys.length*(V*size a)^q ≤ 2^(q+inverseExponent a h u t.val+(a+1)*q) := by
    rw [mul_pow,hN,pow_add,pow_add]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul hlen (Nat.mul_le_mul_right (2^((a+1)*q)) hi.2)
  have heD : inverseExponent a h u t.val+(a+1)*q < W := by
    unfold sumExponent at hW
    dsimp only [q]
    omega
  have heN : q+inverseExponent a h u t.val+(a+1)*q < W := by
    unfold sumExponent at hW
    dsimp only [q]
    omega
  exact ⟨hr.2.trans_lt (hn.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) heN)),
    hr.1.trans_lt (hd.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) heD))⟩

/-- Actual retained inverse-times-power products derive normalization capacity
from the original cached inverse and argument representations. -/
theorem product_fits (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j k : ℕ) (hj : j ≤ k)
    (hk : k < nodeMultiplicity a h u t.val) (W : ℕ)
    (hW : inverseExponent a h u t.val+(a+1)*nodeMultiplicity a h u t.val < W) :
    Fits (coefficient (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients (k-j)*
      coefficient (powersRun (SemiprimeD1WeightPrecision.argument a t.val)
        (nodeMultiplicity a h u t.val)).value k) W := by
  let q:=nodeMultiplicity a h u t.val
  let D:=sourceDenominator a h u t.val
  let V:=inverseBase q D (sourceNumerator a h u t.val)
  rw [powersRun_coefficient _ q k hk]
  have hr:=representation_mul (original_inverse_representation a h u t hq (k-j) (by omega))
    (argument_power_representation a h u t k hk.le)
  have reduced:=representation_reduced_bound (Nat.mul_pos (pow_pos (sourceDenominator_pos a h u t.val) q)
    (by unfold size; positivity)) hr
  have hi:=inverse_power_bounds a h u t
  have hN : (size a)^q=2^((a+1)*q) := by unfold size; rw [← pow_mul]
  have hd : D^q*(size a)^q ≤ 2^(inverseExponent a h u t.val+(a+1)*q) := by
    rw [hN,pow_add]
    exact Nat.mul_le_mul_right _ hi.1
  have hn : V^q*(size a)^q ≤ 2^(inverseExponent a h u t.val+(a+1)*q) := by
    rw [hN,pow_add]
    exact Nat.mul_le_mul_right _ hi.2
  have ht : 2^(inverseExponent a h u t.val+(a+1)*q) < 2^W :=
    Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hW
  exact ⟨reduced.2.trans_lt (hn.trans_lt ht),reduced.1.trans_lt (hd.trans_lt ht)⟩

/-- Actual original local scalar sum refinement, with every coefficient read,
multiply, add and GCD normalization executing on physical words. -/
theorem sum_correct (template : List Bool) (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j : ℕ) (inverse powers : List RationalWord)
    (hi : inverse.map RationalWord.value=(SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients.toList)
    (hp : powers.map RationalWord.value=
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) (nodeMultiplicity a h u t.val)).value.toList)
    (hiv : ∀x∈inverse,x.Valid) (hpv : ∀x∈powers,x.Valid)
    (hW : sumExponent a h u t.val < template.length)
    (keys : List ℕ) (hk : ∀k∈keys,k < nodeMultiplicity a h u t.val)
    (hl : keys.length ≤ nodeMultiplicity a h u t.val) :
    (sum template (nodeMultiplicity a h u t.val) j inverse powers keys).word.value=
      (sumWeights j (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
        (powersRun (SemiprimeD1WeightPrecision.argument a t.val) (nodeMultiplicity a h u t.val)).value keys).value ∧
    (sum template (nodeMultiplicity a h u t.val) j inverse powers keys).word.Valid ∧
      Width (sum template (nodeMultiplicity a h u t.val) j inverse powers keys).word template.length := by
  have hpos : 0 < template.length := by omega
  have hprod : inverseExponent a h u t.val+(a+1)*nodeMultiplicity a h u t.val < template.length := by
    unfold sumExponent at hW
    omega
  induction keys with
  | nil =>
    refine ⟨?_,?_,?_⟩
    · norm_num [sum,sumWeights,SemiprimeRationalBits.zeroWord,RationalWord.value,
        SemiprimeBitIndexClipping.SignedWord.value,SemiprimeBitArithmetic.bitValue]
    · change 0 < 1; decide
    · exact ⟨by simp [sum,SemiprimeRationalBits.zeroWord],by change 1 ≤ template.length; omega⟩
  | cons k ks ih =>
    have hkt:=hk k List.mem_cons_self
    have tail:=ih (fun k h => hk k (List.mem_cons_of_mem _ h)) (by simp only [List.length_cons] at hl; omega)
    by_cases hj : j ≤ k
    · let q:=nodeMultiplicity a h u t.val
      let old:=sum template q j inverse powers ks
      let left:=read q inverse (k-j)
      let right:=read q powers k
      let product:=executeOperation .mul left.word right.word template
      have lv:=read_value q inverse (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
        (k-j) hi (by omega)
      have rv:=read_value q powers (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value k hp hkt
      have lvalid:=read_valid q inverse (k-j) hiv
      have rvalid:=read_valid q powers k hpv
      have productCap : Fits (Operation.mul.value left.word.value right.word.value) template.length := by
        rw [lv,rv]
        exact product_fits a h u t hq j k hj hkt template.length hprod
      have pm:=executeOperation_correct .mul left.word right.word template lvalid rvalid productCap
      have he : Operation.add.value product.word.value old.word.value=
          (sumWeights j (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
            (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value (k::ks)).value := by
        rw [pm.1,lv,rv,tail.1]
        simp only [Operation.value,sumWeights,hj,ite_true]
        rfl
      have addCap : Fits (Operation.add.value product.word.value old.word.value) template.length := by
        rw [he]
        exact sum_fits a h u t hq j (k::ks) hk hl template.length hW
      have out:=executeOperation_correct .add product.word old.word template pm.2.1 tail.2.1 addCap
      simpa only [sum,hj,ite_true] using And.intro (out.1.trans he) out.2
    · simpa only [sum,sumWeights,hj,ite_false] using tail

/-- Actual physical power cache, retaining every original power loop once. -/
structure Cache where
  /-- The physical power words in original order. -/
  words : List RationalWord
  /-- Actual multiplications/GCDs and constructors. -/
  clock : ℕ
  /-- Typed finite-index traversal stages, separate from physical arithmetic. -/
  metadataWork : ℕ

/-- Cache the executed powers on the ACTUAL original finite index list. -/
def powers (template : List Bool) (argument : RationalWord) : List ℕ → Cache
  | [] => ⟨[],1,1⟩
  | k::ks =>
    let tail:=powers template argument ks
    let current:=power template argument k
    ⟨current.word::tail.words,current.clock+tail.clock+3,tail.metadataWork+3⟩

/-- Original power-cache values, legality and widths have no scalar-power
answer or intermediate Fits premise. -/
theorem powers_correct (template : List Bool) (a h u : ℕ) (t : Fin (size a))
    (argument : RationalWord) (ha : argument.value=SemiprimeD1WeightPrecision.argument a t.val)
    (hav : argument.Valid) (hW : (a+1)*nodeMultiplicity a h u t.val+1 ≤ template.length)
    (keys : List ℕ) (hk : ∀k∈keys,k ≤ nodeMultiplicity a h u t.val) :
    (powers template argument keys).words.map RationalWord.value=
      keys.map (fun k => (rationalPower (SemiprimeD1WeightPrecision.argument a t.val) k).value) ∧
    (∀x∈(powers template argument keys).words,x.Valid) ∧
    (∀x∈(powers template argument keys).words,Width x template.length) := by
  have ht : 0 < template.length := by omega
  induction keys with
  | nil => exact ⟨rfl,by simp [powers],by simp [powers]⟩
  | cons k ks ih =>
    have old:=ih (fun k h => hk k (List.mem_cons_of_mem _ h))
    have cur:=argument_correct template argument a h u t k (hk k List.mem_cons_self) ha hav hW
    have width:=power_width template argument k ht
    refine ⟨?_,?_,?_⟩
    · simp only [powers,List.map_cons,cur.1,old.1]
    · intro x hx
      simp only [powers,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact cur.2
      · exact old.2.1 x hx
    · intro x hx
      simp only [powers,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact width
      · exact old.2.2 x hx

/-- The physical cache matches the exact frozen native cached power array. -/
theorem powers_original (template : List Bool) (a h u : ℕ) (t : Fin (size a))
    (argument : RationalWord) (ha : argument.value=SemiprimeD1WeightPrecision.argument a t.val)
    (hav : argument.Valid) (hW : (a+1)*nodeMultiplicity a h u t.val+1 ≤ template.length) :
    (powers template argument (indices (nodeMultiplicity a h u t.val)).value).words.map RationalWord.value=
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) (nodeMultiplicity a h u t.val)).value.toList := by
  have hk : ∀k∈(indices (nodeMultiplicity a h u t.val)).value,k ≤ nodeMultiplicity a h u t.val := by
    simp only [indices_value,List.mem_range]
    exact fun k h => h.le
  have h:=powers_correct template a h u t argument ha hav hW _ hk
  simpa only [powersRun,List.toList_toArray,List.map_map,Function.comp_def] using h.1

/-- Actual power-cache arithmetic reports are retained; no supplied native work cap. -/
theorem powers_clock (template : List Bool) (argument : RationalWord) (q : ℕ)
    (ht : 0 < template.length) (ha : Width argument template.length)
    (keys : List ℕ) (hk : ∀k∈keys,k ≤ q) :
    (powers template argument keys).clock ≤
      keys.length*(q*(20000*(template.length+1)^3+4)+6)+1 := by
  induction keys with
  | nil => simp [powers]
  | cons k ks ih =>
    have old:=ih (fun k h => hk k (List.mem_cons_of_mem _ h))
    have cur:=power_clock template argument k ht ha
    have hp:=Nat.mul_le_mul_right (20000*(template.length+1)^3+4) (hk k List.mem_cons_self)
    simp only [powers,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Exact native finite-index traversal report of the power cache. -/
theorem powers_metadataWork (template : List Bool) (argument : RationalWord) (keys : List ℕ) :
    (powers template argument keys).metadataWork=3*keys.length+1 := by
  induction keys with
  | nil => rfl
  | cons k ks ih => simp only [powers,List.length_cons,ih]; omega

/-- Physical normalization exposes actual canonical signed numerator and
positive-denominator words; no native q.num/q.den operation executes. -/
theorem operation_components (op : Operation) (x y : RationalWord) (template : List Bool)
    (hx : x.Valid) (hy : y.Valid) (hcap : Fits (op.value x.value y.value) template.length) :
    (executeOperation op x y template).word.numerator.value=(op.value x.value y.value).num ∧
      SemiprimeBitArithmetic.bitValue (executeOperation op x y template).word.denominator=(op.value x.value y.value).den := by
  have hv:=rawOperation_value op x y hx hy
  have hn : Fits (rawOperation op x y).word.value template.length := by rw [hv]; exact hcap
  have h:=fitRationalBits_components (rawOperation op x y).word template hn.1 hn.2
  simpa only [executeOperation,hv] using h

/-- Literal source-weight normalization capacity, derived from the actual
right-suffix common denominator and original integer factor heights. -/
theorem weight_fits (a h u : ℕ) (t : Fin (size a))
    (hq : 0 < nodeMultiplicity a h u t.val) (j W : ℕ)
    (hW : SemiprimeD1HermiteWeightBits.weightExponent a h u t.val < W) :
    Fits (weightRun (SemiprimeD1JetRecoveryGrid.Ezero a h u t.val) j
      (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) (nodeMultiplicity a h u t.val)).value
      (indices (nodeMultiplicity a h u t.val)).value).value W := by
  have hb:=weight_suffix_bits a h u t hq j 0
  simp only [List.drop_zero] at hb
  have ht : 2^SemiprimeD1HermiteWeightBits.weightExponent a h u t.val < 2^W :=
    Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hW
  exact ⟨hb.2.trans_lt ht,hb.1.trans_lt ht⟩

/-- Actual physical local weight and canonical numerator/denominator words
refine the original stored coefficient. No native canonical-field extraction
or intermediate/output Fits oracle is used at this endpoint. -/
theorem weight_correct (template : List Bool) (a h u : ℕ) (t : Fin (size a))
    (j : ℕ) (hj : j < nodeMultiplicity a h u t.val) (scalar : RationalWord)
    (inverse powers : List RationalWord)
    (hs : scalar.value=SemiprimeD1JetRecoveryGrid.Ezero a h u t.val) (hsv : scalar.Valid)
    (hi : inverse.map RationalWord.value=(SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients.toList)
    (hp : powers.map RationalWord.value=
      (powersRun (SemiprimeD1WeightPrecision.argument a t.val) (nodeMultiplicity a h u t.val)).value.toList)
    (hiv : ∀x∈inverse,x.Valid) (hpv : ∀x∈powers,x.Valid)
    (hW : sumExponent a h u t.val < template.length)
    (hWW : SemiprimeD1HermiteWeightBits.weightExponent a h u t.val < template.length) :
    let out:=weight template (nodeMultiplicity a h u t.val) j scalar inverse powers
      (indices (nodeMultiplicity a h u t.val)).value
    let target:=coefficient (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).weights j
    out.word.value=target ∧ out.word.Valid ∧ Width out.word template.length ∧
      out.word.numerator.value=target.num ∧ bitValue out.word.denominator=target.den := by
  dsimp only
  let q:=nodeMultiplicity a h u t.val
  let keys:=(indices q).value
  have hq : 0 < q := by omega
  have hk : ∀k∈keys,k < q := by simp only [keys,indices_value,List.mem_range]; exact fun k h => h
  have hlen : keys.length ≤ q := by simp [keys,indices_value]
  have total:=sum_correct template a h u t hq j inverse powers hi hp hiv hpv hW keys hk hlen
  have he : Operation.mul.value scalar.value (sum template q j inverse powers keys).word.value=
      (weightRun (SemiprimeD1JetRecoveryGrid.Ezero a h u t.val) j
        (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
        (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value keys).value := by
    rw [hs,total.1]
    rfl
  have cap : Fits (Operation.mul.value scalar.value (sum template q j inverse powers keys).word.value) template.length := by
    rw [he]
    exact weight_fits a h u t hq j template.length hWW
  have out:=executeOperation_correct .mul scalar (sum template q j inverse powers keys).word template hsv total.2.1 cap
  have canonical:=operation_components .mul scalar (sum template q j inverse powers keys).word template hsv total.2.1 cap
  have native : (weightRun (SemiprimeD1JetRecoveryGrid.Ezero a h u t.val) j
        (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).inverse.coefficients
        (powersRun (SemiprimeD1WeightPrecision.argument a t.val) q).value keys).value=
      coefficient (SemiprimeD1JetRecoveryWeights.acquire a h u t.val).weights j := by
    rw [weightRun_value]
    have hn:=SemiprimeD1JetRecoveryWeights.acquire_weight a h u t.val j hj
    simpa only [SemiprimeD1WeightPrecision.argument,Int.cast_neg,Int.cast_pow,Int.cast_ofNat] using hn.symm
  have equal:=he.trans native
  exact ⟨out.1.trans equal,out.2.1,out.2.2,by simpa only [weight,equal] using canonical.1,
    by simpa only [weight,equal] using canonical.2⟩

/-- Every scalar-sum output has bounded physical width even before semantics. -/
theorem sum_width (template : List Bool) (q j : ℕ) (inverse powers : List RationalWord)
    (keys : List ℕ) (ht : 0 < template.length) : Width (sum template q j inverse powers keys).word template.length := by
  induction keys with
  | nil => exact ⟨by simp [sum,SemiprimeRationalBits.zeroWord],by change 1 ≤ template.length; omega⟩
  | cons k ks ih =>
    simp only [sum]
    split_ifs
    · exact operation_width _ _ _ _
    · exact ih

/-- The exact physical memory/normalization budget for one retained-index visit. -/
def sumStepBudget (W q A : ℕ) : ℕ := 2*((A+1)*(8*W+15*(q+1)+30))+40000*(W+1)^3+10

/-- Every actual coefficient scan and normalized multiply/add is retained.
Only actual physical cache lengths/widths are required, not a work oracle. -/
theorem sum_clock (template : List Bool) (q j : ℕ) (inverse powers : List RationalWord)
    (keys : List ℕ) (ht : 0 < template.length) (A : ℕ)
    (hi : inverse.length ≤ A) (hp : powers.length ≤ A)
    (hiw : ∀x∈inverse,Width x template.length) (hpw : ∀x∈powers,Width x template.length) :
    (sum template q j inverse powers keys).clock ≤ keys.length*sumStepBudget template.length q A+3 := by
  induction keys with
  | nil => simp [sum]
  | cons k ks ih =>
    by_cases hj : j ≤ k
    · let old:=sum template q j inverse powers ks
      let left:=read q inverse (k-j)
      let right:=read q powers k
      let product:=executeOperation .mul left.word right.word template
      have lw:=read_width q inverse (k-j) template.length ht hiw
      have rw:=read_width q powers k template.length ht hpw
      have pw:=operation_width .mul left.word right.word template
      have ow:=sum_width template q j inverse powers ks ht
      have cl:=read_clock q inverse (k-j) template.length hiw
      have cr:=read_clock q powers k template.length hpw
      have cm:=executeOperation_cost .mul left.word right.word template lw rw le_rfl
      have ca:=executeOperation_cost .add product.word old.word template pw ow le_rfl
      have clb : (inverse.length+1)*(8*template.length+15*(q+1)+30) ≤
          (A+1)*(8*template.length+15*(q+1)+30) := Nat.mul_le_mul_right _ (by omega)
      have crb : (powers.length+1)*(8*template.length+15*(q+1)+30) ≤
          (A+1)*(8*template.length+15*(q+1)+30) := Nat.mul_le_mul_right _ (by omega)
      simp only [sum,hj,ite_true,List.length_cons,Nat.add_mul,Nat.one_mul]
      unfold sumStepBudget at *
      dsimp only [old,left,right,product] at *
      omega
    · simp only [sum,hj,ite_false,List.length_cons,Nat.add_mul,Nat.one_mul]
      have hb : 3 ≤ sumStepBudget template.length q A := by unfold sumStepBudget; omega
      omega

/-- Every native address-generation stage is retained for the actual scalar sum. -/
theorem sum_metadataWork (template : List Bool) (q j : ℕ) (inverse powers : List RationalWord)
    (keys : List ℕ) :
    (sum template q j inverse powers keys).metadataWork ≤ keys.length*(8*(q+1)+12)+1 := by
  induction keys with
  | nil => simp [sum]
  | cons k ks ih =>
    simp only [sum]
    split_ifs <;> dsimp only
    · simp only [read_metadataWork,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

/-- Full physical local-weight clock including the final real normalization. -/
theorem weight_clock (template : List Bool) (q j : ℕ) (scalar : RationalWord)
    (inverse powers : List RationalWord) (keys : List ℕ) (ht : 0 < template.length) (A : ℕ)
    (hi : inverse.length ≤ A) (hp : powers.length ≤ A)
    (hiw : ∀x∈inverse,Width x template.length) (hpw : ∀x∈powers,Width x template.length)
    (hs : Width scalar template.length) :
    (weight template q j scalar inverse powers keys).clock ≤
      keys.length*sumStepBudget template.length q A+20000*(template.length+1)^3+6 := by
  have hsum:=sum_clock template q j inverse powers keys ht A hi hp hiw hpw
  have hw:=sum_width template q j inverse powers keys ht
  have hout:=executeOperation_cost .mul scalar (sum template q j inverse powers keys).word template hs hw le_rfl
  simp only [weight]
  omega

end RiemannGaussian.SemiprimeD1RecoveryScalarWeightBits
