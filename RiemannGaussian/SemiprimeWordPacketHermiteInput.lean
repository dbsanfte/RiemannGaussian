/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWordPacketCounter
import RiemannGaussian.SemiprimeMaterializedWordFibreBounds

/-! # A common Hermite input height for actual acquired word packets
The denominator below is proof-only. Runtime computes only the sum of actual
node widths; no large common denominator or encoded packet answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeWordPacketHermiteInput
open scoped BigOperators
open SemiprimeJetArrayHeight SemiprimeLocalExecutionHeight SemiprimeJetArray
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits
open SemiprimeNodeArrayExecution (RuntimeDesign)
open SemiprimeNativeBitsCounter (nodeWord nodeInt nodeWord_value nodeWord_valid)

/-- Runtime height parameter from actual packet metadata alone. -/
def packetBits {n F Q : ℕ} (b R J : ℕ) (arity : Fin F → ℕ)
    (design : Fin Q → RuntimeDesign n F) : ℕ :=
  2*(∑ a,SemiprimeWordPacketCounter.nodeWidth b R J arity (design a))+1

/-- Proof-only common denominator, permitting different group counts at each node. -/
def commonDenominator {n F Q : ℕ} (den : ℕ) (arity : Fin F → ℕ)
    (design : Fin Q → RuntimeDesign n F) : ℕ :=
  ∏ a,(SemiprimeNativeGroupBitsHeight.denominator den (∑ e,arity e) F)^(design a).r

/-- Homogenize a finite family without denominator multiplication at sum steps. -/
theorem homogenize {Q : ℕ} (d B W : Fin Q → ℕ) (q : Fin Q → ℚ)
    (hd : ∀ a,0<d a) (hdW : ∀ a,d a ≤ 2^(W a))
    (hBW : ∀ a,B a ≤ 2^(W a)) (hq : ∀ a,Representation (q a) (d a) (B a)) :
    let D := ∏ a,d a
    0<D ∧ D ≤ 2^(∑ a,W a) ∧
      ∀ a,Representation (q a) D (2^(2*(∑ a,W a)+1)) := by
  have hp : 0<∏ a,d a := Finset.prod_pos (fun a _ => hd a)
  have hb : (∏ a,d a) ≤ 2^(∑ a,W a) := by
    calc
      _ ≤ ∏ a,2^(W a) := Finset.prod_le_prod (fun a _ => hdW a)
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum]
  refine ⟨hp,hb,?_⟩
  intro a
  let c := ∏ x ∈ (Finset.univ.erase a),d x
  have hc : 0<c := Finset.prod_pos (fun x _ => hd x)
  have he : d a*c = ∏ x,d x := by
    simpa only [c] using Finset.mul_prod_erase Finset.univ d (Finset.mem_univ a)
  have hcD : c ≤ ∏ x,d x := by
    rw [← he]
    exact Nat.le_mul_of_pos_left c (hd a)
  have hBa : B a ≤ 2^(∑ x,W x) := (hBW a).trans
    (Nat.pow_le_pow_right (by decide) (Finset.single_le_sum (fun x _ => Nat.zero_le (W x)) (Finset.mem_univ a)))
  have hOne : Representation (1:ℚ) c c := by
    refine ⟨(c:ℤ),?_,by simp⟩
    simp only [Int.cast_natCast]
    exact (div_self (by exact_mod_cast (Nat.ne_of_gt hc))).symm
  have hh := representation_mul (hq a) hOne
  rw [mul_one,he] at hh
  apply representation_mono hh
  calc
    B a*c ≤ 2^(∑ x,W x)*2^(∑ x,W x) := Nat.mul_le_mul hBa (hcD.trans hb)
    _ = 2^(2*(∑ x,W x)) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- Every actual original node packet has a single common Hermite denominator.
Only original source and Boolean-entry bounds are premises. -/
theorem actual_nodes_bound {n F Q : ℕ} (b J R den B : ℕ)
    (arity : Fin F → ℕ) (design : Fin Q → RuntimeDesign n F)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (hvalid : ∀ e i v,Valid (source e i v)) (hd : 0<den)
    (hdb : den ≤ 2^b) (hBb : B ≤ 2^b) (hQb : Q ≤ 2^b)
    (hJb : J ≤ 2^b) (hnb : n ≤ 2^b)
    (hsource : ∀ e i v k,k ≤ R → Representation (coefficient (decode (source e i v)) k) den B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs ≤ 1) :
    let D := commonDenominator den arity design
    0<D ∧ D ≤ 2^(packetBits b R J arity design) ∧
    ∀ a,let out := SemiprimeWordPacketCounter.node b J R (design a) (nodeWord b a).word source entries;
      Valid out.words ∧ out.words.size=J ∧
        ArrayBound (decode out.words) J D (2^(packetBits b R J arity design)) := by
  let s := ∑ e,arity e
  let DG := SemiprimeNativeGroupBitsHeight.denominator den s F
  let BG := SemiprimeNativeGroupBitsHeight.numerator n J R den B Q s F
  let ds := fun a : Fin Q => DG^(design a).r
  let Bs := fun a : Fin Q => SemiprimeCounterEnumeration.weightedCount n (J-1)*
    (SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W*
      (SemiprimeWordPacketWidth.productBase J DG BG (SemiprimeWordPacketCounter.headCap (design a)))^(2*(design a).r))
  let Ws := fun a : Fin Q => SemiprimeWordPacketCounter.nodeWidth b R J arity (design a)
  let out := fun a : Fin Q => SemiprimeWordPacketCounter.node b J R (design a)
    (nodeWord b a).word source entries
  have hDG := SemiprimeNativeGroupBitsHeight.denominator_dyadic b R den s F hdb
  have hBG := SemiprimeNativeGroupBitsHeight.numerator_dyadic b R J den B Q n s F hdb hBb hQb hJb hnb
  have hpos : ∀ a,0<ds a := fun a => pow_pos
    (SemiprimeNativeGroupBitsHeight.denominator_pos den s F hd) _
  have hdW : ∀ a,ds a ≤ 2^(Ws a) := by
    intro a
    exact (SemiprimeWordPacketWidth.fibre_denominator_lt b R n F s J (design a).r
      (SemiprimeWordPacketCounter.headCap (design a))
      (SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W)
      (SemiprimeCounterEnumeration.weightedCount n (J-1)) DG hDG).le
  have hBW : ∀ a,Bs a ≤ 2^(Ws a) := by
    intro a
    have h := SemiprimeWordPacketWidth.support_numerator_lt b R n F s J (design a).r
      (SemiprimeWordPacketCounter.headCap (design a))
      (SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W)
      (SemiprimeCounterEnumeration.weightedCount n (J-1)) DG BG hDG hBG
    simpa only [Bs,Ws,SemiprimeWordPacketCounter.nodeWidth,s,Nat.mul_assoc] using h.le
  have hs (a : Fin Q) := SemiprimeWordPacketCounter.node_spec b J R den B Q (design a) source
    (nodeWord b a).word (nodeInt a) entries hvalid (nodeWord_valid b Q a)
    (nodeWord_value b Q a hQb) hd (by change a.val+1 ≤ Q; omega)
    hdb hBb hQb hJb hnb hsource hentries
  have hp : 0<∏ a,ds a := Finset.prod_pos (fun a _ => hpos a)
  have hD : (∏ a,ds a) ≤ 2^(∑ a,Ws a) := by
    calc
      _ ≤ ∏ a,2^(Ws a) := Finset.prod_le_prod (fun a _ => hdW a)
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum]
  refine ⟨hp,?_,?_⟩
  · exact hD.trans (Nat.pow_le_pow_right (by decide) (by dsimp only [packetBits,Ws]; omega))
  · intro a
    refine ⟨(hs a).2.1,?_,?_⟩
    · exact SemiprimeMaterializedWordFibreBounds.node_size _ J (design a) _
    · intro k hk
      have hh := homogenize ds Bs Ws (fun x => coefficient (decode (out x).words) k)
        hpos hdW hBW (fun x => (hs x).2.2 k hk)
      exact hh.2.2 a

end RiemannGaussian.SemiprimeWordPacketHermiteInput
