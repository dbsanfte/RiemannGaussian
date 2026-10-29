/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRecoveryGrid

/-! # Exact original dyadic-grid valuation tools
The valuation of a nonzero grid difference is determined by its complete residue
class. Literal odd-multiple parameterizations supply exact finite level counts.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1GridValuation
open scoped BigOperators

/-- Original nonzero bounded integer differences have order below the grid modulus. -/
theorem valuation_lt (k : ℕ) (x : ℤ) (hx : x≠0) (hb : x.natAbs<2^k) :
    padicValInt 2 x<k := by
  have hp : 2^padicValInt 2 x≤x.natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hx)) pow_padicValNat_dvd
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mp (hp.trans_lt hb)

/-- Nonzero orders below k are EXACTLY preserved by congruence modulo2^k.
No sign or nonzero-residue-field hypothesis is assumed for the second integer. -/
theorem valuation_congruent (k : ℕ) (x y : ℤ) (hx : x≠0)
    (hv : padicValInt 2 x<k) (hxy : (2:ℤ)^k∣x-y) :
    y≠0 ∧ padicValInt 2 y=padicValInt 2 x := by
  let v := padicValInt 2 x
  have hlowx : (2:ℤ)^v∣x := padicValInt_dvd _
  have hlowxy : (2:ℤ)^v∣x-y := (pow_dvd_pow 2 (by dsimp [v];omega)).trans hxy
  have hlowy : (2:ℤ)^v∣y := by
    have h := dvd_sub hlowx hlowxy
    convert h using 1;ring
  have hhighxy : (2:ℤ)^(v+1)∣x-y := (pow_dvd_pow 2 (by dsimp [v];omega)).trans hxy
  have hnotx : ¬(2:ℤ)^(v+1)∣x := by
    intro h
    rcases (padicValInt_dvd_iff (p:=2) _ _).mp h with h0|hle
    · exact hx h0
    · dsimp [v] at hle;omega
  have hnoty : ¬(2:ℤ)^(v+1)∣y := by
    intro h
    apply hnotx
    convert dvd_add hhighxy h using 1;ring
  have hy : y≠0 := by intro h;apply hnoty;rw [h];exact dvd_zero _
  refine ⟨hy,?_⟩
  have hle : v≤padicValInt 2 y := ((padicValInt_dvd_iff (p:=2) _ _).mp hlowy).resolve_left hy
  have hlt : padicValInt 2 y<v+1 := by
    by_contra h
    apply hnoty
    apply (padicValInt_dvd_iff (p:=2) _ _).mpr
    exact Or.inr (by omega)
  dsimp [v] at *
  omega

/-- The concrete integer remainder of a genuine bounded grid value has its exact order. -/
theorem remainder_valuation (k : ℕ) (x : ℤ) (hx : x≠0) (hb : x.natAbs<2^k) :
    x%((2:ℤ)^k)≠0 ∧ padicValInt 2 (x%((2:ℤ)^k))=padicValInt 2 x :=
  valuation_congruent k x _ hx (valuation_lt k x hx hb) Int.dvd_self_sub_emod

/-- Actual dyadic level set in the canonical complete residue grid. -/
def level (k v : ℕ) : Finset ℕ :=
  (Finset.range (2^k)).filter (fun q => q≠0 ∧ padicValNat 2 q=v)

/-- Literal increasing odd-multiple parameterization, not a cardinality oracle. -/
def oddMultiple (v r : ℕ) : ℕ := 2^v*(2*r+1)

/-- Every generated positive odd multiple has EXACTLY the requested order. -/
theorem oddMultiple_valuation (v r : ℕ) : padicValNat 2 (oddMultiple v r)=v := by
  have ho : ¬2∣2*r+1 := by omega
  have hn : 2*r+1≠0 := by omega
  rw [oddMultiple,padicValNat.mul (by positivity) hn,padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd ho,Nat.add_zero]

/-- Maximal valuation strips an ACTUAL positive integer to an odd quotient. -/
theorem quotient_odd (q : ℕ) (hq : q≠0) : Odd (q/2^padicValNat 2 q) := by
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  intro h
  obtain ⟨r,hr⟩ := h
  apply pow_succ_padicValNat_not_dvd (p:=2) hq
  refine ⟨r,?_⟩
  have he : q/2^padicValNat 2 q*2^padicValNat 2 q=q :=
    Nat.div_mul_cancel pow_padicValNat_dvd
  calc
    q = (q/2^padicValNat 2 q)*2^padicValNat 2 q := he.symm
    _ = (2*r)*2^padicValNat 2 q := by rw [hr]
    _ = 2^(padicValNat 2 q+1)*r := by rw [pow_succ];ring

/-- The original complete grid valuation level is the image of the actual odd list. -/
theorem level_eq_image (k v : ℕ) (hv : v<k) :
    level k v=(Finset.range (2^(k-v-1))).image (oddMultiple v) := by
  ext q
  simp only [level,Finset.mem_filter,Finset.mem_range,Finset.mem_image]
  constructor
  · rintro ⟨hq,hqn,hval⟩
    have ho := quotient_odd q hqn
    rw [hval] at ho
    obtain ⟨r,hr⟩ := ho
    have hrec : q=oddMultiple v r := by
      have he : q/2^v*2^v=q := by rw [← hval];exact Nat.div_mul_cancel pow_padicValNat_dvd
      unfold oddMultiple
      calc
        q = (q/2^v)*2^v := he.symm
        _ = _ := by rw [hr];ring
    refine ⟨r,?_,hrec.symm⟩
    have hk : 2^k=2^v*(2*2^(k-v-1)) := by
      rw [← pow_succ',← pow_add]
      congr 1
      omega
    rw [hrec,oddMultiple,hk] at hq
    have hp : 0<(2:ℕ)^v := by positivity
    nlinarith
  · rintro ⟨r,hr,rfl⟩
    refine ⟨?_,by unfold oddMultiple;positivity,oddMultiple_valuation v r⟩
    have hk : 2^k=2^v*(2*2^(k-v-1)) := by
      rw [← pow_succ',← pow_add]
      congr 1
      omega
    rw [oddMultiple,hk]
    have hp : 0<(2:ℕ)^v := by positivity
    nlinarith

/-- EXACT complete-residue-grid valuation counts, including the highest level. -/
theorem level_card (k v : ℕ) (hv : v<k) : (level k v).card=2^(k-v-1) := by
  rw [level_eq_image k v hv,Finset.card_image_of_injective]
  · simp
  · intro r s he
    unfold oddMultiple at he
    have hp : 0<(2:ℕ)^v := by positivity
    nlinarith

end RiemannGaussian.SemiprimeD1GridValuation
