import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! # Coherent quadratic characters for a finite table of prime weights -/

namespace RiemannGaussian.QuadraticPatterns
open Finset

private theorem crt_prime (M : Finset ℕ) (a : ℕ → ℕ) (B : ℕ)
    (hn : ∀ k ∈ M, k ≠ 0) (hp : Set.Pairwise (M : Set ℕ) Nat.Coprime)
    (ha : ∀ k ∈ M, (a k).Coprime k) :
    ∃ q > B, q.Prime ∧ ∀ k ∈ M, q ≡ a k [MOD k] := by
  let v := Nat.chineseRemainderOfFinset a id M hn hp
  have hc : v.val.Coprime (∏ k ∈ M, k) := Nat.coprime_prod_right_iff.mpr fun k hk => by
    change v.val.gcd k = 1
    exact ((v.property k hk).gcd_eq).trans (ha k hk)
  obtain ⟨q,hq,hprime,hv⟩ := Nat.forall_exists_prime_gt_and_modEq B (prod_ne_zero_iff.mpr hn) hc
  exact ⟨q,hq,hprime,fun k hk => (hv.of_dvd (dvd_prod_of_mem id hk)).trans (v.property k hk)⟩

private theorem symbol_residue (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (z : ℤ)
    (hz : z = 1 ∨ z = -1) :
    ∃ a : ℕ, a.Coprime p ∧ jacobiSym a p = (if p % 4 = 1 then z else -z) := by
  let : Fact p.Prime := ⟨hp⟩
  let t := if p % 4 = 1 then z else -z
  have ht : t = 1 ∨ t = -1 := by unfold t; split <;> rcases hz with rfl | rfl <;> norm_num
  rcases ht with ht | ht
  · exact ⟨1,Nat.coprime_one_left _,by change jacobiSym (1:ℕ) p = t; simp [ht]⟩
  obtain ⟨u,hu⟩ := quadraticChar_exists_neg_one' (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨(u : ZMod p).val, (ZMod.isUnit_iff_coprime _ _).mp (by simp), ?_⟩
  change jacobiSym ((u : ZMod p).val:ℤ) p = t
  rw [ht,← jacobiSym.legendreSym.to_jacobiSym,legendreSym]
  simpa using hu

/-- Realize arbitrary signs on S by a single prime q, in the prescribed class modulo
16, while forcing q + 1 to be divisible by every prime of the disjoint set T. -/
theorem prime_pattern (S T : Finset ℕ) (hST : Disjoint S T)
    (hp : ∀ p ∈ S ∪ T, p.Prime ∧ p ≠ 2) (s : ℕ → ℤ)
    (hs : ∀ p, s p = 1 ∨ s p = -1) (r : ℕ) (hr : r.Coprime 16) (h4 : r % 4 = 3) (B : ℕ) :
    ∃ q > B, q.Prime ∧ q ≡ r [MOD 16] ∧ (∀ p ∈ T, p ∣ q+1) ∧
      ∀ p ∈ S, jacobiSym (p:ℤ) q = s p := by
  classical
  have hrp (p : ℕ) (h : p ∈ S) := hp p (mem_union_left _ h)
  choose a ha using fun p (h : p ∈ S) => symbol_residue p (hrp p h).1 (hrp p h).2 (s p) (hs p)
  let U := S ∪ T
  let M := insert 16 U
  let res (p : ℕ) := if p = 16 then r else if h : p ∈ S then a p h else p-1
  have hodd {p : ℕ} (h : p ∈ U) : p.Coprime 16 := by
    rw [show (16:ℕ) = 2^4 by decide]
    exact ((Nat.coprime_primes (hp p h).1 Nat.prime_two).mpr (hp p h).2).pow_right _
  have h16 {p : ℕ} (h : p ∈ U) : p ≠ 16 := by
    intro e
    have hh := (hp p h).1
    rw [e] at hh
    exact (by decide : ¬Nat.Prime 16) hh
  have hn (p : ℕ) (h : p ∈ M) : p ≠ 0 := by
    rcases mem_insert.mp h with rfl | h
    · decide
    · exact (hp p h).1.ne_zero
  have hpair : Set.Pairwise (M : Set ℕ) Nat.Coprime := by
    intro i hi j hj hij
    rcases mem_insert.mp hi with rfl | hi <;> rcases mem_insert.mp hj with rfl | hj
    · exact (hij rfl).elim
    · exact (hodd hj).symm
    · exact hodd hi
    · exact (Nat.coprime_primes (hp i hi).1 (hp j hj).1).mpr hij
  have hres (p : ℕ) (h : p ∈ M) : (res p).Coprime p := by
    rcases mem_insert.mp h with rfl | h
    · simpa [res] using hr
    by_cases hS : p ∈ S
    · simpa [res,h16 h,hS] using (ha p hS).1
    · have hpos := (hp p h).1.pos
      simpa [res,h16 h,hS,Nat.sub_add_cancel (by omega : 1 ≤ p)] using
        (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (p-1)) : (p-1).Coprime ((p-1)+1))
  obtain ⟨q,hq,hprime,he⟩ := crt_prime M res B hn hpair hres
  have hqr : q ≡ r [MOD 16] := by simpa [res] using he 16 (mem_insert_self _ _)
  have hq4 : q % 4 = 3 := Eq.trans (show q % 4 = r % 4 from hqr.of_dvd (by decide : 4 ∣ 16)) h4
  refine ⟨q,hq,hprime,hqr,fun p hT => ?_,fun p hS => ?_⟩
  · have hU : p ∈ U := mem_union_right _ hT
    have hnS : p ∉ S := fun hS => Finset.disjoint_left.mp hST hS hT
    have hh : q ≡ p-1 [MOD p] := by
      simpa [res,h16 hU,hnS] using he p (mem_insert_of_mem hU)
    have hp0 := (hp p hU).1.pos
    have hmod : q+1 ≡ 0 [MOD p] := by simpa [Nat.sub_add_cancel (by omega : 1 ≤ p),Nat.ModEq] using hh.add_right 1
    exact Nat.modEq_zero_iff_dvd.mp hmod
  · have hU : p ∈ U := mem_union_left _ hS
    let : Fact p.Prime := ⟨(hp p hU).1⟩
    let : Fact q.Prime := ⟨hprime⟩
    have hm : q ≡ a p hS [MOD p] := by
      simpa [res,h16 hU,hS] using he p (mem_insert_of_mem hU)
    have hleg : legendreSym p q = if p % 4 = 1 then s p else -s p := by
      rw [← (ha p hS).2,← jacobiSym.legendreSym.to_jacobiSym]
      unfold legendreSym
      congr 1
      push_cast
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    by_cases h1 : p % 4 = 1
    · rw [legendreSym.quadratic_reciprocity_one_mod_four h1 (by omega : q ≠ 2),hleg,ite_eq_left h1]
    · have h2 := (Nat.Prime.mod_two_eq_one_iff_ne_two (hp p hU).1).mpr (hp p hU).2
      rw [legendreSym.quadratic_reciprocity_three_mod_four (by omega : p % 4 = 3) hq4,hleg,ite_eq_right h1,neg_neg]

end RiemannGaussian.QuadraticPatterns
