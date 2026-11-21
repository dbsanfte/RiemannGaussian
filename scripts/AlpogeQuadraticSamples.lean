import AlpogeQuadraticPatterns
import AlpogeQuadraticPrefix

/-! # One pair of quadratic prime characters across the fourth-power zeta window -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real QuadraticPatterns

private def band (n : ℕ) := (Ioc (n^2) (n^4)).filter Nat.Prime
private def windowPrimes (m : ℕ) := (Ioc (m^2) (m^8)).filter Nat.Prime
private def term (n p : ℕ) := log p * weight (n^4) p

private theorem band_subset {m n : ℕ} (hn : n ∈ Icc m (m^2)) : band n ⊆ windowPrimes m := by
  obtain ⟨ha,hb⟩ := mem_Icc.mp hn
  intro p hp
  obtain ⟨h,hh⟩ := mem_filter.mp hp
  obtain ⟨h1,h2⟩ := mem_Ioc.mp h
  have h8 : (m^2)^4 = m^8 := by ring
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.pow_le_pow_left ha 2).trans_lt h1,
    (h2.trans (Nat.pow_le_pow_left hb 4)).trans_eq h8⟩,hh⟩

private theorem band_eq (n : ℕ) :
    largePrimeSum (n^4) = ∑ p ∈ band n, term n p := by
  have hs : sqrt ((n^4:ℕ):ℝ) = (n^2:ℕ) := by
    push_cast
    rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  unfold largePrimeSum band term
  congr 1
  ext p
  simp only [mem_filter,mem_Ioc,hs,Nat.cast_lt]
  constructor
  · rintro ⟨⟨⟨_,h⟩,hp⟩,hb⟩
    exact ⟨⟨hb,h⟩,hp⟩
  · rintro ⟨⟨hb,h⟩,hp⟩
    exact ⟨⟨⟨by omega,h⟩,hp⟩,hb⟩

/-- Weighted ordinary primes having prescribed quadratic signs modulo q and d. -/
def signedClassSum (q d n : ℕ) (α β : ℤ) : ℝ :=
  ∑ p ∈ (band n).filter (fun p : ℕ => jacobiSym (p:ℤ) q = α ∧ jacobiSym (p:ℤ) d = β), term n p

/-- The +1 modulo q, -1 modulo d class used in the four-character combination. -/
abbrev quadraticClassSum (q d n : ℕ) : ℝ := signedClassSum q d n 1 (-1)

/-- Congruences, ordering, and small-prime splitting required of the chosen pair.
The two auxiliary primes lie beyond the entire sample window. -/
def quadraticWindowPair (m q d : ℕ) : Prop :=
  q.Prime ∧ d.Prime ∧ m^8 < q ∧ q < d ∧ q % 8 = 3 ∧ d % 16 = 7 ∧
    q ∣ d+1 ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ m^2 → p ∣ d+1

private theorem realize_window {m : ℕ} (hm : 2 ≤ m) (s t : ℕ → ℤ)
    (hs : ∀ p, s p = 1 ∨ s p = -1) (ht : ∀ p, t p = 1 ∨ t p = -1) :
    ∃ q d : ℕ, quadraticWindowPair m q d ∧ ∀ p ∈ windowPrimes m,
      jacobiSym (p:ℤ) q = s p ∧ jacobiSym (p:ℤ) d = t p := by
  let S := windowPrimes m
  let small := (Ioc 2 (m^2)).filter Nat.Prime
  have hm2 : 2 ≤ m^2 := hm.trans (Nat.le_self_pow (by decide) _)
  have hpS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ p ≠ 2 := by
    obtain ⟨h,hh⟩ := mem_filter.mp hp
    exact ⟨hh,by have := (mem_Ioc.mp h).1; omega⟩
  obtain ⟨q,hq,hqp,hq16,_,hqsign⟩ := prime_pattern S ∅ (by simp) (by simpa using hpS)
    s hs 3 (by decide) (by decide) (m^8)
  have hm8 : m ≤ m^8 := Nat.le_self_pow (by decide) _
  have hdis : Disjoint S (insert q small) := by
    apply Finset.disjoint_left.mpr
    intro p hp h
    have hband := mem_Ioc.mp (mem_filter.mp hp).1
    rcases mem_insert.mp h with rfl | h
    · omega
    · have := (mem_Ioc.mp (mem_filter.mp h).1).2
      omega
  have hpri (p : ℕ) (h : p ∈ S ∪ insert q small) : p.Prime ∧ p ≠ 2 := by
    rcases mem_union.mp h with h | h
    · exact hpS p h
    rcases mem_insert.mp h with rfl | h
    · exact ⟨hqp,by omega⟩
    · exact ⟨(mem_filter.mp h).2,ne_of_gt (mem_Ioc.mp (mem_filter.mp h).1).1⟩
  obtain ⟨d,hd,hdp,hd16,hsplit,hdsign⟩ := prime_pattern S (insert q small) hdis hpri
    t ht 7 (by decide) (by decide) q
  refine ⟨q,d,⟨hqp,hdp,hq,hd,(hq16.of_dvd (by decide : 8 ∣ 16)),hd16,
    hsplit q (mem_insert_self _ _),?_⟩,fun p hp => ⟨hqsign p hp,hdsign p hp⟩⟩
  intro p hprime h2 hsmall
  exact hsplit p (mem_insert_of_mem (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := hprime.two_le; omega,hsmall⟩,hprime⟩))

private def primeLog (p : ℕ) : ℝ := if p.Prime then log p else 0

private theorem class_identity {m n q d : ℕ} (hn : n ∈ Icc m (m^2)) {s t : ℕ → ℤ}
    (hval : ∀ p ∈ windowPrimes m, jacobiSym (p:ℤ) q = s p ∧ jacobiSym (p:ℤ) d = t p)
    (α β : ℤ) :
    4*signedClassSum q d n α β-largePrimeSum (n^4) =
      ∑ p ∈ Ioc (n^2) (n^4), weight (n^4) p*
        (((if s p = α ∧ t p = β then (4:ℝ) else 0)-1)*primeLog p) := by
  classical
  rw [signedClassSum,sum_filter,band_eq,mul_sum,← sum_sub_distrib,band,sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : p.Prime
  · obtain ⟨h1,h2⟩ := hval p (band_subset hn (mem_filter.mpr ⟨hp,h⟩))
    rw [h1,h2]
    by_cases hh : s p = α ∧ t p = β <;> simp [hh,h,term,primeLog] <;> ring
  · simp [h,primeLog]

/-- Every fourth-power sample in the window obeys the same square-root times log
discrepancy bound, simultaneously for all four quadratic classes of one prime pair. -/
theorem exists_quadraticWindowPair_pointwise (m : ℕ) (hm : 2 ≤ m) :
    ∃ q d : ℕ, quadraticWindowPair m q d ∧
      ∀ n ∈ Icc m (m^2), ∀ α β : ℤ, (α = 1 ∨ α = -1) → (β = 1 ∨ β = -1) →
        |4*signedClassSum q d n α β-largePrimeSum (n^4)| ≤
          6*(1+2*(n:ℝ)^2)*log ((n:ℝ)^4+2) := by
  let L (j : ℕ) := log (j+1 : ℕ)
  have hL : Monotone L := by
    intro a b hab
    exact log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hab)
  have hg (p : ℕ) : 0 ≤ primeLog p ∧ primeLog p ≤ L (p+1) := by
    unfold primeLog L
    split
    · rename_i hp
      exact ⟨log_natCast_nonneg _,log_le_log (by exact_mod_cast hp.pos) (by push_cast; linarith)⟩
    · exact ⟨le_rfl,log_natCast_nonneg _⟩
  obtain ⟨s,t,hs,ht,hpref⟩ := QuadraticPrefix.prefix_four_classes (g := primeLog)
    (show 0 ≤ L 0 by simp [L]) hL hg
  obtain ⟨q,d,hpair,hval⟩ := realize_window hm s t hs ht
  refine ⟨q,d,hpair,fun n hn α β hα hβ => ?_⟩
  have hn2 : 2 ≤ n := hm.trans (mem_Icc.mp hn).1
  let v (p : ℕ) := ((if s p = α ∧ t p = β then (4:ℝ) else 0)-1)*primeLog p
  have hv (j : ℕ) (hj : j ≤ (n^2)^2+1) : |∑ p ∈ range j, v p| ≤ 3*log ((n:ℝ)^4+2) := by
    apply (hpref α β hα hβ j).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    dsimp [L]
    apply log_le_log (by positivity)
    rw [show (n^2)^2=n^4 by ring] at hj
    exact_mod_cast (by omega : j+1 ≤ n^4+2)
  have hlog : 0 ≤ log ((n:ℝ)^4+2) := log_nonneg (by linarith only [pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4])
  have hb := QuadraticPrefix.reciprocal_weight_bound (hn2.trans (Nat.le_self_pow (by decide) _)) v
    (mul_nonneg (by norm_num) hlog) hv
  rw [show (n^2)^2=n^4 by ring,Nat.cast_pow] at hb
  rw [class_identity hn hval]
  linarith only [hb]

end
end RiemannGaussian.AlpogeMined
