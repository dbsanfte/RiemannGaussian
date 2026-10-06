/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryCorrelation

/-!
# The literal lagged carry quadratic

The joined quadratic retains all prime powers and the original complex
phase. Only at height zero is it a positive Gram quadratic. The cyclic
autocorrelation of each denominator is an exact two-spike computation.
-/

namespace RiemannGaussian.SuzukiCarryGram
noncomputable section
open scoped BigOperators ComplexConjugate
open SuzukiIntegerCarry SuzukiCarryCorrelation Complex

/-- A finitely supported linear packet of literal signed carry increments. -/
def packet (S : Finset ℕ) (alpha : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ N ∈ S, alpha N * (incidence N d : ℂ)

/-- The nonnegative arithmetic kernel obtained after joining both incidences. -/
def packetMass (S : Finset ℕ) (alpha : ℕ → ℂ) (d : ℕ) : ℝ :=
  Complex.normSq (packet S alpha d)

/-- The full phase-retaining quadratic on one common finite prime support. -/
def quadratic (X : ℕ) (S : Finset ℕ) (alpha : ℕ → ℂ) (phase : ℕ → ℂ) : ℂ :=
  ∑ N ∈ S, ∑ M ∈ S, alpha N * conj (alpha M) * correlation X N M phase

/-- Every coefficient packet has nonnegative squared mass; this does not
assert positivity of the complex, height-twisted quadratic. -/
theorem packetMass_nonneg (S : Finset ℕ) (alpha : ℕ → ℂ) (d : ℕ) :
    0 ≤ packetMass S alpha d := Complex.normSq_nonneg _

private theorem joined_atom (S : Finset ℕ) (alpha : ℕ → ℂ) (d : ℕ) :
    (∑ N ∈ S, ∑ M ∈ S,
      alpha N * conj (alpha M) * ((incidence N d * incidence M d : ℝ) : ℂ)) =
        (packetMass S alpha d : ℂ) := by
  classical
  calc
    _ = (∑ N ∈ S, alpha N * (incidence N d : ℂ)) *
        (∑ M ∈ S, conj (alpha M) * (incidence M d : ℂ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro N _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      push_cast
      ring
    _ = packet S alpha d * conj (packet S alpha d) := by
      simp only [packet, map_sum, map_mul, Complex.conj_ofReal]
    _ = _ := Complex.mul_conj _

/-- Exact quadratic identity, before any norm or positive-part bound.
The arbitrary complex phase stays inside the joined prime-power sum. -/
theorem quadratic_eq_joined (X : ℕ) (S : Finset ℕ) (alpha : ℕ → ℂ)
    (phase : ℕ → ℂ) :
    quadratic X S alpha phase =
      ∑ d ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt d : ℂ) * phase d * (packetMass S alpha d : ℂ) := by
  classical
  unfold quadratic correlation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm, ← joined_atom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  ring

/-- The literal fixed-height carry-Gram identity, including every prime power. -/
theorem primePhase_quadratic_eq_joined (X : ℕ) (S : Finset ℕ) (alpha : ℕ → ℂ)
    (y : ℝ) :
    quadratic X S alpha (primePhase y) =
      ∑ d ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt d : ℂ) * primePhase y d *
          (packetMass S alpha d : ℂ) := quadratic_eq_joined X S alpha _

/-- A complete Gram entry uses the finite support of both incidences,
not a physically truncated prime population. -/
def fullGram (N M : ℕ) (phase : ℕ → ℂ) : ℂ :=
  correlation (2*(max N M+1)) N M phase

/-- The complete Gram has exactly the integer endpoint gcd formula. -/
theorem fullGram_eq_gcd_sum (N M : ℕ) (phase : ℕ → ℂ) :
    fullGram N M phase = ∑ i : Fin 3, ∑ j : Fin 3,
      ((endpointSign i*endpointSign j : ℝ) : ℂ)*
        divisorPhase phase (Nat.gcd (endpoint N i) (endpoint M j)) := by
  exact correlation_eq_gcd_sum (by have := le_max_left N M; omega) phase

/-- Any common cutoff containing the first row computes the complete entry. -/
theorem fullGram_eq_correlation {X N M : ℕ} (hN : 2*(N+1) ≤ X) (phase : ℕ → ℂ) :
    fullGram N M phase = correlation X N M phase := by
  rw [fullGram_eq_gcd_sum, correlation_eq_gcd_sum hN]

/-- The complete matrix quadratic, with an arbitrary finite coefficient support. -/
def fullQuadratic (S : Finset ℕ) (alpha : ℕ → ℂ) (phase : ℕ → ℂ) : ℂ :=
  ∑ N ∈ S, ∑ M ∈ S, alpha N*conj (alpha M)*fullGram N M phase

/-- Common-support conversion retains every selected prime-power incidence. -/
theorem fullQuadratic_eq_quadratic {X : ℕ} (S : Finset ℕ) (alpha : ℕ → ℂ)
    (phase : ℕ → ℂ) (hS : ∀ N ∈ S, 2*(N+1) ≤ X) :
    fullQuadratic S alpha phase = quadratic X S alpha phase := by
  unfold fullQuadratic quadratic
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M _
  rw [fullGram_eq_correlation (hS N hN)]

/-- The full finite-support quadratic has no omitted prime powers.
The displayed support is canonical and contains every active increment. -/
theorem fullQuadratic_eq_joined (S : Finset ℕ) (alpha : ℕ → ℂ) (phase : ℕ → ℂ) :
    fullQuadratic S alpha phase =
      ∑ d ∈ Finset.Icc 1 (2*(S.sup id+1)),
        (ArithmeticFunction.vonMangoldt d : ℂ)*phase d*(packetMass S alpha d : ℂ) := by
  rw [fullQuadratic_eq_quadratic (X := 2*(S.sup id+1)) S alpha phase (fun N hN => by
    have h : N ≤ S.sup id := Finset.le_sup (f := id) hN
    omega), quadratic_eq_joined]

/-- Constant coefficients telescope exactly, with no prime-period boundary discarded. -/
theorem packet_interval_eq {A B : ℕ} (hAB : A ≤ B) (d : ℕ) :
    packet (Finset.Ico A B) (fun _ => 1) d = ((carry B d : ℝ)-(carry A d : ℝ) : ℝ) := by
  have he : (∑ N ∈ Finset.Ico A B, incidence N d) = (carry B d : ℝ)-(carry A d : ℝ) := by
    unfold incidence
    rw [Finset.sum_Ico_eq_sub _ hAB,
      Finset.sum_range_sub (fun k => (carry k d : ℝ)) B,
      Finset.sum_range_sub (fun k => (carry k d : ℝ)) A]
    ring
  simpa only [packet, one_mul, ← Complex.ofReal_sum] using congrArg (Complex.ofReal) he

/-- The flat packet joins the two endpoint carries as one exact kernel. -/
theorem packetMass_interval_eq {A B : ℕ} (hAB : A ≤ B) (d : ℕ) :
    packetMass (Finset.Ico A B) (fun _ => 1) d =
      (carry B d : ℝ)+(carry A d : ℝ)-2*(carry B d : ℝ)*(carry A d : ℝ) := by
  rw [packetMass, packet_interval_eq hAB]
  rcases carry_eq_zero_or_one A d with ha | ha <;>
    rcases carry_eq_zero_or_one B d with hb | hb <;> norm_num [ha, hb]

/-- The positive height-zero mass still dominates a linear carry increment.
This prevents paying the twisted quadratic by its whole positive mass. -/
theorem packetMass_interval_ge {A B : ℕ} (hAB : A ≤ B) (d : ℕ) :
    (carry B d : ℝ)-(carry A d : ℝ) ≤ packetMass (Finset.Ico A B) (fun _ => 1) d := by
  rw [packetMass_interval_eq hAB]
  rcases carry_eq_zero_or_one A d with ha | ha <;>
    rcases carry_eq_zero_or_one B d with hb | hb <;> norm_num [ha, hb]

private theorem extended_primeCarry {N X : ℕ} (hNX : 2*N ≤ X) :
    (∑ d ∈ Finset.Icc 1 X, (carry N d : ℝ)*ArithmeticFunction.vonMangoldt d) = primeCarry N := by
  unfold primeCarry
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hNX)
  intro d hdX hdN
  have hd : 2*N < d := by
    have := (Finset.mem_Icc.mp hdX).1
    simp only [Finset.mem_Icc] at hdN
    omega
  simp [carry_eq_zero_of_lt hd]

/-- An unconditional linear-minus-logarithmic lower bound for the flat
packet's unsigned mass. It is an obstruction audit, not a signed payment. -/
theorem flat_zeroHeight_mass_lower {X A : ℕ} (hX : 4*A ≤ X) :
    (A : ℝ)*Real.log 4-Real.log (4*A+1 : ℕ) ≤
      (quadratic X (Finset.Ico A (2*A)) (fun _ => 1) (primePhase 0)).re := by
  rw [primePhase_quadratic_eq_joined]
  simp only [primePhase, Complex.ofReal_zero, mul_zero, neg_zero, zero_mul,
    Complex.exp_zero, mul_one, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]
  have he : primeCarry (2*A)-primeCarry A ≤
      ∑ d ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt d*
        packetMass (Finset.Ico A (2*A)) (fun _ => 1) d := by
    rw [← extended_primeCarry (by omega : 2*(2*A) ≤ X),
      ← extended_primeCarry (by omega : 2*A ≤ X), ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro d _
    have h := mul_le_mul_of_nonneg_right (packetMass_interval_ge (by omega : A ≤ 2*A) d)
      (@ArithmeticFunction.vonMangoldt_nonneg d)
    nlinarith
  have hlo := (primeCarry_bounds (2*A)).1
  have hhi := (primeCarry_bounds A).2
  push_cast at hlo
  rw [show 2*(2*(A : ℝ))+1 = 4*(A : ℝ)+1 by ring] at hlo
  exact (by push_cast; nlinarith : (A : ℝ)*Real.log 4-Real.log (4*A+1 : ℕ) ≤ primeCarry (2*A)-primeCarry A).trans he

/-- The genuine positive Gram statement is restricted to zero height. -/
theorem quadratic_zeroHeight_nonneg (X : ℕ) (S : Finset ℕ) (alpha : ℕ → ℂ) :
    0 ≤ (quadratic X S alpha (primePhase 0)).re := by
  rw [primePhase_quadratic_eq_joined]
  simp only [primePhase, Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero,
    mul_one, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun d _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (packetMass_nonneg S alpha d))

/-- The literal incidence is periodic, including each discontinuity endpoint. -/
theorem incidence_mod (N d : ℕ) : incidence N d = incidence (N%d) d := by
  simp only [incidence_eq_divisorIndicators, divisorIndicator, Nat.dvd_iff_mod_eq_zero]
  simp [Nat.add_mod, Nat.mul_mod]

private theorem carry_lt_period {N d : ℕ} (hN : N < d) :
    carry N d = if d ≤ 2*N then 1 else 0 := by
  unfold carry
  rw [Nat.div_eq_of_lt hN, mul_zero, Nat.sub_zero]
  split_ifs with h
  · apply Nat.div_eq_of_lt_le <;> omega
  · exact Nat.div_eq_of_lt (by omega)

/-- The increment has one positive and one negative atom in each period. -/
theorem incidence_two_spikes {d : ℕ} (hd : 2 ≤ d) (N : ℕ) :
    incidence N d = (if N%d = (d-1)/2 then (1 : ℝ) else 0) -
      (if N%d = d-1 then (1 : ℝ) else 0) := by
  rw [incidence_mod]
  have hN : N%d < d := Nat.mod_lt N (by omega)
  unfold incidence
  rw [carry_lt_period hN]
  by_cases hlast : N%d = d-1
  · have he : N%d+1 = d := by omega
    have hz : carry d d = 0 := by
      unfold carry
      rw [Nat.mul_div_cancel _ (by omega : 0 < d), Nat.div_self (by omega : 0 < d)]
    rw [he, hz]
    have hnot : d-1 ≠ (d-1)/2 := by omega
    norm_num [hlast, hnot, show d ≤ 2*(d-1) by omega]
  · have hnext : N%d+1 < d := by omega
    rw [carry_lt_period hnext]
    by_cases hmid : N%d = (d-1)/2
    · norm_num [hmid, show (d-1)/2 ≠ d-1 by omega, show d ≤ 2*((d-1)/2+1) by omega,
        show ¬d ≤ 2*((d-1)/2) by omega]
    · split_ifs <;> norm_num <;> omega

/-- The exact coefficient functional samples two arithmetic progressions.
This is useful for smooth/Fejer packets without removing the complex coefficients. -/
theorem packet_eq_residue_sums {d : ℕ} (hd : 2 ≤ d)
    (S : Finset ℕ) (alpha : ℕ → ℂ) :
    packet S alpha d =
      (∑ N ∈ S.filter (fun N => N%d = (d-1)/2), alpha N) -
        (∑ N ∈ S.filter (fun N => N%d = d-1), alpha N) := by
  classical
  unfold packet
  simp_rw [incidence_two_spikes hd, Complex.ofReal_sub, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_filter, Finset.sum_filter]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro N _
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- A complete arithmetic period cancels, including the endpoints. -/
theorem carry_add_multiple_period (N d q : ℕ) : carry (N+d*q) d = carry N d := by
  by_cases hd : d = 0
  · simp [carry, hd]
  have hp : 0 < d := Nat.pos_of_ne_zero hd
  unfold carry
  rw [show 2*(N+d*q) = 2*N+d*(2*q) by ring,
    Nat.add_mul_div_left _ _ hp, Nat.add_mul_div_left _ _ hp]
  omega

/-- Flat packets vanish exactly on denominators dividing their full period. -/
theorem packet_interval_eq_zero_of_dvd {A H d : ℕ} (hd : d ∣ H) :
    packet (Finset.Ico A (A+H)) (fun _ => 1) d = 0 := by
  obtain ⟨q, rfl⟩ := hd
  rw [packet_interval_eq (by omega), carry_add_multiple_period]
  simp

/-- Distinct incidence rows cannot share a denominator larger than their
separation budget. The statement is pointwise, not an averaged cancellation. -/
theorem incidence_lag_product_eq_zero {N H d : ℕ} (hH : 0 < H) (hd : 2*H+1 < d) :
    incidence N d*incidence (N+H) d = 0 := by
  by_cases hn : incidence N d = 0
  · simp [hn]
  by_cases hm : incidence (N+H) d = 0
  · simp [hm]
  rcases incidence_support hn with ha | hb <;> rcases incidence_support hm with hc | he
  · have hh : d ∣ 2*H := by
      simpa only [show (2*(N+H)+1)-(2*N+1) = 2*H by omega] using Nat.dvd_sub hc ha
    have := Nat.le_of_dvd (by omega : 0 < 2*H) hh
    omega
  · have hh : d ∣ 2*H+1 := by
      simpa only [show (2*(N+H)+2)-(2*N+1) = 2*H+1 by omega] using Nat.dvd_sub he ha
    have := Nat.le_of_dvd (by omega : 0 < 2*H+1) hh
    omega
  · have hh : d ∣ 2*H-1 := by
      simpa only [show (2*(N+H)+1)-(2*N+2) = 2*H-1 by omega] using Nat.dvd_sub hc hb
    have := Nat.le_of_dvd (by omega : 0 < 2*H-1) hh
    omega
  · have hh : d ∣ 2*H := by
      simpa only [show (2*(N+H)+2)-(2*N+2) = 2*H by omega] using Nat.dvd_sub he hb
    have := Nat.le_of_dvd (by omega : 0 < 2*H) hh
    omega

/-- At a fixed nonzero lag, the complete Gram involves only prime powers
at most `2*H+1`, uniformly in the absolute scale. All phases are unchanged. -/
theorem fullGram_lag_eq_short_sum {H : ℕ} (hH : 0 < H) (N : ℕ) (phase : ℕ → ℂ) :
    fullGram N (N+H) phase = ∑ d ∈ Finset.Icc 1 (2*H+1),
      ((incidence N d*incidence (N+H) d : ℝ) : ℂ)*
        (ArithmeticFunction.vonMangoldt d : ℂ)*phase d := by
  unfold fullGram correlation
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega))
  intro d hdX hdH
  have hd : 2*H+1 < d := by
    have := (Finset.mem_Icc.mp hdX).1
    simp only [Finset.mem_Icc] at hdH
    omega
  rw [incidence_lag_product_eq_zero hH hd]
  simp

/-- The exact periodic lag autocorrelation; the normalization is literal. -/
def lagAutocorrelation (d h : ℕ) : ℝ :=
  (∑ N ∈ Finset.range d, incidence N d * incidence (N+h) d) / d

private theorem cyclic_atom_sum {d a b : ℕ} (ha : a < d) (h : ℕ) :
    (∑ N ∈ Finset.range d,
      (if N%d = a then (1 : ℝ) else 0) *
        (if (N+h)%d = b then (1 : ℝ) else 0)) =
      if (a+h)%d = b then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_eq_single a]
  · simp [Nat.mod_eq_of_lt ha]
  · intro N hN hne
    have hna : N%d ≠ a := by simpa [Nat.mod_eq_of_lt (Finset.mem_range.mp hN)] using hne
    simp [hna]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr ha))

/-- Every nontrivial denominator has only three possible nonzero lag
residues. For an even denominator the two negative residues coincide. -/
theorem lagAutocorrelation_eq {d : ℕ} (hd : 2 ≤ d) (h : ℕ) :
    lagAutocorrelation d h =
      (2*(if h%d = 0 then (1 : ℝ) else 0) -
        (if h%d = d/2 then (1 : ℝ) else 0) -
        (if h%d = d-d/2 then (1 : ℝ) else 0)) / d := by
  have ha : (d-1)/2 < d := by omega
  have hb : d-1 < d := by omega
  have hm : h%d < d := Nat.mod_lt h (by omega)
  have haa : ((d-1)/2+h)%d = (d-1)/2 ↔ h%d = 0 := by
    have hh := Nat.add_mod_add_ite ((d-1)/2) h d
    rw [Nat.mod_eq_of_lt ha] at hh
    split_ifs at hh <;> omega
  have hbb : (d-1+h)%d = d-1 ↔ h%d = 0 := by
    have hh := Nat.add_mod_add_ite (d-1) h d
    rw [Nat.mod_eq_of_lt hb] at hh
    split_ifs at hh <;> omega
  have hab : ((d-1)/2+h)%d = d-1 ↔ h%d = d/2 := by
    have hh := Nat.add_mod_add_ite ((d-1)/2) h d
    rw [Nat.mod_eq_of_lt ha] at hh
    split_ifs at hh <;> omega
  have hba : (d-1+h)%d = (d-1)/2 ↔ h%d = d-d/2 := by
    have hh := Nat.add_mod_add_ite (d-1) h d
    rw [Nat.mod_eq_of_lt hb] at hh
    split_ifs at hh <;> omega
  unfold lagAutocorrelation
  simp_rw [incidence_two_spikes hd]
  have hexp (N : ℕ) :
      ((if N%d = (d-1)/2 then (1 : ℝ) else 0) - (if N%d = d-1 then (1 : ℝ) else 0)) *
        ((if (N+h)%d = (d-1)/2 then (1 : ℝ) else 0) -
          (if (N+h)%d = d-1 then (1 : ℝ) else 0)) =
      (if N%d = (d-1)/2 then (1 : ℝ) else 0) * (if (N+h)%d = (d-1)/2 then (1 : ℝ) else 0) -
      (if N%d = (d-1)/2 then (1 : ℝ) else 0) * (if (N+h)%d = d-1 then (1 : ℝ) else 0) -
      (if N%d = d-1 then (1 : ℝ) else 0) * (if (N+h)%d = (d-1)/2 then (1 : ℝ) else 0) +
      (if N%d = d-1 then (1 : ℝ) else 0) * (if (N+h)%d = d-1 then (1 : ℝ) else 0) := by ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    cyclic_atom_sum ha, cyclic_atom_sum ha, cyclic_atom_sum hb, cyclic_atom_sum hb]
  simp_rw [haa, hab, hba, hbb]
  ring

/-- Trivial denominators have no carry incidence or lag contribution. -/
theorem lagAutocorrelation_zero_one (h : ℕ) :
    lagAutocorrelation 0 h = 0 ∧ lagAutocorrelation 1 h = 0 := by
  simp [lagAutocorrelation, incidence, carry]

end
end RiemannGaussian.SuzukiCarryGram
