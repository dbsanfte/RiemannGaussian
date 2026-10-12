/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorPowerCovariance
import RiemannGaussian.ArithmeticOperatorFloorInverseAudit

/-!
# Full prime-power GCD contrasts have only the old diagonal source

The matrix kernel can be nonseparable and can include every moving
height, Gaussian, modular and physical code. Its coprime contrast is
zero on different prime bases. After the EXACT diagonal is retained,
every surviving entry involves two different powers of one prime, hence
that prime is below the square-root cutoff. Polynomial-logarithmic kernel
budgets give source-o(1) for every exponent above one half.

This is an actual-prime support theorem, not a free-weight PSD argument.
The diagonal is NOT paid. Coprime distinct-column CRT/order kernels,
power-growing amplitudes and an independent estimate for the retained
diagonal are outside the claim.
-/

namespace RiemannGaussian.ArithmeticOperatorPrimeGcdContrast
noncomputable section
open Complex Filter ArithmeticOperatorPowerCovariance
open ArithmeticOperatorFloorInverseAudit
open scoped BigOperators Topology

/-- All actual prime bases and positive powers in the physical exponent
rectangle. Values outside the cutoff must be zero in the literal kernel. -/
def interaction (P : Finset ℕ) (J : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, ∑ q ∈ P, (Real.log p : ℂ)*(Real.log q : ℂ)*
    ∑ r ∈ orders J, ∑ s ∈ orders J, K (p^r) (q^s)

/-- Every same-label prime-power entry, including every proper power
and its original complex matrix phase. This is the UNPAID part. -/
def diagonal (P : Finset ℕ) (J : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)^2*∑ r ∈ orders J, K (p^r) (p^r)

/-- Entire non-diagonal contrast after the distinct-prime support join. -/
def cross (P : Finset ℕ) (J : ℕ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)^2*∑ r ∈ orders J,
    ∑ s ∈ (orders J).erase r, K (p^r) (p^s)

/-- Exact finite integer reduction BEFORE any norm: different prime
bases are coprime at every power, leaving the full diagonal plus one
same-base cross matrix. No actual-prime phase is discarded. -/
theorem interaction_eq_diagonal_add_cross (P : Finset ℕ) (J : ℕ)
    (K : ℕ → ℕ → ℂ) (hP : ∀ p ∈ P, p.Prime)
    (hcoprime : ∀ d e, Nat.Coprime d e → K d e=0) :
    interaction P J K=diagonal P J K+cross P J K := by
  classical
  have hb : interaction P J K=
      ∑ p ∈ P, (Real.log p : ℂ)^2*∑ r ∈ orders J, ∑ s ∈ orders J, K (p^r) (p^s) := by
    unfold interaction
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_eq_single p]
    · ring
    · intro q hq hqp
      have hz : (∑ r ∈ orders J, ∑ s ∈ orders J, K (p^r) (q^s))=0 := by
        apply Finset.sum_eq_zero
        intro r _
        apply Finset.sum_eq_zero
        intro s _
        exact hcoprime _ _ (Nat.coprime_pow_primes r s (hP p hp) (hP q hq) hqp.symm)
      rw [hz,mul_zero]
    · intro hh
      exact (hh hp).elim
  rw [hb]
  unfold diagonal cross
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [←mul_add]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [←Finset.sum_erase_add _ _ hr]
  ring

/-- The physical exponent rectangle omits only entries that are EXACTLY
zero, not a prime-power error assigned a heuristic rate. -/
theorem active_order_mem {p r e J : ℕ} (hp : p.Prime) (hr : 0<r)
    {K : ℕ → ℕ → ℂ} (hphysical : ∀ d e, 2^(2*J)<d ∨ 2^(2*J)<e → K d e=0)
    (hactive : K (p^r) e≠0) : r ∈ orders J := by
  have hcut : p^r≤2^(2*J) := by
    by_contra hh
    exact hactive (hphysical _ _ (Or.inl (by omega)))
  have hmin : (2 : ℕ)^r≤p^r := Nat.pow_le_pow_left hp.two_le _
  have hrmax : r≤2*J := (Nat.pow_le_pow_iff_right (by norm_num : 1<(2 : ℕ))).mp
    (hmin.trans hcut)
  exact Finset.mem_Icc.mpr ⟨hr,hrmax⟩

/-- Arbitrary nonseparable common-prime cross terms have exact small-base
support. All row/column phases remain INSIDE K during this reduction. -/
theorem cross_eq_small (P : Finset ℕ) (J : ℕ) (K : ℕ → ℕ → ℂ)
    (hphysical : ∀ d e, 2^(2*J)<d ∨ 2^(2*J)<e → K d e=0) :
    cross P J K=cross (P.filter (fun p => p≤2^J)) J K := by
  classical
  unfold cross
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpnot
  have hlarge : 2^J<p := by
    by_contra hh
    exact hpnot (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro s hs
  have hr1 : 1≤r := (Finset.mem_Icc.mp hr).1
  have hs1 : 1≤s := (Finset.mem_Icc.mp (Finset.mem_erase.mp hs).2).1
  have hsr : s≠r := (Finset.mem_erase.mp hs).1
  by_cases hrr : 2≤r
  · exact higher_order_zero (f := fun p r => K (p^r) (p^s)) hlarge hrr
      (fun _ _ hh => hphysical _ _ (Or.inl hh))
  · have hss : 2≤s := by omega
    exact higher_order_zero (f := fun p s => K (p^r) (p^s)) hlarge hss
      (fun _ _ hh => hphysical _ _ (Or.inr hh))

/-- Quantitative whole contrast budget AFTER the prime-specific support
join. It is valid for an arbitrary, not necessarily rank-one, phase matrix. -/
theorem norm_cross_le (P : Finset ℕ) (J : ℕ) (K : ℕ → ℕ → ℂ)
    {B : ℝ} (hB : 0≤B) (hP : P ⊆ Finset.Icc 1 (2^(2*J)))
    (hK : ∀ p ∈ P, ∀ r ∈ orders J, ∀ s ∈ orders J, ‖K (p^r) (p^s)‖≤B)
    (hphysical : ∀ d e, 2^(2*J)<d ∨ 2^(2*J)<e → K d e=0) :
    ‖cross P J K‖≤B*((2*J : ℕ) : ℝ)^4*(Real.log 2)^2*(2 : ℝ)^J := by
  classical
  rw [cross_eq_small P J K hphysical]
  let Q := P.filter (fun p => p≤2^J)
  have hcard : (Q.card : ℝ)≤(2 : ℝ)^J := by
    have hs : Q ⊆ Finset.Icc 1 (2^J) := by
      intro p hp
      obtain ⟨hp,hpmax⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hP hp)).1,hpmax⟩
    exact_mod_cast (by simpa using Finset.card_le_card hs : Q.card≤2^J)
  have hlog (p : ℕ) (hp : p ∈ Q) : ‖(Real.log p : ℂ)‖≤((2*J : ℕ) : ℝ)*Real.log 2 := by
    have hpP := (Finset.mem_filter.mp hp).1
    have hpmax := (Finset.mem_Icc.mp (hP hpP)).2
    have hpmin := (Finset.mem_Icc.mp (hP hpP)).1
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
    have hh := Real.log_le_log (by exact_mod_cast hpmin : (0 : ℝ)<p)
      (by exact_mod_cast hpmax : (p : ℝ)≤(2 : ℝ)^(2*J))
    simpa only [Real.log_pow] using hh
  have hcount : ((orders J).card : ℝ)=((2*J : ℕ) : ℝ) := by simp [orders]
  have hin (p : ℕ) (hp : p ∈ Q) :
      ‖∑ r ∈ orders J, ∑ s ∈ (orders J).erase r, K (p^r) (p^s)‖≤
        ((2*J : ℕ) : ℝ)^2*B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ r ∈ orders J, ((2*J : ℕ) : ℝ)*B := by
        apply Finset.sum_le_sum
        intro r hr
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ s ∈ orders J, B :=
            (Finset.sum_le_sum (fun s hs => hK p (Finset.mem_filter.mp hp).1 r hr s
              (Finset.mem_erase.mp hs).2)).trans
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
                (fun _ _ _ => hB))
          _ = _ := by simp [hcount]
      _ = _ := by simp [hcount]; ring
  unfold cross
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ Q, (((2*J : ℕ) : ℝ)*Real.log 2)^2*(((2*J : ℕ) : ℝ)^2*B) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul,norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hlog p hp) 2) (hin p hp)
        (norm_nonneg _) (by positivity)
    _ = (Q.card : ℝ)*((((2*J : ℕ) : ℝ)*Real.log 2)^2*(((2*J : ℕ) : ℝ)^2*B)) := by simp
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ)^J*((((2*J : ℕ) : ℝ)*Real.log 2)^2*(((2*J : ℕ) : ℝ)^2*B)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

/-- Every polynomial-logarithmic nonseparable coprime contrast has the
SAME power-source limit as its exact diagonal. No free PSD, PNT or
zero-mode hypothesis occurs in this actual prime-power support theorem. -/
theorem tendsto_scaled_interaction_sub_diagonal (P : ℕ → Finset ℕ)
    (K : ℕ → ℕ → ℕ → ℂ) (d : ℕ) {C beta : ℝ} (hC : 0≤C) (hbeta : 1/2<beta)
    (hprime : ∀ J p, p ∈ P J → p.Prime)
    (hP : ∀ J, P J ⊆ Finset.Icc 1 (2^(2*J)))
    (hK : ∀ J p, p ∈ P J → ∀ r ∈ orders J, ∀ s ∈ orders J,
      ‖K J (p^r) (p^s)‖≤C*((J+1 : ℕ) : ℝ)^d)
    (hcoprime : ∀ J a b, Nat.Coprime a b → K J a b=0)
    (hphysical : ∀ J a b, 2^(2*J)<a ∨ 2^(2*J)<b → K J a b=0) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      (interaction (P J) J (K J)-diagonal (P J) J (K J))) atTop (𝓝 0) := by
  let a := Real.exp (-2*beta*Real.log 2)
  let r := a*2
  have ha : 0<a := Real.exp_pos _
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by
    have he : r=Real.exp ((1-2*beta)*Real.log 2) := by
      dsimp [r,a]
      calc
        _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
        _ = _ := by rw [←Real.exp_add]; congr 1; ring
    rw [he]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith)
      (Real.log_pos (by norm_num)))
  have ht : Tendsto (fun J : ℕ =>
      (16*C*(Real.log 2)^2)*(((J+1 : ℕ) : ℝ)^(d+4)*r^J)) atTop (𝓝 0) := by
    simpa using (tendsto_shifted_polynomial_geometric (d+4) hr hr1).const_mul
      (16*C*(Real.log 2)^2)
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [interaction_eq_diagonal_add_cross (P J) J (K J) (hprime J) (hcoprime J),
    add_sub_cancel_left,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ha.le]
  calc
    _ ≤ a^J*(C*((J+1 : ℕ) : ℝ)^d*((2*J : ℕ) : ℝ)^4*(Real.log 2)^2*(2 : ℝ)^J) :=
      mul_le_mul_of_nonneg_left (norm_cross_le (P J) J (K J) (by positivity)
        (hP J) (hK J) (hphysical J)) (pow_nonneg ha.le J)
    _ ≤ a^J*(C*((J+1 : ℕ) : ℝ)^d*(2*((J+1 : ℕ) : ℝ))^4*(Real.log 2)^2*(2 : ℝ)^J) := by
      push_cast
      gcongr
      norm_cast
      omega
    _ = _ := by dsimp [r]; rw [mul_pow,pow_add]; push_cast; ring

end
end RiemannGaussian.ArithmeticOperatorPrimeGcdContrast
