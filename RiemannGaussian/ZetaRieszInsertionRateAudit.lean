/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszInsertionCapacity
import RiemannGaussian.ZetaRieszOwnerCountEnergy

/-!
# Rate obstruction for independent ordinary-prime insertion weights

The complete signed finite insertion response retains an empty-channel mass.
Even the full pool of genuine primes through exponential physical length
cannot make that mass geometrically small: an elementary reciprocal-prime
bound gives a polynomial lower bound in the factorial order. Consequently
the corresponding source-normalized coefficient residual regrows for every
fixed `u > 1/2`.

This is a no-go for independent weights `1/p`, not a lower bound for the
literal masked carrier. Correlated inventory, allocation, funding and phases
are not replaced by independent weights, and the native floor remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszInsertionRateAudit
open ZetaRieszInsertionCapacity ZetaRieszOwnerCountEnergy

/-- A reciprocal prime cannot remove more than twice its reciprocal mass
from the logarithm of the empty insertion channel. -/
theorem log_one_sub_inv_lower {x : ℝ} (hx : 2 ≤ x) :
    -2*x⁻¹ ≤ log (1-x⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x-1 := by linarith
  have ht : 0 < 1-x⁻¹ := by
    have hi := (inv_lt_one₀ hx0).mpr (show 1 < x by linarith)
    linarith
  have he : 1-(1-x⁻¹)⁻¹ = -(x-1)⁻¹ := by
    field_simp
    ring
  have hi : (x-1)⁻¹ ≤ 2*x⁻¹ := by
    simpa only [one_div,div_eq_mul_inv,one_mul] using
      (div_le_div_iff₀ hm hx0).mpr (show (1 : ℝ)*x ≤ 2*(x-1) by linarith)
  have hl := one_sub_inv_le_log_of_pos ht
  rw [he] at hl
  linarith only [hi,hl]

/-- The exact full empty-channel product, without a prime-count ceiling. -/
theorem prime_empty_mass_lower (Q : Finset ℕ) (hQ : ∀ p∈Q,p.Prime) :
    exp (-2*(∑ p∈Q,(p : ℝ)⁻¹)) ≤ ∏ p∈Q,(1-(p : ℝ)⁻¹) := by
  have hpos p (hp : p∈Q) : 0 < 1-(p : ℝ)⁻¹ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
    exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr hp1)
  have hsum := Finset.sum_le_sum (s := Q) (fun p hp =>
    log_one_sub_inv_lower (show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast (hQ p hp).two_le))
  calc
    _ = exp (∑ p∈Q,-2*(p : ℝ)⁻¹) := by rw [← Finset.mul_sum]
    _ ≤ exp (∑ p∈Q,log (1-(p : ℝ)⁻¹)) := exp_le_exp.mpr hsum
    _ = _ := by
      rw [← log_prod (fun p hp => (hpos p hp).ne'),
        exp_log (Finset.prod_pos hpos)]

/-- A deliberately coarse elementary constant; no PNT or density model. -/
theorem primeHarmonic_le_eight (X : ℕ) :
    primeHarmonic X ≤ 8*(1+log (4*log X+8)) := by
  have he : exp (1/2 : ℝ) ≤ 2 := by
    calc
      _ ≤ exp (log 2) := exp_le_exp.mpr (by linarith [log_two_gt_d9])
      _ = _ := exp_log (by norm_num)
  have hl : log (4 : ℝ) ≤ 2 := by
    have h : log (4 : ℝ)=2*log 2 := by
      simpa only [show (2 : ℝ)^2=4 by norm_num,Nat.cast_ofNat] using log_pow (2 : ℝ) 2
    rw [h]
    linarith [log_two_lt_d9]
  have hc : 2*exp (1/2 : ℝ)*log 4 ≤ 8 := by
    nlinarith [exp_nonneg (1/2 : ℝ),log_nonneg (by norm_num : (1 : ℝ)≤4)]
  have ht : 0 ≤ 1+log (4*log X+8) := by
    have h := log_nonneg (show (1 : ℝ) ≤ 4*log X+8 by
      linarith [log_natCast_nonneg X])
    linarith
  exact (primeHarmonic_le_loglog X).trans (mul_le_mul_of_nonneg_right hc ht)

/-- ANY genuine-prime subpool has at least this empty mass, even when
all prime counts and all possible insertion subsets are retained. -/
theorem prime_pool_empty_mass_lower (Q : Finset ℕ) (X : ℕ)
    (hQ : ∀ p∈Q,p.Prime ∧ p≤X) :
    exp (-16*(1+log (4*log X+8))) ≤ ∏ p∈Q,(1-(p : ℝ)⁻¹) := by
  have hsub : Q ⊆ (Finset.Icc 1 X).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(hQ p hp).1.pos,(hQ p hp).2⟩,(hQ p hp).1⟩
  have hs : (∑ p∈Q,(p : ℝ)⁻¹) ≤ primeHarmonic X := by
    simpa only [primeHarmonic,one_div] using
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  exact (exp_le_exp.mpr (by linarith [primeHarmonic_le_eight X,hs])).trans
    (prime_empty_mass_lower Q (fun p hp => (hQ p hp).1))

/-- Exponential prime length still leaves polynomial empty mass in the
factorial order. The pool may vary arbitrarily and include every prime. -/
theorem prime_pool_empty_mass_order_lower (Q : Finset ℕ) (X N : ℕ)
    (hQ : ∀ p∈Q,p.Prime ∧ p≤X) (hX : log X ≤ 2*(N : ℝ)+2) :
    exp (-16)/(8*((N : ℝ)+2))^16 ≤ ∏ p∈Q,(1-(p : ℝ)⁻¹) := by
  have hp : 0 < 4*log X+8 := by linarith [log_natCast_nonneg X]
  have hlarge : 0 < 8*((N : ℝ)+2) := by positivity
  have hl : log (4*log X+8) ≤ log (8*((N : ℝ)+2)) :=
    log_le_log hp (by linarith only [hX])
  have he : exp (16*log (8*((N : ℝ)+2)))=(8*((N : ℝ)+2))^16 := by
    simpa only [Nat.cast_ofNat,exp_log hlarge] using
      exp_nat_mul (log (8*((N : ℝ)+2))) 16
  calc
    _ = exp (-16*(1+log (8*((N : ℝ)+2)))) := by
      rw [show -16*(1+log (8*((N : ℝ)+2)))=
        -16-16*log (8*((N : ℝ)+2)) by ring,exp_sub,he]
    _ ≤ exp (-16*(1+log (4*log X+8))) := exp_le_exp.mpr (by linarith only [hl])
    _ ≤ _ := prime_pool_empty_mass_lower Q X hQ

/-- Sum every actual-prime insertion count FIRST. Even their complete
joined coefficient residual cannot have a geometric saving. The positive
hinge scale may move arbitrarily with the order. -/
theorem response_order_lower (Q : Finset ℕ) (X N : ℕ)
    (hQ : ∀ p∈Q,p.Prime ∧ p≤X) (hX : log X ≤ 2*(N : ℝ)+2)
    {d : ℝ} (hd : 0 < d) :
    exp (-16)/(8*((N : ℝ)+2))^16 ≤
      response Q (fun p => (p : ℝ)⁻¹) (fun p => log p) d/d := by
  apply (le_div_iff₀ hd).mpr
  have ha p (hp : p∈Q) : 0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).1.one_lt.le
    exact ⟨inv_nonneg.mpr (by linarith),(inv_le_one₀ (by linarith)).mpr hp1⟩
  exact (mul_le_mul_of_nonneg_right (prime_pool_empty_mass_order_lower Q X N hQ hX)
    hd.le).trans (by simpa only [max_eq_right hd.le] using response_ge_empty Q _ _ d ha)

/-- Even additional fixed polynomial savings do not change the rate verdict. -/
theorem empty_lower_source_div_pow_tendsto {u : ℝ} (hu : 1/2 < u) (v : ℕ) :
    Tendsto (fun N : ℕ =>
      exp (-16)/(8*((N : ℝ)+2))^16*(2*u)^N/((N : ℝ)+2)^v) atTop atTop := by
  have hr : 1 < 2*u := by linarith
  have hr0 : 0 < 2*u := by linarith
  have hshift := (tendsto_pow_const_div_const_pow_of_one_lt (16+v) hr).comp
    (tendsto_add_atTop_nat 2)
  have hsmall : Tendsto (fun N : ℕ => ((N : ℝ)+2)^(16+v)/(2*u)^N)
      atTop (nhds 0) := by
    convert hshift.const_mul ((2*u)^2) using 1
    · ext N
      simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,pow_add]
      field_simp
    · simp
  have hpos : ∀ᶠ N : ℕ in atTop,0 < ((N : ℝ)+2)^(16+v)/(2*u)^N :=
    Eventually.of_forall (fun N => div_pos (by positivity) (pow_pos hr0 N))
  have hinv := (tendsto_nhdsWithin_iff.mpr ⟨hsmall,hpos⟩).inv_tendsto_nhdsGT_zero
  have hc := hinv.const_mul_atTop (show 0 < exp (-16)/(8 : ℝ)^16 by positivity)
  convert hc using 1
  ext N
  simp only [Pi.inv_apply,mul_pow,inv_div,pow_add]
  field_simp

/-- The proved polynomial lower bound itself regrows at source scale. -/
theorem empty_lower_source_tendsto {u : ℝ} (hu : 1/2 < u) :
    Tendsto (fun N : ℕ =>
      exp (-16)/(8*((N : ℝ)+2))^16*(2*u)^N) atTop atTop := by
  simpa only [pow_zero,div_one] using empty_lower_source_div_pow_tendsto hu 0

/-- Even the entire growing actual-prime pool with every insertion count
retained cannot pay an exponentially growing source envelope in this
independent coefficient model. No literal-carrier sign is inferred. -/
theorem response_source_tendsto {u : ℝ} (hu : 1/2 < u)
    (Q : ℕ → Finset ℕ) (X : ℕ → ℕ) (d : ℕ → ℝ)
    (hQ : ∀ N,∀ p∈Q N,p.Prime ∧ p≤X N)
    (hX : ∀ N,log (X N) ≤ 2*(N : ℝ)+2) (hd : ∀ N,0 < d N) :
    Tendsto (fun N : ℕ => (2*u)^N*
      (response (Q N) (fun p => (p : ℝ)⁻¹) (fun p => log p) (d N)/d N))
      atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (empty_lower_source_tendsto hu)
  filter_upwards [] with N
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (response_order_lower (Q N) (X N) N (hQ N) (hX N) (hd N))
    (show 0 ≤ (2*u)^N by positivity)

/-- Summing all insertion counts cannot supply a sufficient rate in this
independent model even after ANY fixed polynomial source discount. -/
theorem response_source_div_pow_tendsto {u : ℝ} (hu : 1/2 < u)
    (Q : ℕ → Finset ℕ) (X : ℕ → ℕ) (d : ℕ → ℝ) (v : ℕ)
    (hQ : ∀ N,∀ p∈Q N,p.Prime ∧ p≤X N)
    (hX : ∀ N,log (X N) ≤ 2*(N : ℝ)+2) (hd : ∀ N,0 < d N) :
    Tendsto (fun N : ℕ => (2*u)^N*
      (response (Q N) (fun p => (p : ℝ)⁻¹) (fun p => log p) (d N)/d N)/
        ((N : ℝ)+2)^v) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (empty_lower_source_div_pow_tendsto hu v)
  filter_upwards [] with N
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (response_order_lower (Q N) (X N) N (hQ N) (hX N) (hd N))
    (show 0 ≤ (2*u)^N by positivity)

/-- The rate failure also rules out a bounded COFINAL subsequence in this
independent coefficient model, not just a limit along every order. -/
theorem not_frequently_response_source_div_pow_le {u : ℝ} (hu : 1/2 < u)
    (Q : ℕ → Finset ℕ) (X : ℕ → ℕ) (d : ℕ → ℝ) (v : ℕ)
    (hQ : ∀ N,∀ p∈Q N,p.Prime ∧ p≤X N)
    (hX : ∀ N,log (X N) ≤ 2*(N : ℝ)+2) (hd : ∀ N,0 < d N) (B : ℝ) :
    ¬∃ᶠ N : ℕ in atTop,(2*u)^N*
      (response (Q N) (fun p => (p : ℝ)⁻¹) (fun p => log p) (d N)/d N)/
        ((N : ℝ)+2)^v ≤ B := by
  intro h
  have ht := response_source_div_pow_tendsto hu Q X d v hQ hX hd
  obtain ⟨N,hle,hgt⟩ := (h.and_eventually (ht.eventually_gt_atTop B)).exists
  exact (not_lt_of_ge hle) hgt

/-- The same polynomial residual is present in the exact arithmetic
cofactor family. Every subset must be squarefree and old base primes must
lie beyond the hinge; literal carrier masks are not completed here. -/
theorem arithmetic_response_order_lower (Q : Finset ℕ) (X N b : ℕ)
    (hQ : ∀ p∈Q,p.Prime ∧ p≤X) (hX : log X ≤ 2*(N : ℝ)+2)
    {d : ℝ} (hd : 0 < d)
    (hfull : ∀ U∈Q.powerset,Squarefree (b*∏ p∈U,p))
    (hlarge : ∀ p∈b.primeFactors,d ≤ log p) :
    exp (-16)/(8*((N : ℝ)+2))^16 ≤
      (∑ U∈Q.powerset,(-1 : ℝ)^U.card*(∏ p∈U,(p : ℝ)⁻¹)*
        VaughanLogAverage.riesz d (b*∏ p∈U,p))/d := by
  rw [arithmetic_response_eq Q _ (fun p hp => (hQ p hp).1) b d hfull hlarge]
  exact response_order_lower Q X N hQ hX hd

end RiemannGaussian.ZetaRieszInsertionRateAudit
