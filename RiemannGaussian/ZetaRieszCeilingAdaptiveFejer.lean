/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingFejerCluster
import RiemannGaussian.ZetaRieszCeilingWholeHeightBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A moving-order signed estimate for the whole native ceiling

Fejér positivity is applied to the entire actual competing divisor before
using its complete height mass. The degree is allowed to grow with height;
no sparsity, phase balance or numerical zero-count hypothesis is imposed.
This is an arithmetic input for the unchanged `joinedPhysical` source.
The adaptive-degree choice and native transfer are postponed in favour of
the user-requested mask-preserving Selberg adjacent-order test. The price
remains height dependent: the constant ceiling is open.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingAdaptiveFejer
open ZetaRieszCeilingMomentIsolation ZetaRieszCeilingSignedCluster
open ZetaRieszCeilingFejerCluster

/-- The complete Fejér mass of the exact triangular order weights. -/
theorem triangular_weight_sum (d : ℕ) :
    2 * (∑ j ∈ Finset.range d, ((d : ℝ)-j)) = (d : ℝ)*(d+1) := by
  induction d with
  | zero => simp
  | succ d hd =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    have he : (∑ j ∈ Finset.range d, ((d : ℝ)+1-j)) =
        (∑ j ∈ Finset.range d, ((d : ℝ)-j))+(d : ℝ) := by
      simp_rw [show ∀ j : ℕ, (d : ℝ)+1-j = ((d : ℝ)-j)+1 by intro j; ring]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [he]
    nlinarith only [hd]

/-- The actual signed cluster satisfies the Fejér inequality at any
degree and stride. All local multiplicities remain joined. -/
theorem competing_fejer_any (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (d K : ℕ) (hK : 0 < K) :
    0 <= (d+1 : ℝ)*competingMass rho hrho+
      2*∑ j ∈ Finset.range d, ((d : ℝ)-j)*
        (competingMoment rho hrho (K*(j+1)-1)).re := by
  have ht := weighted_fejer_nonneg
    ((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im).erase
      (-((3/2-rho.1.re : ℝ) : ℂ)))
    (modeCoefficient (zetaRightHalfDiscParameter rho hrho) rho.1.im)
    (fun z => ((3/2-rho.1.re : ℝ) : ℂ)*(-z⁻¹))
    (fun z hz => coefficient_nonneg _ _ (Finset.mem_erase.mp hz).2)
    (fun _ hz => competing_node_norm_le rho hrho hexposed hz) d K
  have he (j : ℕ) : K*(j+1)-1+1 = K*(j+1) := by
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hK (Nat.zero_lt_succ j)))
  simpa only [competingMoment, he, competingMass] using ht

/-- The competing mass is bounded once, rather than once per test order. -/
theorem competingMass_le_height (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re) :
    competingMass rho hrho <= localZetaLogHeight rho.1.im+11 := by
  apply le_trans _ (local_mode_mass_height (zetaRightHalfDiscParameter rho hrho) rho.1.im)
  unfold competingMass
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
  intro z hz _
  exact coefficient_nonneg _ _ hz

private theorem geometric_prefix_le (d : ℕ) :
    (∑ j ∈ Finset.range d, (1/16 : ℝ)^j) <= 16/15 := by
  have hs := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/16 : ℝ)‖ < 1)
  have h := hs.summable.sum_le_tsum (Finset.range d) (fun _ _ => by positivity)
  rw [hs.tsum_eq] at h
  norm_num at h ⊢
  exact h

private theorem weighted_geometric_prefix_le (d : ℕ) :
    (∑ j ∈ Finset.range d, ((j : ℝ)+1)*(1/16 : ℝ)^j) <= 256/225 := by
  have ha := hasSum_coe_mul_geometric_of_norm_lt_one
    (by norm_num : ‖(1/16 : ℝ)‖ < 1)
  have hb := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/16 : ℝ)‖ < 1)
  have hs := ha.add hb
  have he : (fun j : ℕ => (j : ℝ)*(1/16)^j+(1/16)^j) =
      (fun j : ℕ => ((j : ℝ)+1)*(1/16)^j) := by funext j; ring
  rw [he] at hs
  have h := hs.summable.sum_le_tsum (Finset.range d) (fun _ _ => by positivity)
  rw [hs.tsum_eq] at h
  norm_num at h ⊢
  exact h

/-- The regular channels at stride 32 have a uniformly summable price.
The selected/competing singular channels are not included in this price. -/
theorem stride_paid_sum_le {u H H0 : ℝ} (hu : 0 <= u) (hU : u <= 10001/20000)
    (hH : 1 <= H) (hH0 : H0 <= 4) (d : ℕ) :
    (∑ j ∈ Finset.range d,
      (u^(32*(j+1))+
        160*u*(H+H0)*(32*(j+1) : ℕ)*(10*u/7)^(32*(j+1)-1)+
        (H+11)*(4*u/3)^(32*(j+1)))) <= (H+11)/8 := by
  have hup : u <= 3/5 := by linarith only [hU]
  have hq : 10*u/7 <= 18/25 := by linarith only [hU]
  have hr : 4*u/3 <= 3/4 := by linarith only [hU]
  have hQ : (10*u/7)^32 <= (1/16 : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hq 32).trans (by norm_num)
  have hR : (4*u/3)^32 <= (1/8192 : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hr 32).trans (by norm_num)
  have hP : u^32 <= (1/65536 : ℝ) :=
    (pow_le_pow_left₀ hu hup 32).trans (by norm_num)
  have hb : 160*u*32*(10*u/7)^31 <= (1/10 : ℝ) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 <= 10*u/7) hq 31
    have hmul := mul_le_mul (show 160*u*32 <= (160*(10001/20000)*32 : ℝ) by
      linarith only [hU]) hp (by positivity) (by positivity)
    exact hmul.trans (by norm_num)
  have ht (j : ℕ) :
      u^(32*(j+1))+160*u*(H+H0)*(32*(j+1) : ℕ)*(10*u/7)^(32*(j+1)-1)+
        (H+11)*(4*u/3)^(32*(j+1)) <=
      (1/65536 : ℝ)*(1/16)^j+
        ((H+11)/10)*((j : ℝ)+1)*(1/16)^j+
        ((H+11)/8192)*(1/16)^j := by
    have hjQ := pow_le_pow_left₀ (by positivity) hQ j
    have hjR := pow_le_pow_left₀ (by positivity : 0 <= (4*u/3)^32)
      (hR.trans (by norm_num : (1/8192 : ℝ) <= 1/16)) j
    have hjP := pow_le_pow_left₀ (by positivity : 0 <= u^32)
      (hP.trans (by norm_num : (1/65536 : ℝ) <= 1/16)) j
    have hpm : u^(32*(j+1)) <= (1/65536 : ℝ)*(1/16)^j := by
      rw [Nat.mul_add, pow_add, pow_mul]
      simpa only [Nat.mul_one, Nat.one_mul, mul_comm] using
        mul_le_mul hP hjP (by positivity) (by positivity)
    have hrm : (H+11)*(4*u/3)^(32*(j+1)) <= ((H+11)/8192)*(1/16)^j := by
      rw [Nat.mul_add, pow_add, pow_mul]
      have hp := mul_le_mul hR hjR (by positivity) (by positivity)
      have hh := mul_le_mul_of_nonneg_left hp (by linarith only [hH] : 0 <= H+11)
      simpa only [Nat.mul_one, Nat.one_mul, mul_one, one_mul,
        mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using hh
    have he : 32*(j+1)-1 = 31+32*j := by omega
    have hqm : 160*u*(H+H0)*(32*(j+1) : ℕ)*(10*u/7)^(32*(j+1)-1) <=
        ((H+11)/10)*((j : ℝ)+1)*(1/16)^j := by
      rw [he, pow_add, pow_mul]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      have hv := mul_le_mul hb hjQ (by positivity) (by norm_num : (0 : ℝ) <= 1/10)
      have hv1 := mul_le_mul_of_nonneg_right (show H+H0 <= H+11 by linarith only [hH0])
        (by positivity : 0 <= 160*u*32*(10*u/7)^31*((10*u/7)^32)^j*((j : ℝ)+1))
      have hv2 := mul_le_mul_of_nonneg_left hv
        (by positivity : 0 <= (H+11)*((j : ℝ)+1))
      nlinarith only [hv1, hv2]
    linarith only [hpm, hqm, hrm]
  have hs := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.range d) => ht j)
  simp_rw [Finset.sum_add_distrib, <-Finset.mul_sum] at hs
  have hg := geometric_prefix_le d
  have hw := weighted_geometric_prefix_le d
  have he : (∑ j ∈ Finset.range d, (H+11)/10*((j : ℝ)+1)*(1/16)^j) =
      (H+11)/10 * (∑ j ∈ Finset.range d, ((j : ℝ)+1)*(1/16)^j) := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [he] at hs
  have ht1 := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) <= 1/65536)
  have ht2 := mul_le_mul_of_nonneg_left hw (by positivity : 0 <= (H+11)/10)
  have ht3 := mul_le_mul_of_nonneg_left hg (by positivity : 0 <= (H+11)/8192)
  simp only [Finset.sum_add_distrib, <-Finset.mul_sum]
  nlinarith only [hs, ht1, ht2, ht3, hH]

/-- An independent arithmetic cap at any positive moving degree. There
is no competing-count, signed-balance or stronger separation assumption. -/
theorem multiplicity_le_degree_price (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re <= 10001/20000) (d : ℕ) (hd : 0 < d) :
    (analyticZetaZeroMultiplicity rho : ℝ) <=
      (2*(3/2-rho.1.re))^(32*d)+(5/4)*(localZetaLogHeight rho.1.im+11)/(d : ℝ) := by
  let u := 3/2-rho.1.re
  let H := localZetaLogHeight rho.1.im
  let H0 := localZetaLogHeight 0
  let m : ℝ := analyticZetaZeroMultiplicity rho
  let P (j : ℕ) : ℝ := u^(32*(j+1))+
    160*u*(H+H0)*(32*(j+1) : ℕ)*(10*u/7)^(32*(j+1)-1)+
    (H+11)*(4*u/3)^(32*(j+1))
  have hu : 1/2 <= u := by dsimp [u]; linarith [rho.re_lt_one]
  have hu0 : 0 <= u := by linarith only [hu]
  have hH : 1 <= H := (two_lt_localZetaLogHeight rho.1.im).le.trans' (by norm_num)
  have hH0 : H0 <= 4 := zero_height_log_le
  have hH0pos : 0 <= H0 := (two_lt_localZetaLogHeight 0).le.trans' (by norm_num)
  have hpaid : (∑ j ∈ Finset.range d, P j) <= (H+11)/8 :=
    stride_paid_sum_le hu0 hU hH hH0 d
  have hw (j : ℕ) (hj : j ∈ Finset.range d) : 0 <= (d : ℝ)-j := by
    exact sub_nonneg.mpr (by exact_mod_cast (Finset.mem_range.mp hj).le)
  have ht (j : ℕ) (hj : j ∈ Finset.range d) :
      ((d : ℝ)-j)*(m+(competingMoment rho hrho (32*(j+1)-1)).re) <=
        ((d : ℝ)-j)*((2*u)^(32*d)+P j) := by
    have he : 32*(j+1)-1+1 = 32*(j+1) := by omega
    have heR : ((32*(j+1)-1 : ℕ) : ℝ)+1 = (32*(j+1) : ℕ) := by exact_mod_cast he
    have hmain : (2*u)^(32*(j+1)) <= (2*u)^(32*d) :=
      pow_le_pow_right₀ (by linarith only [hu]) (by
        exact Nat.mul_le_mul_left 32 (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
    have hm := multiplicity_add_competing_re_le rho hrho (32*(j+1)-1)
    simp only [he, heR] at hm
    apply mul_le_mul_of_nonneg_left _ (hw j hj)
    change m+(competingMoment rho hrho (32*(j+1)-1)).re <= _
    dsimp only [P, m, u, H, H0] at hmain ⊢
    linarith only [hm, hmain]
  have htests := mul_le_mul_of_nonneg_left (Finset.sum_le_sum ht) (by norm_num : (0 : ℝ) <= 2)
  have hleft : 2*(∑ j ∈ Finset.range d,
      ((d : ℝ)-j)*(m+(competingMoment rho hrho (32*(j+1)-1)).re)) =
      (d : ℝ)*(d+1)*m+2*(∑ j ∈ Finset.range d,
        ((d : ℝ)-j)*(competingMoment rho hrho (32*(j+1)-1)).re) := by
    simp_rw [mul_add, Finset.sum_add_distrib, <-Finset.sum_mul]
    have hc := congrArg (fun v : ℝ => v*m) (triangular_weight_sum d)
    nlinarith only [hc]
  have hweight : (∑ j ∈ Finset.range d, ((d : ℝ)-j)*P j) <= (d : ℝ)*(H+11)/8 := by
    have h := Finset.sum_le_sum (s := Finset.range d) (fun j _ =>
      mul_le_mul_of_nonneg_right
        (sub_le_self (d : ℝ) (Nat.cast_nonneg j))
        (show 0 <= P j by dsimp only [P]; positivity))
    rw [<-Finset.mul_sum] at h
    exact h.trans (by
      have h := mul_le_mul_of_nonneg_left hpaid (Nat.cast_nonneg d)
      simpa only [mul_div_assoc] using h)
  have hright : 2*(∑ j ∈ Finset.range d, ((d : ℝ)-j)*((2*u)^(32*d)+P j)) <=
      (d : ℝ)*(d+1)*(2*u)^(32*d)+(d : ℝ)*(H+11)/4 := by
    simp_rw [mul_add, Finset.sum_add_distrib, <-Finset.sum_mul]
    have hc := congrArg (fun v : ℝ => v*(2*u)^(32*d)) (triangular_weight_sum d)
    nlinarith only [hc, hweight]
  rw [hleft] at htests
  have hpos := competing_fejer_any rho hrho hexposed d 32 (by norm_num)
  have hmass := competingMass_le_height rho hrho
  have hmass1 := mul_le_mul_of_nonneg_left hmass
    (by positivity : 0 <= (d+1 : ℝ))
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  have hraw : (d : ℝ)*(d+1)*m <=
      (d : ℝ)*(d+1)*(2*u)^(32*d)+(d+1)*(H+11)+(d : ℝ)*(H+11)/4 := by
    linarith only [htests, hright, hpos, hmass1]
  have hfinal : m <= (2*u)^(32*d)+(5/4)*(H+11)/(d : ℝ) := by
    apply (mul_le_mul_iff_left₀ hD).mp
    have hnon : 0 <= H+11 := by linarith only [hH]
    have he : (5/4)*(H+11)/(d : ℝ)*(d : ℝ) = (5/4)*(H+11) :=
      div_mul_cancel₀ _ hD.ne'
    rw [add_mul, he]
    nlinarith only [hraw, hnon, hD]
  exact hfinal

end RiemannGaussian.ZetaRieszCeilingAdaptiveFejer
