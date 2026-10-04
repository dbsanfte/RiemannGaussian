/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedMovingCarrierObstruction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Whole-family moment cancellation and its surviving period coefficient

All original normalized block-point moments separate into one original
seed moment and one geometric sum. This is an exact aggregate identity
over the composite ring, including zero denominators. It is not a bit
bound for acquiring the seed moments or reconstructing their carrier.

The whole family's centered moment series cannot be an endpoint shift
difference, even if the unknown endpoint series depends on the input and
the actual block count. At the original global order every point power
is one and the positive label count survives, while a shift difference
has zero coefficient. This obstructs pure endpoint telescoping without
requiring materialized carriers, a fixed linear state or a degree bound.
Short truncated moment reconstruction and compensated telescoping with
an additional period channel remain separate acquisition questions.
-/

namespace RiemannGaussian.SemiprimeSeedMomentCancellationObstruction

open scoped BigOperators
open SemiprimeSeedPointRigidity SemiprimeSeedSumAcquisition
open SemiprimeSharedIntervalJet SemiprimeDenseRowCarries
open SemiprimeGlobalPhaseCancellation SemiprimeLocalOrderRouting
open SemiprimeCentreFreeCover SemiprimeWrapIndexRecovery SemiprimeWideWrapCoverage

/-- Proof-side power sum of the complete ORIGINAL seed target family. -/
noncomputable def seedMoment {N : ℕ} (g : (ZMod N)ˣ) (m r : ℕ) : ZMod N :=
  ∑ j∈Finset.range (m-1),((progressionSeed g N m (j+1)).step : ZMod N)^r

/-- Proof-side power sum of every original seed and every supplied block.
Labels are retained with multiplicity; no point-stream algorithm is defined. -/
noncomputable def gridMoment {N : ℕ} (g : (ZMod N)ˣ) (m w J r : ℕ) : ZMod N :=
  ∑ j∈Finset.range (m-1),∑ k∈Finset.range J,(seedPoint g m w (j+1) k)^r

/-- Each actual normalized point has the common geometric block scale. -/
theorem seedPoint_geometric {N : ℕ} (g : (ZMod N)ˣ) (m w j k : ℕ) :
    seedPoint g m w j k=
      ((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ) : ZMod N)^k*
        ((progressionSeed g N m j).step : ZMod N) := by
  unfold seedPoint normalizedPoint
  simp only [←Units.val_pow_eq_pow_val,inv_pow,pow_mul,Nat.mul_comm]

/-- Whole-family moment extraction factors into a seed power sum and
a geometric sum. Repeated points contribute their original label weight. -/
theorem gridMoment_separable {N : ℕ} (g : (ZMod N)ˣ) (m w J r : ℕ) :
    gridMoment g m w J r=seedMoment g m r*
      ∑ k∈Finset.range J,
        (((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ) : ZMod N)^r)^k := by
  unfold gridMoment seedMoment
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [seedPoint_geometric,mul_pow,pow_right_comm,mul_comm]

/-- The cancellation identity is division-free. At a zero geometric
denominator it does not determine the actual surviving moment. -/
theorem gridMoment_geometric_difference {N : ℕ} (g : (ZMod N)ˣ) (m w J r : ℕ) :
    (((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ) : ZMod N)^r-1)*gridMoment g m w J r=
      seedMoment g m r*
        ((((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ) : ZMod N)^r)^J-1) := by
  rw [gridMoment_separable,mul_left_comm,mul_geom_sum]

/-- Every original target is a power of the original unit, so its power
at the global period is one. The period is proof-side, never input advice. -/
theorem original_seed_period {N m j : ℕ} (g : (ZMod N)ˣ)
    (hm : 0<m) (hj : j.Coprime m) :
    (((progressionSeed g N m j).step : ZMod N)^orderOf g)=1 := by
  rw [seed_step_offset g hm hj,←Units.val_pow_eq_pow_val,zpow_pow_orderOf]
  rfl

/-- The geometric block scale has the same proof-side period, for ANY
width; order preservation or a denominator inversion is unnecessary. -/
theorem block_scale_period {N : ℕ} (g : (ZMod N)ˣ) (m w : ℕ) :
    (((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ) : ZMod N)^orderOf g)=1 := by
  rw [←Units.val_pow_eq_pow_val,inv_pow]
  change (((((g^(m^2))^w)^orderOf g)⁻¹ : (ZMod N)ˣ) : ZMod N)=1
  rw [pow_right_comm (g^(m^2)) w (orderOf g),
    pow_right_comm g (m^2) (orderOf g),pow_orderOf_eq_one,one_pow,one_pow,inv_one]
  rfl

/-- All original seed contributions ADD at the period: their combined
moment is m-1, even over the original composite ring. -/
theorem seedMoment_period {N m : ℕ} (g : (ZMod N)ˣ) (hm : 0<m) (hmprime : m.Prime) :
    seedMoment g m (orderOf g)=((m-1 : ℕ) : ZMod N) := by
  unfold seedMoment
  have hterms : ∀ j∈Finset.range (m-1),
      (((progressionSeed g N m (j+1)).step : ZMod N)^orderOf g)=1 := by
    intro j hj
    have hlt := Finset.mem_range.mp hj
    exact original_seed_period g hm
      ((hmprime.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm)
  rw [Finset.sum_congr rfl hterms]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]

/-- At the period the entire rectangular original point family has
its full raw label mass, including every geometric block and duplicate. -/
theorem gridMoment_period {N m : ℕ} (g : (ZMod N)ˣ) (hm : 0<m) (hmprime : m.Prime)
    (w J : ℕ) :
    gridMoment g m w J (orderOf g)=(((m-1)*J : ℕ) : ZMod N) := by
  rw [gridMoment_separable,seedMoment_period g hm hmprime,block_scale_period]
  simp only [one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Nat.cast_mul]

/-- Centering removes the trivial constant moment before telescoping
is tested; the obstruction below occurs at a POSITIVE period coefficient. -/
noncomputable def centredSeedSeries {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    PowerSeries (ZMod N) := PowerSeries.mk fun r => if r=0 then 0 else seedMoment g m r

/-- The centered whole-family block series, retaining every positive
moment of the original labeled point family. -/
noncomputable def centredGridSeries {N : ℕ} (g : (ZMod N)ˣ) (m w J : ℕ) :
    PowerSeries (ZMod N) := PowerSeries.mk fun r => if r=0 then 0 else gridMoment g m w J r

/-- Exact coefficients of the centered original seed moment series. -/
theorem centredSeedSeries_coeff {N : ℕ} (g : (ZMod N)ˣ) (m r : ℕ) (hr : 0<r) :
    PowerSeries.coeff r (centredSeedSeries g m)=seedMoment g m r := by
  simp only [centredSeedSeries,PowerSeries.coeff_mk,if_neg (Nat.ne_of_gt hr)]

/-- Exact coefficients of the centered whole-family block series. -/
theorem centredGridSeries_coeff {N : ℕ} (g : (ZMod N)ˣ) (m w J r : ℕ) (hr : 0<r) :
    PowerSeries.coeff r (centredGridSeries g m w J)=gridMoment g m w J r := by
  simp only [centredGridSeries,PowerSeries.coeff_mk,if_neg (Nat.ne_of_gt hr)]

/-- The entire finite block family is the sum of geometric shifts of
the original seed series. This is the exact input to the proposed
endpoint cancellation, rather than an unrelated formal-series model. -/
theorem centredGridSeries_shifts {N : ℕ} (g : (ZMod N)ˣ) (m w J : ℕ) :
    centredGridSeries g m w J=
      ∑ k∈Finset.range J,PowerSeries.rescale
        (((((seedBase g m)^w)⁻¹ : (ZMod N)ˣ) : ZMod N)^k) (centredSeedSeries g m) := by
  classical
  ext r
  simp only [map_sum,PowerSeries.coeff_rescale,centredGridSeries,
    centredSeedSeries,PowerSeries.coeff_mk]
  by_cases hr : r=0
  · simp [hr]
  · simp only [if_neg hr]
    rw [gridMoment_separable,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_right_comm,mul_comm]

/-- A geometric endpoint difference always loses the period coefficient,
regardless of how its endpoint series is represented or acquired. -/
theorem rescale_difference_period_coeff {R : Type*} [CommRing R]
    (F : PowerSeries R) (c : R) (D : ℕ) (hc : c^D=1) :
    PowerSeries.coeff D (PowerSeries.rescale c F-F)=0 := by
  rw [map_sub,PowerSeries.coeff_rescale,hc,one_mul,sub_self]

/-- A surviving period coefficient excludes EVERY formal endpoint
series, with no degree, fixed-state, recurrence or materialization premise. -/
theorem no_series_endpoint_difference {R : Type*} [CommRing R]
    (H : PowerSeries R) (c : R) (D : ℕ) (hc : c^D=1)
    (hH : PowerSeries.coeff D H≠0) :
    ¬∃ F : PowerSeries R,PowerSeries.rescale c F-F=H := by
  rintro ⟨F,hF⟩
  have he := rescale_difference_period_coeff F c D hc
  rw [hF] at he
  exact hH he

/-- Every compensated endpoint formula must keep the full period mass
in its extra channel. Calling that channel zero would erase actual data. -/
theorem compensated_difference_period_coeff {R : Type*} [CommRing R]
    (F B H : PowerSeries R) (c : R) (D : ℕ) (hc : c^D=1)
    (he : PowerSeries.rescale c F-F+B=H) :
    PowerSeries.coeff D B=PowerSeries.coeff D H := by
  have hcoeff := congrArg (PowerSeries.coeff D) he
  rw [map_add,rescale_difference_period_coeff F c D hc,zero_add] at hcoeff
  exact hcoeff

/-- Linear factory width 4m and this actual block count cover the FULL
original padded interval. Their raw label mass lies strictly below m^2,
so it cannot vanish modulo an input above the public quadratic prefix. -/
theorem linear_moment_grid_count {m : ℕ} (hm : 4≤m) :
    let J := seedLength m/(4*m)+1
    0<J ∧ seedLength m<(4*m)*J ∧ (m-1)*J<m^2 := by
  let J := seedLength m/(4*m)+1
  have hw : 0<4*m := by omega
  have hrem := Nat.mod_lt (seedLength m) hw
  have hdiv := Nat.mod_add_div (seedLength m) (4*m)
  have hL := (seedLength_bounds hm).2
  have hle := Nat.div_le_div_right (c:=4*m) hL
  have htop : 4*m^2=m*(4*m) := by ring
  rw [htop,Nat.mul_div_cancel m hw] at hle
  have hJ : J≤m+1 := by dsimp only [J]; omega
  have hcount := Nat.mul_le_mul_left (m-1) hJ
  have hm1 : m-1+1=m := by omega
  change 0<J ∧ seedLength m<(4*m)*J ∧ (m-1)*J<m^2
  refine ⟨Nat.zero_lt_succ _,?_,?_⟩
  · dsimp only [J]
    nlinarith only [hrem,hdiv]
  · nlinarith only [hcount,hm1,hm]

/-- The actual whole-family finite block series admits no pure endpoint
formula at ANY width and actual block count whose positive raw label mass
is below N. The endpoint series may depend on that particular count.
No source pricing or endpoint-series degree restriction is assumed. -/
theorem original_grid_endpoint_obstruction {p q m w J : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hmass : 0<(m-1)*J) (hmasslt : (m-1)*J<p*q)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let h := projectedUnit g m
    let c := (((seedBase h m)^w)⁻¹ : (ZMod (p*q))ˣ)
    16*m^4<orderOf h ∧
      ¬∃ F : PowerSeries (ZMod (p*q)),
        PowerSeries.rescale ((c : ZMod (p*q))^J) F-F=centredGridSeries h m w J := by
  let : NeZero (p*q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp.pos hq.pos)⟩
  let h := projectedUnit g m
  let c := (((seedBase h m)^w)⁻¹ : (ZMod (p*q))ˣ)
  have hperiod := long_global_order_bound hp hq hpq g hlong
  have hD : 0<orderOf h := Nat.zero_le _ |>.trans_lt hperiod
  have hnonzero : (((m-1)*J : ℕ) : ZMod (p*q))≠0 := by
    intro he
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hmasslt,ZMod.val_zero] at hv
    omega
  refine ⟨hperiod,?_⟩
  apply no_series_endpoint_difference _ _ (orderOf h)
  · rw [pow_right_comm,block_scale_period,one_pow]
  · rw [centredGridSeries_coeff h m w J _ hD,gridMoment_period h (by omega) hmprime]
    exact hnonzero

/-- The obstruction includes a linear-width acquisition proposal covering
the FULL original padded interval. The positive period mass is below N
by the public quadratic-prefix size, even without prefix-none advice. -/
theorem original_linear_grid_endpoint_obstruction {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hsize : m^2<p*q) (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    let h := projectedUnit g m
    let J := seedLength m/(4*m)+1
    let c := (((seedBase h m)^(4*m))⁻¹ : (ZMod (p*q))ˣ)
    16*m^4<orderOf h ∧
      ¬∃ F : PowerSeries (ZMod (p*q)),
        PowerSeries.rescale ((c : ZMod (p*q))^J) F-F=centredGridSeries h m (4*m) J := by
  have hgrid := linear_moment_grid_count hm
  exact original_grid_endpoint_obstruction hp hq hpq hm hmprime
    (Nat.mul_pos (by omega) hgrid.1) (hgrid.2.2.trans hsize) g hlong

/-- The pure endpoint obstruction attaches to the ACTUAL N-only public
long route without a new prefix-none premise or private order advice. -/
theorem actual_public_route_moment_endpoint_obstruction {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      let J := seedLength m/(4*m)+1
      let c := (((seedBase h m)^(4*m))⁻¹ : (ZMod (p*q))ˣ)
      16*m^4<orderOf h ∧
        ¬∃ F : PowerSeries (ZMod (p*q)),
          PowerSeries.rescale ((c : ZMod (p*q))^J) F-F=centredGridSeries h m (4*m) J := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  have hN := Nat.mul_pos hp.pos hq.pos
  have hmBounds := SemiprimeEuclidRowBudget.publicRowModulus_bounds hN
  have hm : 4≤SemiprimeEuclidRowBudget.publicRowModulus (p*q) := hB.trans hmBounds.1
  exact ⟨hc,original_linear_grid_endpoint_obstruction hp hq hpq.ne hm
    (SemiprimeEuclidRowBudget.publicRowModulus_prime (p*q))
    (public_modulus_prefix_below_input hN hB) (ZMod.unitOfCoprime a hc) hlong⟩

end RiemannGaussian.SemiprimeSeedMomentCancellationObstruction
