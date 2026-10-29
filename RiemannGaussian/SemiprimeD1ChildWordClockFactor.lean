/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordPacketClockFactor
import RiemannGaussian.SemiprimeD1ChildWordBudgetLinear

/-! # Actual tape-child clock prefactors
Full serialization and recopy are retained, including the actual old network
inventory. Eager table scales are cubed, rather than silently treated as linear.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RiemannGaussian.SemiprimeD1ChildWordClockFactor
open SemiprimeD1JetAxes SemiprimeD1WordPacketClockFactor
open SemiprimeD1ChildTableCopyTape (tapeBudget tableCap)

/-- Polynomial coefficient for every actual old-table routing/serialization stage. -/
def leftFactor (old : Context) (extra : List ℕ) (p D O I v : ℕ) : ℕ :=
  (2*O+2*D+v+9*p+(extra++old.axes).prod+30)+
    ((tapeBudget I+7)+(D*(4*D+7)+1+SemiprimeD1ChildTableCopy.liftBudget old extra p+12))+
    tapeCoefficient (storageCoefficient old)+tapeCoefficient (storageCoefficient ⟨extra++old.axes,p⟩)

/-- Actual old-table acquisition and full recopy have the explicit cubic eager
scale, with parent inventory and all routing reports left in the coefficient. -/
theorem leftBudget_factor (old : Context) (extra : List ℕ) (p D O I v : ℕ) :
    SemiprimeD1ChildNetworkTapeBudget.leftBudget old extra p D O I v ≤
      leftFactor old extra p D O I v*2^(3*D) := by
  let q:=2^D
  let cap:=2^(3*D)
  have hq : 1 ≤ q := Nat.one_le_two_pow
  have hcap : 1 ≤ cap := Nat.one_le_two_pow
  have hqc : q ≤ cap := Nat.pow_le_pow_right (by decide) (by omega)
  have hq3 : q^3=cap := by dsimp only [q,cap];rw [←pow_mul];congr 1;omega
  have ho : tapeBudget (tableCap old D)*q ≤ tapeCoefficient (storageCoefficient old)*cap := by
    calc
      _ ≤ (tapeBudget (tableCap old D)+7)*q := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ tapeCoefficient (storageCoefficient old)*q^3 := tape_scaled _ q hq
      _ = _ := by rw [hq3]
  have hn : (tapeBudget (tableCap ⟨extra++old.axes,p⟩ D)+7)*q ≤
      tapeCoefficient (storageCoefficient ⟨extra++old.axes,p⟩)*cap := by
    simpa only [hq3,storageCoefficient,tableCap] using
      tape_scaled (storageCoefficient (⟨extra++old.axes,p⟩:Context)) q hq
  let C:=2*O+2*D+v+9*p+(extra++old.axes).prod+30
  let A:=(tapeBudget I+7)+(D*(4*D+7)+1+SemiprimeD1ChildTableCopy.liftBudget old extra p+12)
  have hc : C ≤ C*cap := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hcap
  have ha : A*q ≤ A*cap := Nat.mul_le_mul_left A hqc
  unfold SemiprimeD1ChildNetworkTapeBudget.leftBudget SemiprimeD1ChildTensorTablesTape.cacheBudget
  change _ ≤ leftFactor old extra p D O I v*cap
  calc
    _ = C+A*q+tapeBudget (tableCap old D)*q+
        (tapeBudget (tableCap ⟨extra++old.axes,p⟩ D)+7)*q := by dsimp only [C,A,q];ring
    _ ≤ C*cap+A*cap+tapeCoefficient (storageCoefficient old)*cap+
        tapeCoefficient (storageCoefficient ⟨extra++old.axes,p⟩)*cap :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc ha) ho) hn
    _ = _ := by unfold leftFactor;dsimp only [C,A];ring

/-- Fixed arithmetic coefficient of the actual whole child, after eager scales
are factored. Actual source/header/inventory reports are retained literally. -/
def prefactor (old : Context) (extra : List ℕ)
    (p a D A K P T B L E NF M I W G O H : ℕ) : ℕ :=
  W+G+10*(NF+1)+10*(NF+M+2*M^2+1)^3+
    NF*leftFactor old extra p D O I NF+
    M*rightFactor ⟨extra++old.axes,p⟩ a A K P T B L E H 0 G M

/-- Whole source-free actual child report factors through the original
catalogue inequality, with no table/coefficient/report answer supplied. -/
theorem sourceFree_factor (net : SemiprimeD1TensorNetwork.Network) (old : Context)
    (extra : List ℕ) (D a u : ℕ) (i : Fin a)
    (hcoef : 2^(2*2^a)*
      (SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision+1)^(2*2^a) ≤ 2^D) :
    let src:=SemiprimeD1ChildOriginalClock.source net old a u i
    let M:=SemiprimeD1ChildOriginalClock.ports net
    let NF:=net.leftCount+net.rows.length
    let K:=SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision
    let E:=SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M
    let H:=SemiprimeD1PacketModeMaskBudget.prepareOverhead net.leftCount net.rows.length 64 a M src.precision
    SemiprimeD1ChildWordBudgetLinear.sourceFree net old extra D a u i ≤
      prefactor old extra src.precision a D (2*2^a) K src.precision (2^a) src.precision K E NF M
        (SemiprimeD1NetworkStateResources.inventory net)
        (SemiprimeD1ChildOriginalClock.dataCap net a) (SemiprimeD1ChildOriginalClock.graphCap net a)
        (SemiprimeD1ChildOriginalClock.orderCap net a) H*2^(3*D) := by
  dsimp only
  let src:=SemiprimeD1ChildOriginalClock.source net old a u i
  let M:=SemiprimeD1ChildOriginalClock.ports net
  let NF:=net.leftCount+net.rows.length
  let K:=SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision
  let E:=SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M
  let H:=SemiprimeD1PacketModeMaskBudget.prepareOverhead net.leftCount net.rows.length 64 a M src.precision
  let cap:=2^(3*D)
  have hcap : 1 ≤ cap := Nat.one_le_two_pow
  have hl:=leftBudget_factor old extra src.precision D (SemiprimeD1ChildOriginalClock.orderCap net a)
    (SemiprimeD1NetworkStateResources.inventory net) NF
  have hr:=rightClock_factor ⟨extra++old.axes,src.precision⟩ a (2*2^a) K src.precision
    (2^a) src.precision K E H 0 (SemiprimeD1ChildOriginalClock.graphCap net a) M D hcoef
  let C:=SemiprimeD1ChildOriginalClock.dataCap net a+SemiprimeD1ChildOriginalClock.graphCap net a+
    10*(NF+1)+10*(NF+M+2*M^2+1)^3
  have hc : C ≤ C*cap := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hcap
  unfold SemiprimeD1ChildWordBudgetLinear.sourceFree
  change _ ≤ _*cap
  calc
    _ = C+NF*SemiprimeD1ChildNetworkTapeBudget.leftBudget old extra src.precision D
        (SemiprimeD1ChildOriginalClock.orderCap net a) (SemiprimeD1NetworkStateResources.inventory net) NF+
      M*SemiprimeD1WordPacketTableClock.rightClock ⟨extra++old.axes,src.precision⟩ a (2*2^a) K
        src.precision (2^a) src.precision K E H 0 (SemiprimeD1ChildOriginalClock.graphCap net a) M := by
      dsimp only [C,NF,M,src,K,E,H];ring
    _ ≤ C*cap+NF*(leftFactor old extra src.precision D (SemiprimeD1ChildOriginalClock.orderCap net a)
        (SemiprimeD1NetworkStateResources.inventory net) NF*cap)+
      M*(rightFactor ⟨extra++old.axes,src.precision⟩ a (2*2^a) K src.precision (2^a) src.precision K E H 0
        (SemiprimeD1ChildOriginalClock.graphCap net a) M*cap) :=
      Nat.add_le_add (Nat.add_le_add hc (Nat.mul_le_mul_left NF hl)) (Nat.mul_le_mul_left M hr)
    _ = _ := by unfold prefactor;dsimp only [C,NF,M,src,K,E,H];ring

end RiemannGaussian.SemiprimeD1ChildWordClockFactor
