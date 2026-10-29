import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutIndexed
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumeratorBridge

namespace OAI.Algorithms

/-! The actual universal incidence-copy block over a commutative coefficient
ring in which the power-of-two denominator is a unit. -/

namespace SubexponentialSAT.SqrtLog.LayoutUniversal

open scoped BigOperators
open Matrix
open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ} {O : Type*} [CommRing O]

abbrev U (r Q : ℕ) := UniversalType r Q 1
abbrev Head (t : Fin Q) (g : Fin r) := {u : U r Q // u.head t = g}

def jointOwner (t : Fin Q) (g : Fin r) : Joint t g (0 : Fin 1) → Head t g :=
  fun j => ⟨j.val, j.property.1⟩

def headOwner (t : Fin Q) (g : Fin r) : Head t g → U r Q := Subtype.val

theorem headOwner_injective (t : Fin Q) (g : Fin r) :
    Function.Injective (headOwner t g) := Subtype.val_injective

noncomputable def constraints (A R : ℕ) (t : Fin Q) (g : Fin r) :
    Joint t g (0 : Fin 1) → Head t g → ℤ :=
  pulledConstraints (jointOwner t g)
    (clearedDefect (LayoutNumerator.denominator R)
      (LayoutNumerator.joint (0 : Fin 1) t g A R))

theorem locality {node : Fin Q → O} (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (a : U r Q) (t : Fin Q) (g : Fin r) (hg : g ≠ a.slot 0 t) :
    KillsIntegerKernel
      (fun y : Head t g =>
        (sourceRow (LayoutNumerator.family r Q 1 A R) denom a 0 R units y.val).eval
          (node t)) (constraints A R t g) := by
  classical
  intro z hz
  let zfull : U r Q → ℤ := row (headOwner t g) z
  have hzhead : ∀ y, y.head t ≠ g → zfull y = 0 := by
    intro y hy
    apply LayoutPullback.row_eq_zero
    rintro ⟨v, hv⟩
    exact hy (hv ▸ v.property)
  have hzjoint (y : Joint t g (0 : Fin 1)) : zfull y.val = z (jointOwner t g y) :=
    row_apply_injective (headOwner t g) (headOwner_injective t g) z
      (jointOwner t g y)
  have hc : clearedDefect (LayoutNumerator.denominator R)
      (LayoutNumerator.joint (0 : Fin 1) t g A R) *ᵥ
      (fun y : Joint t g (0 : Fin 1) => zfull y.val) = 0 := by
    funext j
    have hj := hz j
    change signature
      (pulledConstraints (jointOwner t g)
        (fun j i => clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R) j i)) z j = 0 at hj
    rw [signature_pullback] at hj
    simpa only [signature, duplicate, Function.comp_def, Matrix.mulVec,
      dotProduct, hzjoint, Pi.zero_apply] using hj
  have h := LayoutNumerator.family_sourceRow_annihilates A R denom hdenom a 0
    units t g hg zfull hzhead hc
  change (∑ y : Head t g,
    (sourceRow (LayoutNumerator.family r Q 1 A R) denom a 0 R units y.val).eval
      (node t) * (z y : O)) = 0
  have hcast (y : U r Q) : (zfull y : O) =
      row (headOwner t g) (fun v => (z v : O)) y :=
    row_map (Int.castRingHom O) (headOwner t g) z y
  simp_rw [hcast] at h
  rw [row_right_dot] at h
  exact h

/-- Every row, constraint, origin and degree in this block is the concrete
universal swap construction; no abstract locality hypothesis is an input. -/
noncomputable def data {node : Fin Q → O} (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) :
    Layout.Data (O := O) (G := Fin r) (id : U r Q → U r Q)
      (id : U r Q → U r Q) Q R :=
  Layout.ofIndexed node units (fun t u => u.head t) (fun u => u.slot 0)
    (fun a => sourceRow (LayoutNumerator.family r Q 1 A R) denom a 0 R units)
    (by
      intro a y
      have h := congrFun (sourceRow_origin (LayoutNumerator.family r Q 1 A R)
        denom a 0 R units) y
      simpa [Pi.single_apply, eq_comm] using h)
    (fun a y => sourceRow_degree (LayoutNumerator.family r Q 1 A R)
      denom a 0 R units y)
    (fun t g => Joint t g (0 : Fin 1)) (constraints A R)
    (fun t a g hg => locality A R denom hdenom units a t g hg)

end SubexponentialSAT.SqrtLog.LayoutUniversal

end OAI.Algorithms
