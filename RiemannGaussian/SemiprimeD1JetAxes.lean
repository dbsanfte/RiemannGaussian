/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCompactBits

/-! # Executed creation-tagged dense jet vectors
New axes are outermost, so every old coordinate stays in the initial block.
Canonical precision increase copies the SAME bits; it is not a ring map.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetAxes
open SemiprimeBitArithmetic

/-- Finite nilpotent-axis dimensions and current coordinate residue precision. -/
structure Context where
  /-- Outermost axis first. Each operational axis is required positive. -/
  axes : List ℕ
  /-- Coordinate modulus is2^precision. -/
  precision : ℕ
  deriving DecidableEq, Repr

/-- Actual dense coefficient count; the scalar/no-axis ring has rank one. -/
def Context.rank (ctx : Context) : ℕ := ctx.axes.prod

/-- Positive axes are the only required shape admissibility condition. -/
def Context.Positive (ctx : Context) : Prop := ∀ q∈ctx.axes,0<q

/-- Immutable creation tags survive every later axis or precision embedding. -/
structure Tagged where
  /-- The axes and precision at the tensor's creation, never rewritten. -/
  creation : Context
  /-- Target context in which this copied view is currently used. -/
  current : Context
  /-- Physical unsigned coordinate words in dense outermost-axis order. -/
  coefficients : List (List Bool)
  deriving Repr

/-- Literal acquired vector and retained primitive-bit/list-cell report. -/
structure Run where
  /-- Actual creation-tagged output. -/
  value : Tagged
  /-- Copies, zero allocations and finite scalar/list control. -/
  clock : ℕ

/-- Actual bit-copy reports cached once per coordinate. -/
def copyVector : List (List Bool) → List (List Bool) × ℕ
  | [] => ([],1)
  | w::ws =>
    let head := SemiprimeSourceCompactBits.copy w
    let tail := copyVector ws
    (head.bits::tail.1,head.clock+tail.2+3)

/-- Every physical source bit remains unchanged. -/
theorem copyVector_value (ws : List (List Bool)) : (copyVector ws).1=ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [copyVector,SemiprimeSourceCompactBits.copy_bits,ih]

/-- All bit and cell copies are paid, without closure memoization. -/
theorem copyVector_clock (ws : List (List Bool)) :
    (copyVector ws).2=3*(ws.map List.length).sum+4*ws.length+1 := by
  induction ws with
  | nil => simp [copyVector]
  | cons w ws ih => simp only [copyVector,SemiprimeSourceCompactBits.copy_clock,
      List.map_cons,List.sum_cons,List.length_cons,ih];omega

/-- Uniform input word widths bound all actual copy calls and list cells. -/
theorem copyVector_clock_le (ws : List (List Bool)) (W : ℕ)
    (hw : ∀w∈ws,w.length≤W) :
    (copyVector ws).2≤ws.length*(3*W+4)+1 := by
  induction ws with
  | nil => simp [copyVector]
  | cons w ws ih =>
    have hh:=hw w List.mem_cons_self
    have ht:=ih (fun v hv => hw v (List.mem_cons_of_mem w hv))
    simp only [copyVector,SemiprimeSourceCompactBits.copy_clock,List.length_cons]
    nlinarith

/-- Initial immutable creation tag is installed on actual copied payload data. -/
def acquire (ctx : Context) (ws : List (List Bool)) : Run :=
  let out := copyVector ws
  ⟨⟨ctx,ctx,out.1⟩,out.2+ctx.axes.length+3⟩

/-- The acquired coefficient payload is the supplied physical vector, not an answer oracle. -/
theorem acquire_coefficients (ctx : Context) (ws : List (List Bool)) :
    (acquire ctx ws).value.coefficients=ws := copyVector_value ws

/-- Actual extension copies all old words and appends freshly allocated zero cells.
Native rank products and list metadata remain explicit scalar/control operations. -/
def embed (entry : Tagged) (extra : List ℕ) (p : ℕ) : Run :=
  let old := copyVector entry.coefficients
  let zeros := List.replicate (entry.current.rank*(extra.prod-1)) ([] : List Bool)
  ⟨⟨entry.creation,⟨extra++entry.current.axes,p⟩,old.1++zeros⟩,
    old.2+zeros.length+old.1.length+extra.length+entry.current.axes.length+7⟩

/-- Same physical creator precision and axis signature are retained. -/
theorem embed_creation (entry : Tagged) (extra : List ℕ) (p : ℕ) :
    (embed entry extra p).value.creation=entry.creation := rfl

/-- Every old nilpotent coordinate survives, not merely its constant term. -/
theorem embed_coefficients (entry : Tagged) (extra : List ℕ) (p : ℕ) :
    (embed entry extra p).value.coefficients=entry.coefficients++
      List.replicate (entry.current.rank*(extra.prod-1)) [] := by
  simp only [embed,copyVector_value]

/-- New outer axes multiply the actual dense rank. -/
theorem embed_rank (entry : Tagged) (extra : List ℕ) (p : ℕ) :
    (embed entry extra p).value.current.rank=extra.prod*entry.current.rank := by
  simp only [embed,Context.rank,List.prod_append]

/-- All original coefficients can be recovered by an actual prefix take. -/
theorem take_embed (entry : Tagged) (extra : List ℕ) (p : ℕ)
    (hshape : entry.coefficients.length=entry.current.rank) :
    ((embed entry extra p).value.coefficients.take entry.current.rank)=entry.coefficients := by
  rw [embed_coefficients,←hshape,List.take_left]

/-- Every old coefficient index is literally preserved. -/
theorem get_embed (entry : Tagged) (extra : List ℕ) (p i : ℕ)
    (hi : i<entry.coefficients.length) :
    ((embed entry extra p).value.coefficients[i]?).getD []=
      (entry.coefficients[i]?).getD [] := by
  rw [embed_coefficients,List.getElem?_append_left hi]

/-- Positive added axis dimensions make the resulting dense vector shape exact. -/
theorem embed_shape (entry : Tagged) (extra : List ℕ) (p : ℕ)
    (hshape : entry.coefficients.length=entry.current.rank) (hextra : 0<extra.prod) :
    (embed entry extra p).value.coefficients.length=(embed entry extra p).value.current.rank := by
  rw [embed_coefficients,embed_rank,List.length_append,List.length_replicate,hshape]
  have he : extra.prod-1+1=extra.prod := by omega
  nlinarith

/-- Two successive zero blocks have exactly the direct extension length. -/
theorem padding_compose (r A B : ℕ) (hA : 0<A) (hB : 0<B) :
    r*(A-1)+(A*r)*(B-1)=r*(B*A-1) := by
  have h1 : r≤r*A := Nat.le_mul_of_pos_right r hA
  have h2 : r*A≤r*A*B := Nat.le_mul_of_pos_right (r*A) hB
  have he : (r*A-r)+(r*A*B-r*A)=r*A*B-r := by omega
  simpa only [Nat.mul_sub_left_distrib,Nat.mul_one,Nat.mul_assoc,Nat.mul_comm,
    Nat.mul_left_comm] using he

/-- Extending first by A then by B preserves the same creation tag and
coefficient vector as a single outer-prefix extension B++A. -/
theorem embed_compose (entry : Tagged) (A B : List ℕ) (p q : ℕ)
    (hA : 0<A.prod) (hB : 0<B.prod) :
    (embed (embed entry A p).value B q).value=
      (embed entry (B++A) q).value := by
  have he:=padding_compose entry.current.rank A.prod B.prod hA hB
  simp only [embed,copyVector_value,Context.rank,List.prod_append,List.append_assoc,
    ← List.replicate_add]
  cases entry with
  | mk creation current coefficients =>
    simp only [Tagged.mk.injEq,true_and]
    dsimp only [Context.rank] at he
    rw [he]

/-- Every word width is inherited or zero, with no output Fits premise. -/
theorem embed_width (entry : Tagged) (extra : List ℕ) (p W : ℕ)
    (hw : ∀w∈entry.coefficients,w.length≤W) :
    ∀w∈(embed entry extra p).value.coefficients,w.length≤W := by
  rw [embed_coefficients]
  intro w h
  rcases List.mem_append.mp h with h|h
  · exact hw w h
  · have hz:=List.eq_of_mem_replicate h
    subst w
    exact Nat.zero_le W

/-- The actual embedding report, including every zero cell and copied old spine. -/
theorem embed_clock (entry : Tagged) (extra : List ℕ) (p : ℕ) :
    (embed entry extra p).clock=
      3*(entry.coefficients.map List.length).sum+5*entry.coefficients.length+
      entry.current.rank*(extra.prod-1)+extra.length+entry.current.axes.length+8 := by
  simp only [embed,copyVector_value,copyVector_clock,List.length_replicate]
  omega

/-- Precision interpretation is ordinary coordinatewise modular projection. -/
def coordinateResidue (p : ℕ) (w : List Bool) : ℕ := bitValue w%2^p

/-- Lifting a creator's canonical representative keeps its numerical value at
higher precision. This is a SET operation, not a ring-homomorphism claim. -/
theorem canonical_lift_value (w : List Bool) (pc p : ℕ)
    (hw : bitValue w<2^pc) (hp : pc≤p) : coordinateResidue p w=bitValue w := by
  apply Nat.mod_eq_of_lt
  exact hw.trans_le (Nat.pow_le_pow_right (by decide : 1≤2) hp)

/-- Higher-to-lower modular projection agrees with direct coordinate reduction. -/
theorem projection_consistent (w : List Bool) (p q : ℕ) (hq : q≤p) :
    (coordinateResidue p w)%2^q=coordinateResidue q w := by
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hq)

/-- All actual embedding copies and allocations have an explicit dimension bound. -/
theorem embed_clock_le (entry : Tagged) (extra : List ℕ) (p W : ℕ)
    (hshape : entry.coefficients.length=entry.current.rank)
    (hw : ∀w∈entry.coefficients,w.length≤W) :
    (embed entry extra p).clock≤entry.current.rank*(3*W+5)+
      entry.current.rank*(extra.prod-1)+extra.length+entry.current.axes.length+8 := by
  have hc:=copyVector_clock_le entry.coefficients W hw
  simp only [embed,copyVector_value,List.length_replicate]
  rw [hshape] at hc ⊢
  nlinarith

/-- New outer zero coordinates and all copied old coordinates are canonical at
any precision above the immutable creator precision. -/
theorem embed_values (entry : Tagged) (extra : List ℕ) (p : ℕ)
    (hp : entry.creation.precision≤p)
    (hc : ∀w∈entry.coefficients,bitValue w<2^entry.creation.precision) :
    ∀w∈(embed entry extra p).value.coefficients,bitValue w<2^p := by
  rw [embed_coefficients]
  intro w hw
  rcases List.mem_append.mp hw with hw|hw
  · exact (hc w hw).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) hp)
  · have hz:=List.eq_of_mem_replicate hw
    subst w
    exact pow_pos (by decide : 0<2) p

/-- The scalar modular interpretation of every old coordinate is preserved. -/
theorem embed_coordinate_residue (entry : Tagged) (extra : List ℕ) (p i : ℕ)
    (hi : i<entry.coefficients.length) :
    coordinateResidue p (((embed entry extra p).value.coefficients[i]?).getD [])=
      coordinateResidue p ((entry.coefficients[i]?).getD []) := by
  rw [get_embed entry extra p i hi]

end RiemannGaussian.SemiprimeD1JetAxes
