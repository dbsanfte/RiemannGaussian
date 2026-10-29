/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineResource
/-! # Actual true-geometry/product cleanup bank retains its physical byte cap -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineRetainedData
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
namespace Old
export SemiprimeD1StackRecoveryGridWordCaps (Data auxiliary_data mass_le)
export SemiprimeD1StackRecoveryGridStateCaps (geometry_data)
export SemiprimeD1StackRecoveryGridBoundaryCaps (product_data)
end Old
/-- SAME physically acquired G14 fields, copied binaryt, cleared marker temporaries and empty product bank preserve all104 old caps. -/
theorem product_cleared_data (w:Words) (a h u:Nat) (t:List Bool) (L:Nat)
    (hw:Old.Data w.toWords L) (ht:t.length≤ L) (hg:20000*(a+t.length+1)≤ L):
    Old.Data (SemiprimeD1StackRecoveryAffineRetained.productCleared w a h u t).toWords L:=by
  have h0:=Old.auxiliary_data w.toWords .q t L hw ht
  have h1:=Old.geometry_data (SemiprimeD1StackRecoveryAffineRetained.asked w t).toWords (List.replicate a true) t L h0
    (by simpa only [List.length_replicate] using hg)
  change Old.Data (SemiprimeD1StackRecoveryAffineRetained.geometric w a t).toWords L at h1
  have h2:=Old.auxiliary_data _ .orderTodo [] L h1 (Nat.zero_le _)
  have h3:=Old.product_data _ (SemiprimeD1StackUnaryProduct.contents [] [] [] []) L h2
    (by intro slot;cases slot <;> exact Nat.zero_le _)
  exact h3
/-- Every actual physical old word is counted in the true ten-role cleanup's original mass allowance. -/
theorem product_cleared_mass (w:Words) (a h u:Nat) (t:List Bool) (L:Nat)
    (hw:Old.Data w.toWords L) (ht:t.length≤ L) (hg:20000*(a+t.length+1)≤ L):
    SemiprimeD1StackRecoveryGridCleanup.mass
      (SemiprimeD1StackRecoveryGridView.bank (SemiprimeD1StackRecoveryAffineRetained.productCleared w a h u t).toWords)≤ 104*L:=
  Old.mass_le _ L (product_cleared_data w a h u t L hw ht hg)
end RiemannGaussian.SemiprimeD1StackRecoveryAffineRetainedData
