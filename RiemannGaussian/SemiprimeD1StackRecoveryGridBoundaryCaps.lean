/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridStateCaps
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowCleanup
import RiemannGaussian.SemiprimeD1StackRecoveryGridRowBases
/-! # Physical metadata, power and cleanup boundary cap preservation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridBoundaryCaps
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data put_registers put_data power_width update_le)
end Caps
namespace T
export SemiprimeD1StackRecoveryGridTransient (result caches)
end T
/-- Actual metadata/product-bank replacement preserves every other physical word. -/
theorem product_data (w:Words) (p:P.Stack→List Bool) (L:Nat) (hw:Caps.Data w L) (hp:∀k,(p k).length≤ L) :
    Caps.Data {w with product:=p} L:=by
  intro k
  rcases k with k|k
  · exact hw (rationalStack k)
  · rcases k with k|k
    · exact hw (geometryAux k)
    · rcases k with k|k
      · exact hw (divisionStack k)
      · rcases k with k|k
        · exact hp k
        · rcases k with k|k
          · exact hw (reg k.1 k.2)
          · exact hw (aux k)
/-- The acquired unary multiplicity is the only nonempty product word. -/
theorem metadata_data (w:Words) (m L:Nat) (hw:Caps.Data w L) (hm:m≤ L) :
    Caps.Data {w with product:=SemiprimeD1StackUnaryProduct.contents [] [] [] (List.replicate m true)} L:=by
  apply product_data w _ L hw
  intro k
  cases k <;> first
    | exact Nat.zero_le _
    | change (List.replicate m true).length≤L;rw [List.length_replicate];exact hm
/-- Real transient cleanup cannot enlarge any actual register word. -/
theorem transient_registers (w:Words) (B:Nat) (hw:Caps.Registers w B) :Caps.Registers (T.result w) B:=by
  intro r b
  change (if r∈T.caches then [] else w.registers (r,b)).length≤ B
  split
  · exact Nat.zero_le _
  · exact hw r b
/-- Real transient cleanup preserves every actual foreign-data word cap. -/
theorem transient_data (w:Words) (L:Nat) (hw:Caps.Data w L) :Caps.Data (T.result w) L:=by
  intro k
  rcases k with k|k
  · exact hw (rationalStack k)
  · rcases k with k|k
    · exact hw (geometryAux k)
    · rcases k with k|k
      · exact hw (divisionStack k)
      · rcases k with k|k
        · exact hw (productStack k)
        · rcases k with k|k
          · change (if k.1∈T.caches then [] else w.registers k).length≤ L
            split
            · exact Nat.zero_le _
            · exact hw (reg k.1 k.2)
          · exact hw (aux k)
/-- Actual product cleanup only erases cells and preserves its global data cap. -/
theorem product_clear_data (w:Words) (L:Nat) (hw:Caps.Data w L) :
    Caps.Data {w with product:=Function.update w.product .product []} L:=by
  have h:=Caps.update_le (bank w) (productStack .product) [] L hw (Nat.zero_le _)
  rw [update_product] at h
  exact h
/-- Whole physical row cleanup keeps both register and foreign-word caps. -/
theorem row_product_data (w:Words) (L:Nat) (hw:Caps.Data w L) :
    Caps.Data (SemiprimeD1StackRecoveryGridRowCleanup.productCleared w) L:=
  product_clear_data (T.result w) L (transient_data w L hw)
/-- Both actual power cache writes retain semantic register widths, including literal m0 one. -/
theorem powers_registers (w:Words) (width:List Bool) (m B:Nat) (hw:Caps.Registers w B) (hW:width.length+2≤ B) :
    Caps.Registers (SemiprimeD1StackRecoveryGridRowBases.powersResult w width m) B:=by
  have hn:=Caps.power_width width (getReg w .numBase) m B hW
  have h0:=Caps.put_registers w .numPower _ B hw hn.1 hn.2
  let ready:=SemiprimeD1StackRecoveryGridRowBases.numeratorPower w width m
  have hd:=Caps.power_width width (getReg ready .denBase) m B hW
  exact Caps.put_registers ready .denPower _ B h0 hd.1 hd.2
/-- Both actual power results retain foreign actual data caps, independent of numeric coefficient values. -/
theorem powers_data (w:Words) (width:List Bool) (m L:Nat) (hw:Caps.Data w L) (hW:width.length+2≤ L) :
    Caps.Data (SemiprimeD1StackRecoveryGridRowBases.powersResult w width m) L:=by
  have hn:=Caps.power_width width (getReg w .numBase) m L hW
  have h0:=Caps.put_data w .numPower _ L hw hn.1 hn.2
  let ready:=SemiprimeD1StackRecoveryGridRowBases.numeratorPower w width m
  have hd:=Caps.power_width width (getReg ready .denBase) m L hW
  exact Caps.put_data ready .denPower _ L h0 hd.1 hd.2
end RiemannGaussian.SemiprimeD1StackRecoveryGridBoundaryCaps
