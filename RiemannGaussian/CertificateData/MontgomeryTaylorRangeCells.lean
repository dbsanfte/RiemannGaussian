/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells00
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells01
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells02
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells03
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells04
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells05
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells06
import RiemannGaussian.CertificateData.MontgomeryTaylorRangeCells07

/-!
# The complete kernel-checked continuous range table

The 9306 consecutive cells cover all real separations from `166/500` to
`9472/500`. The table controls both squared value and signed curvature.
It is one component of the proposed seven-point certificate, not by itself
a proved improvement of the zeta zero-count proportion.
-/

namespace RiemannGaussian.MontgomeryTaylorRangeTable.CertificateData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The complete continuous value and curvature table. -/
def table : Table :=
(.node (Int.ofNat 0, Int.negSucc 15536297907304) (4774 / 500) (.node (Int.ofNat 0, Int.negSucc 15536297907304) (2470 / 500) (.node (Int.ofNat 0, Int.negSucc 15536297907304) (1318 / 500) Group00.table Group01.table) (.node (Int.ofNat 0, Int.negSucc 50410831779) (3622 / 500) Group02.table Group03.table)) (.node (Int.ofNat 0, Int.negSucc 15681458517) (7078 / 500) (.node (Int.ofNat 0, Int.negSucc 15681458517) (5926 / 500) Group04.table Group05.table) (.node (Int.ofNat 0, Int.negSucc 7179895858) (8230 / 500) Group06.table Group07.table)))

/-- All continuous cells and all cached range bounds pass the Lean kernel. -/
theorem table_checked : check table (166 / 500) (9472 / 500) = true :=
  check_node (check_node (check_node (Group00.table_checked) (Group01.table_checked) (by decide +kernel) (by decide +kernel)) (check_node (Group02.table_checked) (Group03.table_checked) (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)) (check_node (check_node (Group04.table_checked) (Group05.table_checked) (by decide +kernel) (by decide +kernel)) (check_node (Group06.table_checked) (Group07.table_checked) (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

/-- The complete continuous analytic meaning of the stored range table. -/
theorem table_valid : Valid table (166 / 500) (9472 / 500) := check_sound table_checked

end RiemannGaussian.MontgomeryTaylorRangeTable.CertificateData
