import RiemannGaussian.SemiprimeMeasurementBits
open RiemannGaussian.SemiprimeMeasurementBits
open RiemannGaussian.SemiprimeBitIndexClipping
set_option autoImplicit false
private def p1 : SignedWord := ⟨false,[true]⟩
private def p2 : SignedWord := ⟨false,[false,true]⟩
private def p3 : SignedWord := ⟨false,[true,true]⟩
private def m1 : SignedWord := ⟨true,[true]⟩
private def m3 : SignedWord := ⟨true,[true,true]⟩
private def nz : SignedWord := ⟨true,[false,false]⟩
#eval (equal nz zero).accepted
#eval (dot [p3,m3,p2] [true,true,true]).word.value
#eval (test [([p3,m3,p2],p2)] [true,true,true]).accepted
#eval (test [([p3,m3,p2],p1)] [true,true,true]).accepted
private def rows : Fin 2 → Fin 3 → SignedWord := ![![p1,m1,zero],![zero,zero,p1]]
#eval ((representative 3 2 rows ![zero,p1]).found.map (fun bits => List.ofFn bits))
#eval ((representative 3 2 rows ![p2,p1]).found.map (fun bits => List.ofFn bits))
