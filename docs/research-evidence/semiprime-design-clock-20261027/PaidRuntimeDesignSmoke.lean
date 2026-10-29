import RiemannGaussian.SemiprimePaidRuntimeDesign
open RiemannGaussian
open SemiprimeRuntimeDesignAcquisition
private def raw : RawDesign 1 1 where
  r := 1
  head := fun _ => 0
  assigned := fun _ => 0
  count := fun _ => 1
  rows := fun _ _ _ => -1
  W := fun _ => 1
private def acquired := SemiprimePaidRuntimeDesign.build raw (fun _ _ _ => ⟨-1,7⟩) 0
#eval (let out := acquired
       if hr : 0<out.value.r then
         let g : Fin out.value.r := ⟨0,hr⟩
         if hm : 0<out.value.m g then
           if hh : 0<out.value.h g then
             (out.value.r,out.value.h g,out.value.m g,out.value.C g ⟨0,hm⟩ ⟨0,hh⟩,out.work)
           else (out.value.r,0,out.value.m g,0,out.work)
         else (out.value.r,out.value.h g,0,0,out.work)
       else (0,0,0,0,out.work))
