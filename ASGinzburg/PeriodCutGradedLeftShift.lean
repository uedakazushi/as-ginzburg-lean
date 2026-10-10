import ASGinzburg.PeriodCutGradedLeftModules

namespace ASGinzburg.ZAlgebra.PeriodIso.CutGradedLeftModule
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable {Q : CutQuiver} {E : A.PeriodIso (Q.vertices:ℤ)}

noncomputable def shiftedDecomposition (M : CutGradedLeftModule.{u,v,w} Q E) (t : ℤ) :
    DirectSum.Decomposition (fun q => M.grade (q+t)) := by
  letI := M.decomposition
  have h : DirectSum.IsInternal M.grade := DirectSum.Decomposition.isInternal _
  apply DirectSum.IsInternal.chooseDecomposition (fun q => M.grade (q+t))
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact h.submodule_iSupIndep.comp (Equiv.addRight t).injective
  · exact (Equiv.addRight t).iSup_comp.trans h.submodule_iSup_eq_top

noncomputable def shifted (M : CutGradedLeftModule.{u,v,w} Q E) (t : ℤ) :
    CutGradedLeftModule.{u,v,w} Q E where
  space := M.space
  representation := M.representation
  grade q := M.grade (q+t)
  decomposition := M.shiftedDecomposition t
  homogeneous m r q x hx := by
    have h := M.homogeneous m r (q+t) x hx
    simpa only [show q+t+(m:ℤ)=q+(m:ℤ)+t by ring] using h

end ASGinzburg.ZAlgebra.PeriodIso.CutGradedLeftModule
