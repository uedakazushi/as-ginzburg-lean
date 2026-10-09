import ASGinzburg.PeriodCornerModuleInternalGrading

/-! Vertex inclusions lie in precisely the degree given by their negative sheet. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerModuleDegreeInsertion_lof
    (M : (E.cornerCoverZAlgebra Q).RightModule) (q : ℤ) (i : Q.Vertex)
    (v : E.CornerModuleSpace Q M (i,-q)) :
    E.cornerModuleDegreeInsertion Q M q
      (DirectSum.lof k Q.Vertex (fun i => E.CornerModuleSpace Q M (i,-q)) i v)=
        DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) (i,-q) v := by
  apply (E.cornerModuleDegreeEquiv Q M).injective
  change E.cornerModuleDegreeEquiv Q M
    ((E.cornerModuleDegreeEquiv Q M).symm
      (DirectSum.lof k ℤ (E.CornerModuleDegreeSpace Q M) q
        (DirectSum.lof k Q.Vertex (fun i => E.CornerModuleSpace Q M (i,-q)) i v)))=_
  rw [(E.cornerModuleDegreeEquiv Q M).apply_symm_apply]
  apply DFinsupp.ext
  intro p
  apply DFinsupp.ext
  intro j
  rw [E.cornerModuleDegreeEquiv_apply]
  by_cases hp : p=q
  · subst p
    by_cases hj : j=i
    · subst j
      simp only [DirectSum.lof_eq_of,DirectSum.of_eq_same]
    · have hji : (j,-q)≠(i,-q) := by simpa using hj
      simp only [DirectSum.lof_eq_of,DirectSum.of_eq_same,
        DirectSum.of_eq_of_ne _ _ _ hj,DirectSum.of_eq_of_ne _ _ _ hji]
  · have hji : (j,-p)≠(i,-q) := by
      intro h
      exact hp (neg_inj.mp (congrArg Prod.snd h))
    simp only [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne _ _ _ hp,
      DirectSum.of_eq_of_ne _ _ _ hji,DirectSum.zero_apply]

theorem cornerModule_lof_mem_grade
    (M : (E.cornerCoverZAlgebra Q).RightModule) (q : ℤ) (x : Q.LiftVertex)
    (h : x.2=-q) (v : E.CornerModuleSpace Q M x) :
    DirectSum.lof k Q.LiftVertex (E.CornerModuleSpace Q M) x v∈
      E.cornerModuleGrade Q M q := by
  rcases x with ⟨i,s⟩
  dsimp only at h
  subst s
  exact ⟨DirectSum.lof k Q.Vertex (fun i => E.CornerModuleSpace Q M (i,-q)) i v,
    E.cornerModuleDegreeInsertion_lof Q M q i v⟩

end ASGinzburg.ZAlgebra.PeriodIso
