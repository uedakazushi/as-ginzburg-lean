import ASGinzburg.PeriodCornerModuleDegreeDecomposition

/-! The actual cut-module total space is the internal direct sum of its integer grades. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cornerModuleDegreeRangeEquiv
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    (⨁ q : ℤ,E.CornerModuleDegreeSpace Q M q) ≃ₗ[k] ⨁ q : ℤ,E.cornerModuleGrade Q M q :=
  DFinsupp.mapRange.linearEquiv (E.cornerModuleDegreeGradeEquiv Q M)

theorem cornerModuleDegreeRangeEquiv_map
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    (E.cornerModuleDegreeRangeEquiv Q M).toLinearMap=E.cornerModuleDegreeRangeMap Q M := by
  apply DFinsupp.lhom_ext
  intro q x
  change E.cornerModuleDegreeRangeEquiv Q M
    (DirectSum.lof k ℤ (E.CornerModuleDegreeSpace Q M) q x)=
      E.cornerModuleDegreeRangeMap Q M
        (DirectSum.lof k ℤ (E.CornerModuleDegreeSpace Q M) q x)
  rw [cornerModuleDegreeRangeMap,DirectSum.toModule_lof]
  change DFinsupp.mapRange (fun q => E.cornerModuleDegreeGradeEquiv Q M q)
    (fun q => (E.cornerModuleDegreeGradeEquiv Q M q).map_zero)
    (DFinsupp.single q x)=DFinsupp.single q (E.cornerModuleDegreeGradeEquiv Q M q x)
  exact DFinsupp.mapRange_single

theorem cornerModuleDegreeRangeEquiv_coe
    (M : (E.cornerCoverZAlgebra Q).RightModule)
    (x : ⨁ q : ℤ,E.CornerModuleDegreeSpace Q M q) :
    DirectSum.coeLinearMap (E.cornerModuleGrade Q M)
      (E.cornerModuleDegreeRangeEquiv Q M x)=
        (E.cornerModuleDegreeEquiv Q M).symm x := by
  have h := E.cornerModuleDegreeRangeMap_left Q M
  rw [← E.cornerModuleDegreeRangeEquiv_map Q M] at h
  exact LinearMap.congr_fun h x

noncomputable instance cornerModuleGradeDecomposition
    (M : (E.cornerCoverZAlgebra Q).RightModule) :
    DirectSum.Decomposition (E.cornerModuleGrade Q M) where
  decompose' x := E.cornerModuleDegreeRangeEquiv Q M (E.cornerModuleDegreeEquiv Q M x)
  left_inv x := by
    change DirectSum.coeLinearMap (E.cornerModuleGrade Q M)
      (E.cornerModuleDegreeRangeEquiv Q M (E.cornerModuleDegreeEquiv Q M x))=x
    rw [E.cornerModuleDegreeRangeEquiv_coe]
    exact (E.cornerModuleDegreeEquiv Q M).symm_apply_apply x
  right_inv x := by
    obtain ⟨z,rfl⟩ := (E.cornerModuleDegreeRangeEquiv Q M).surjective x
    change E.cornerModuleDegreeRangeEquiv Q M
      (E.cornerModuleDegreeEquiv Q M (DirectSum.coeLinearMap (E.cornerModuleGrade Q M)
        (E.cornerModuleDegreeRangeEquiv Q M z)))=E.cornerModuleDegreeRangeEquiv Q M z
    rw [E.cornerModuleDegreeRangeEquiv_coe,(E.cornerModuleDegreeEquiv Q M).apply_symm_apply]

theorem cornerModuleGrade_isInternal (M : (E.cornerCoverZAlgebra Q).RightModule) :
    DirectSum.IsInternal (E.cornerModuleGrade Q M) :=
  DirectSum.Decomposition.isInternal _

end ASGinzburg.ZAlgebra.PeriodIso
