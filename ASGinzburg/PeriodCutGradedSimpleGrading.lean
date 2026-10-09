import ASGinzburg.PeriodCutGradedSimpleSpaces

/-! The actual simple total space is concentrated in degree minus its sheet. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerSimpleDegreeSpace_subsingleton (z : Q.LiftVertex) (q : ℤ)
    (hq : q≠-z.2) :
    Subsingleton (E.CornerModuleDegreeSpace Q
      ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) q) := by
  letI : ∀ i : Q.Vertex,Subsingleton (E.CornerModuleSpace Q
    ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) (i,-q)) := fun i =>
    E.cornerSimpleSpace_off Q z (i,-q) (by
      intro h
      have hs := congrArg Prod.snd h
      dsimp only at hs
      exact hq (by omega))
  infer_instance

theorem cornerSimpleGrade_off (z : Q.LiftVertex) (q : ℤ) (hq : q≠-z.2) :
    E.cornerModuleGrade Q ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) q=⊥ := by
  letI := E.cornerSimpleDegreeSpace_subsingleton Q z q hq
  apply le_antisymm _ bot_le
  rintro v ⟨w,rfl⟩
  have hw : w=0 := Subsingleton.elim _ _
  rw [hw,map_zero]
  exact Submodule.zero_mem _

theorem cornerSimpleGrade_diagonal (z : Q.LiftVertex) :
    E.cornerModuleGrade Q ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) (-z.2)=⊤ := by
  apply top_unique
  intro v hv
  have hm := E.cornerModule_lof_mem_grade Q
    ((E.cornerCoverZAlgebra Q).simpleRightModule (Q.height z)) (-z.2) z (by simp)
    (E.cornerSimpleTotalSpaceEquiv Q z v)
  have he := (E.cornerSimpleTotalSpaceEquiv Q z).symm_apply_apply v
  change DirectSum.lof k Q.LiftVertex _ z (E.cornerSimpleTotalSpaceEquiv Q z v)=v at he
  rwa [he] at hm

end ASGinzburg.ZAlgebra.PeriodIso
