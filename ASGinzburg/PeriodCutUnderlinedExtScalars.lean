import ASGinzburg.PeriodCutUnderlinedExtRepresentation

/-! The actual underlined Ext left R module retains its original
k-linear structure and the compatible scalar tower. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutUnderlinedExtScalarTower (M : E.CutGradedRightModule Q) (n : ℕ) :
    letI := E.cutUnderlinedExtLeftModule Q M n
    IsScalarTower k (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
      (E.CutUnderlinedRegularExt Q M n) := by
  letI := E.cutUnderlinedExtLeftModule Q M n
  constructor
  intro c r x
  change E.cutUnderlinedExtLeftRepresentation Q M n (c • r) x=
      c • E.cutUnderlinedExtLeftRepresentation Q M n r x
  rw [map_smul,LinearMap.smul_apply]

noncomputable def cutUnderlinedExtScalarComm (M : E.CutGradedRightModule Q) (n : ℕ) :
    letI := E.cutUnderlinedExtLeftModule Q M n
    SMulCommClass k (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
      (E.CutUnderlinedRegularExt Q M n) := by
  letI := E.cutUnderlinedExtLeftModule Q M n
  constructor
  intro c r x
  change c • E.cutUnderlinedExtLeftRepresentation Q M n r x=
      E.cutUnderlinedExtLeftRepresentation Q M n r (c • x)
  exact ((E.cutUnderlinedExtLeftRepresentation Q M n r).map_smul c x).symm

end ASGinzburg.ZAlgebra.PeriodIso
