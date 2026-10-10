import ASGinzburg.PeriodCutUnderlinedExtLinearity

/-! Actual left multiplication followed by Ext postcomposition extends
to a genuine unital k-algebra representation of the entire cut ring. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutUnderlinedExtHomogeneousComponent_one (M : E.CutGradedRightModule Q) (n : ℕ) :
    E.cutUnderlinedExtHomogeneousComponent Q M n 0
      (GradedMonoid.GOne.one : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) 0)=1 :=
  E.cutUnderlinedExtHomogeneousOperator_one Q M n

theorem cutUnderlinedExtHomogeneousComponent_mul (M : E.CutGradedRightModule Q) (p : ℕ)
    {m n : ℕ}
    (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m)
    (b : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) n) :
    E.cutUnderlinedExtHomogeneousComponent Q M p (m+n) (GradedMonoid.GMul.mul a b)=
      E.cutUnderlinedExtHomogeneousComponent Q M p m a*
        E.cutUnderlinedExtHomogeneousComponent Q M p n b :=
  E.cutUnderlinedExtHomogeneousOperator_mul Q M p m n a b

noncomputable def cutUnderlinedExtLeftRepresentation (M : E.CutGradedRightModule Q) (n : ℕ) :
    E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) →ₐ[k]
      Module.End k (E.CutUnderlinedRegularExt Q M n) :=
  DirectSum.toAlgebra k _ (E.cutUnderlinedExtHomogeneousComponent Q M n)
    (E.cutUnderlinedExtHomogeneousComponent_one Q M n)
    (E.cutUnderlinedExtHomogeneousComponent_mul Q M n)

theorem cutUnderlinedExtLeftRepresentation_homogeneous (M : E.CutGradedRightModule Q)
    (n m : ℕ) (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m) :
    E.cutUnderlinedExtLeftRepresentation Q M n
      (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a)=
        E.cutUnderlinedExtHomogeneousOperator Q M n m a := by
  change DirectSum.toModule k ℕ _ (E.cutUnderlinedExtHomogeneousComponent Q M n)
    (DirectSum.lof k ℕ _ m a)=_
  rw [DirectSum.toModule_lof]
  rfl

noncomputable def cutUnderlinedExtLeftModule (M : E.CutGradedRightModule Q) (n : ℕ) :
    Module (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
      (E.CutUnderlinedRegularExt Q M n) :=
  Module.compHom _ (E.cutUnderlinedExtLeftRepresentation Q M n).toRingHom

noncomputable def cutUnderlinedExtLeftModuleCat (M : E.CutGradedRightModule Q) (n : ℕ) :
    ModuleCat.{v} (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) := by
  letI := E.cutUnderlinedExtLeftModule Q M n
  exact ModuleCat.of _ (E.CutUnderlinedRegularExt Q M n)

theorem cutUnderlinedExtLeftModule_homogeneous_smul (M : E.CutGradedRightModule Q)
    (n m : ℕ) (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m)
    (x : E.CutUnderlinedRegularExt Q M n) :
    letI := E.cutUnderlinedExtLeftModule Q M n
    E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a • x=
      E.cutUnderlinedExtHomogeneousOperator Q M n m a x := by
  letI := E.cutUnderlinedExtLeftModule Q M n
  change E.cutUnderlinedExtLeftRepresentation Q M n
    (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a) x=_
  rw [E.cutUnderlinedExtLeftRepresentation_homogeneous]

end ASGinzburg.ZAlgebra.PeriodIso
