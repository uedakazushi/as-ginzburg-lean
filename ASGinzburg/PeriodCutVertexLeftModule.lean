import ASGinzburg.PeriodCutCharacterClassification
import Mathlib.RingTheory.SimpleModule.Basic

/-! The actual one-dimensional vertex module for the native cut algebra.
Its action is evaluation of the genuine scalar augmentation. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutVertexLeftModule (i : Q.Vertex) :
    Module (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) k :=
  Module.compHom k (E.cutVertexCharacter Q i).toRingHom

noncomputable def cutVertexLeftScalarTower (i : Q.Vertex) :
    letI := E.cutVertexLeftModule Q i
    IsScalarTower k (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) k := by
  letI := E.cutVertexLeftModule Q i
  constructor
  intro c r x
  change E.cutVertexCharacter Q i (c • r)*x=c*(E.cutVertexCharacter Q i r*x)
  rw [map_smul,smul_eq_mul,mul_assoc]

theorem cutVertexLeft_isSimple (i : Q.Vertex) :
    letI := E.cutVertexLeftModule Q i
    IsSimpleModule (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) k := by
  letI := E.cutVertexLeftModule Q i
  letI := E.cutVertexLeftScalarTower Q i
  refine {eq_bot_or_eq_top := ?_}
  intro N
  rcases eq_bot_or_eq_top (N.restrictScalars k) with h | h
  · left
    apply Submodule.restrictScalars_injective k (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) k
    simpa only [Submodule.restrictScalars_bot] using h
  · right
    apply Submodule.restrictScalars_injective k (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) k
    simpa only [Submodule.restrictScalars_top] using h

end ASGinzburg.ZAlgebra.PeriodIso
