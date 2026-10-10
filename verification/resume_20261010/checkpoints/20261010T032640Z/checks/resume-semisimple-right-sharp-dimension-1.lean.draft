import work.ASGinzburgDraft.ASCutSemisimpleRightDimension
import work.ASGinzburgDraft.ASCutOrdinarySimpleSharpDimension

/-! The actual radical quotient has projective dimension exactly three
when the cut has a vertex. This lower bound is obtained from a genuine
vertex summand and nonzero actual third Tor of that ordinary simple. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutSemisimpleRight_projectiveDimension_ge_three
    (hAS : A.ASRegular Q) (i : Q.Vertex) :
    (3 : WithBot ℕ∞) ≤ projectiveDimension (hAS.cutSemisimpleRightObject A Q) := by
  let X := fun j : Q.Vertex => hAS.cutOrdinarySimple A Q (j,0)
  let r : Retract (X i) (⨁ X) :=
    { i := biproduct.ι X i
      r := biproduct.π X i
      retract := biproduct.ι_π_self X i }
  have h := r.projectiveDimension_le
  rw [← projectiveDimension_eq_of_iso (hAS.cutSemisimpleRightVertexIso A Q)] at h
  exact (hAS.cutOrdinarySimple_projectiveDimension_ge_three A Q (i,0)).trans h

theorem ASRegular.cutSemisimpleRight_projectiveDimension_eq_three
    (hAS : A.ASRegular Q) [Nonempty Q.Vertex] :
    projectiveDimension (hAS.cutSemisimpleRightObject A Q) = 3 := by
  obtain ⟨i⟩ := ‹Nonempty Q.Vertex›
  exact le_antisymm ((projectiveDimension_le_iff _ 3).mpr inferInstance)
    (hAS.cutSemisimpleRight_projectiveDimension_ge_three A Q i)

end ASGinzburg.ZAlgebra
