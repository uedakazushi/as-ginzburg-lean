import ASGinzburg.PeriodCutZeroScalarCharacters
import ASGinzburg.PeriodCutAugmentationKernel

/-! Classification of genuine algebra characters from their homogeneous
values. The AS application derives both hypotheses from the actual Ext action. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutVertexCharacter (i : Q.Vertex) :
    E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) →ₐ[k] k :=
  (Pi.evalAlgHom k (fun _ : Q.Vertex => k) i).comp (E.cutAugmentation Q)

theorem cutVertexCharacter_apply (i : Q.Vertex)
    (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) :
    E.cutVertexCharacter Q i r=E.cutAugmentation Q r i := rfl

theorem cutCharacter_eq_vertex
    (χ : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) →ₐ[k] k) (i : Q.Vertex)
    (hvertex : ∀ j : Q.Vertex,χ (E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) j)=
      if j=i then 1 else 0)
    (hpositive : ∀ (m : ℕ) (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) (m+1)),
      χ (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) (m+1) a)=0) :
    χ=E.cutVertexCharacter Q i := by
  classical
  apply AlgHom.ext
  intro r
  refine DirectSum.induction_on r ?_ ?_ ?_
  · rw [map_zero,map_zero]
  · intro m a
    change χ (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a)=
      E.cutAugmentation Q (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a) i
    cases m with
    | zero =>
      rw [E.cutAugmentation_zero_component]
      exact E.cutCharacter_zeroComponent_eq_diagonal Q χ i hvertex a
    | succ m =>
      rw [hpositive,E.cutAugmentation_positive_component]
      rfl
  · intro r s hr hs
    rw [map_add,map_add,hr,hs]

end ASGinzburg.ZAlgebra.PeriodIso
