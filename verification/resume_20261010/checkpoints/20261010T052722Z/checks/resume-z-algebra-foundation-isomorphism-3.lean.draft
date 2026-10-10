import ASGinzburg.ZAlgebraIsomorphisms
import ASGinzburg.FoundationAlgebra
import ASGinzburg.FiniteComponentAlgebraEquiv
import ASGinzburg.FiniteComponentIdempotents

/-! Every actual vertex-fixed Z-algebra isomorphism restricts to a genuine
vertex-fixed algebra isomorphism of the original finite foundations. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
universe u
variable {k : Type u} [Field k] {B : ZAlgebra.{u,u} k} {A : ZAlgebra.{u,u} k}
  (F : Isomorphism B A) (Q : CutQuiver)

noncomputable def foundationComponentIsomorphism :
    (B.foundationComponents Q).Isomorphism (A.foundationComponents Q) where
  map i j := F.map (i.val:ℤ) (j.val:ℤ)
  map_id i := F.map_id (i.val:ℤ)
  map_comp f g := F.map_comp f g

noncomputable def foundationAlgEquiv :
    (B.foundationComponents Q).Total ≃ₐ[k] (A.foundationComponents Q).Total :=
  (F.foundationComponentIsomorphism Q).totalAlgEquiv

theorem foundationAlgEquiv_apply (x : (B.foundationComponents Q).Total) (i j : Q.Vertex) :
    F.foundationAlgEquiv Q x i j = F.map (i.val:ℤ) (j.val:ℤ) (x i j) := rfl

theorem foundationAlgEquiv_vertex (i : Q.Vertex) :
    F.foundationAlgEquiv Q ((B.foundationComponents Q).totalIdempotent i) =
      (A.foundationComponents Q).totalIdempotent i := by
  classical
  funext p q
  rw [F.foundationAlgEquiv_apply]
  by_cases hp : p=i
  · subst p
    by_cases hq : q=i
    · subst q
      simp only [LinearComponentAlgebra.totalIdempotent,
        LinearComponentAlgebra.totalComponent_apply_same]
      exact F.map_id (i.val:ℤ)
    · simp [LinearComponentAlgebra.totalIdempotent,LinearComponentAlgebra.totalComponent,hq]
  · simp [LinearComponentAlgebra.totalIdempotent,LinearComponentAlgebra.totalComponent,hp]

end ASGinzburg.ZAlgebra.Isomorphism
