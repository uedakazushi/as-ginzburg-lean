import ASGinzburg.PathArrowSubstitutionInverse
import ASGinzburg.PathAutomorphismGradings
import ASGinzburg.FiniteComponentAutomorphismProducts

/-! An actual vertex-fixed path automorphism is the genuine substitution
of its actual arrow images, including arbitrary nonlinear images. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def VertexCutPathAutomorphism.arrowReplacement
    (E : Q.VertexCutPathAutomorphism k) : Q.PathArrowReplacement k :=
  fun a => VertexCutPathAutomorphism.componentLinearEquiv Q k E
    (Q.source a) (Q.target a) (Q.pathIdentityArrowReplacement k a)

theorem VertexCutPathAutomorphism.component_single_substitution
    (E : Q.VertexCutPathAutomorphism k) {i j : Q.Vertex} (p : Q.Path i j) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i j (Finsupp.single p 1) =
      Q.pathArrowSubstitutionPath k (VertexCutPathAutomorphism.arrowReplacement Q k E) p := by
  induction p with
  | nil =>
    rw [pathArrowSubstitutionPath]
    exact (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_id
      E.val (VertexCutPathAutomorphism.fixes_vertex Q k E) i
  | @snoc j p a ha ih =>
    subst j
    have hp : Q.pathComp k (Q.pathIdentityArrowReplacement k a)
        (Finsupp.single p 1) = Finsupp.single (Path.snoc p a rfl) 1 := by
      simp [pathIdentityArrowReplacement, Q.pathComp_single, Path.comp]
    rw [← hp]
    have hE := (Q.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp
      E.val (VertexCutPathAutomorphism.fixes_vertex Q k E)
      (Finsupp.single p 1) (Q.pathIdentityArrowReplacement k a)
    change VertexCutPathAutomorphism.componentLinearEquiv Q k E _ _
      (Q.pathComp k (Q.pathIdentityArrowReplacement k a) (Finsupp.single p 1)) = _ at hE
    rw [hE]
    change Q.pathComp k (VertexCutPathAutomorphism.arrowReplacement Q k E a)
      (VertexCutPathAutomorphism.componentLinearEquiv Q k E _ _ (Finsupp.single p 1)) = _
    rw [ih]
    simp only [pathArrowSubstitutionPath]

theorem VertexCutPathAutomorphism.component_substitution
    (E : Q.VertexCutPathAutomorphism k) (i j : Q.Vertex)
    (f : Q.PathComponent k i j) :
    VertexCutPathAutomorphism.componentLinearEquiv Q k E i j f =
      Q.pathArrowSubstitutionComponent k
        (VertexCutPathAutomorphism.arrowReplacement Q k E) i j f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single p c =>
    have hs : Finsupp.single p c = c • Finsupp.single p (1 : k) := by simp
    rw [hs, map_smul, map_smul, VertexCutPathAutomorphism.component_single_substitution]
    simp

theorem VertexCutPathAutomorphism.substitution
    (E : Q.VertexCutPathAutomorphism k) :
    E.val.toAlgHom = Q.pathArrowSubstitution k
      (VertexCutPathAutomorphism.arrowReplacement Q k E) := by
  apply AlgHom.ext
  intro x
  funext i j
  change E.val x i j = Q.pathArrowSubstitution k
    (VertexCutPathAutomorphism.arrowReplacement Q k E) x i j
  rw [← VertexCutPathAutomorphism.componentLinearEquiv_projection Q k E,
    VertexCutPathAutomorphism.component_substitution]
  rfl

end ASGinzburg.CutQuiver
