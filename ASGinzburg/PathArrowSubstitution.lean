import ASGinzburg.PathJacobianRing
import ASGinzburg.FiniteComponentAlgebraMaps
import ASGinzburg.FiniteComponentMapEmbeddings

/-! Replacing each actual arrow by a finite linear combination of actual
paths with the same endpoints extends to a genuine path-algebra map. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

abbrev PathArrowReplacement :=
  ∀ a : Q.Arrow, Q.PathComponent k (Q.source a) (Q.target a)

noncomputable def pathArrowSubstitutionPath (σ : Q.PathArrowReplacement k) :
    {i j : Q.Vertex} → Q.Path i j → Q.PathComponent k i j
  | _,_,.nil i => Q.pathId k i
  | _,_,.snoc p a h => Q.pathComp k (h ▸ σ a) (pathArrowSubstitutionPath σ p)

theorem pathArrowSubstitutionPath_comp (σ : Q.PathArrowReplacement k)
    {i j l : Q.Vertex} (p : Q.Path i j) (q : Q.Path j l) :
    Q.pathArrowSubstitutionPath k σ (p.comp q) =
      Q.pathComp k (Q.pathArrowSubstitutionPath k σ q)
        (Q.pathArrowSubstitutionPath k σ p) := by
  induction q with
  | nil => simp only [Path.comp_nil,pathArrowSubstitutionPath,Q.pathComp_id]
  | @snoc j q a h ih =>
    subst j
    simp only [Path.comp,pathArrowSubstitutionPath,ih,Q.pathComp_assoc]

noncomputable def pathArrowSubstitutionComponent (σ : Q.PathArrowReplacement k)
    (i j : Q.Vertex) : Q.PathComponent k i j →ₗ[k] Q.PathComponent k i j :=
  Finsupp.linearCombination k (Q.pathArrowSubstitutionPath k σ)

@[simp] theorem pathArrowSubstitutionComponent_single (σ : Q.PathArrowReplacement k)
    {i j : Q.Vertex} (p : Q.Path i j) (c : k) :
    Q.pathArrowSubstitutionComponent k σ i j (Finsupp.single p c) =
      c • Q.pathArrowSubstitutionPath k σ p := by
  simp [pathArrowSubstitutionComponent]

theorem pathArrowSubstitutionComponent_id (σ : Q.PathArrowReplacement k) (i : Q.Vertex) :
    Q.pathArrowSubstitutionComponent k σ i i (Q.pathId k i) = Q.pathId k i := by
  simp [pathId,pathArrowSubstitutionPath]

theorem pathArrowSubstitutionComponent_comp (σ : Q.PathArrowReplacement k)
    {i j l : Q.Vertex} (f : Q.PathComponent k i j) (g : Q.PathComponent k j l) :
    Q.pathArrowSubstitutionComponent k σ i l (Q.pathComp k g f) =
      Q.pathComp k (Q.pathArrowSubstitutionComponent k σ j l g)
        (Q.pathArrowSubstitutionComponent k σ i j f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' ih ih' => simp [map_add,ih,ih']
  | single p a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' => simp [map_add,LinearMap.add_apply,ih,ih']
    | single q b =>
      simp [Q.pathArrowSubstitutionPath_comp,map_smul,LinearMap.smul_apply,smul_smul,mul_comm]

noncomputable def pathArrowSubstitution (σ : Q.PathArrowReplacement k) :
    Q.PathRing k →ₐ[k] Q.PathRing k :=
  (Q.pathComponentAlgebra k).totalAlgHomOfComponents (Q.pathComponentAlgebra k)
    (Q.pathArrowSubstitutionComponent k σ)
    (Q.pathArrowSubstitutionComponent_id k σ)
    (Q.pathArrowSubstitutionComponent_comp k σ)

theorem pathArrowSubstitution_apply (σ : Q.PathArrowReplacement k)
    (x : Q.PathRing k) (i j : Q.Vertex) :
    Q.pathArrowSubstitution k σ x i j = Q.pathArrowSubstitutionComponent k σ i j (x i j) := rfl

theorem pathArrowSubstitution_component (σ : Q.PathArrowReplacement k)
    (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    Q.pathArrowSubstitution k σ ((Q.pathComponentAlgebra k).totalComponent i j f) =
      (Q.pathComponentAlgebra k).totalComponent i j
        (Q.pathArrowSubstitutionComponent k σ i j f) :=
  (Q.pathComponentAlgebra k).totalLinearMapOfComponents_component (Q.pathComponentAlgebra k)
    (Q.pathArrowSubstitutionComponent k σ) i j f

theorem pathArrowSubstitution_arrow (σ : Q.PathArrowReplacement k) (a : Q.Arrow) :
    Q.pathArrowSubstitutionComponent k σ (Q.source a) (Q.target a)
      (Finsupp.single (Path.snoc (.nil (Q.source a)) a rfl) 1) = σ a := by
  simp [pathArrowSubstitutionPath,Q.id_pathComp]

end ASGinzburg.CutQuiver
