import work.ASGinzburgDraft.GeneratedMinimalRelationClasses
import ASGinzburg.UnrolledJacobianAlgebra
import ASGinzburg.FoundationSurvivingArrows

/-! On sheet zero, the actual Jacobian generators are exactly the cut
derivatives, and their classes span the genuine minimal relation space. -/
namespace ASGinzburg.CutQuiver
open ZAlgebra
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def foundationCutDerivativeGenerator (φ : Q.Potential k)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    Q.jacobianGenerators k φ (i.val : ℤ) (j.val : ℤ) := by
  let hi : Q.height (Q.target a.val, (0 : ℤ)) = (i.val : ℤ) := by
    simp only [a.property.2.1, height, mul_zero, add_zero]
  let hj : Q.height (Q.source a.val, (0 : ℤ) + ((1-Q.cutDegree a.val : ℕ) : ℤ)) =
      (j.val : ℤ) := by
    simp only [a.property.1, Q.cutDegree_true a.property.2.2, Nat.sub_self,
      Nat.cast_zero, add_zero, height, mul_zero]
  exact ⟨(Q.unrolledPathZAlgebra k).homTransport _ _ _ _ hi hj
    (Q.integerJacobianRelation k a.val φ 0), a.val, 0, hi, hj, rfl⟩

theorem foundationCutDerivativeGenerator_surjective (φ : Q.Potential k)
    (i j : Q.Vertex) : Function.Surjective (Q.foundationCutDerivativeGenerator k φ i j) := by
  rintro ⟨f, a, m, hi, hj, heq⟩
  have hi' : (Q.target a, m) = (i, (0 : ℤ)) :=
    Q.height_bijective.injective (by simpa only [height, mul_zero, add_zero] using hi)
  have hj' : (Q.source a, m + ((1-Q.cutDegree a : ℕ) : ℤ)) = (j, (0 : ℤ)) :=
    Q.height_bijective.injective (by simpa only [height, mul_zero, add_zero] using hj)
  have hm : m = 0 := congrArg Prod.snd hi'
  subst m
  have hc : Q.cut a = true := by
    have hd := congrArg Prod.snd hj'
    cases h : Q.cut a
    · simp [cutDegree, h] at hd
    · rfl
  refine ⟨⟨a, congrArg Prod.fst hj', congrArg Prod.fst hi', hc⟩, ?_⟩
  apply Subtype.ext
  exact heq

noncomputable def foundationMinimalCutDerivativeClass (φ : Q.Potential k)
    (i j : Q.Vertex) (a : Q.FoundationRelationArrow i j) :
    Q.MinimalRelationComponent (Q.unrolledJacobianIdeal k φ) (i.val : ℤ) (j.val : ℤ) :=
  Q.generatedMinimalRelationClass k (Q.jacobianGenerators k φ) _ _
    (Q.foundationCutDerivativeGenerator k φ i j a)

set_option synthInstance.maxHeartbeats 200000 in
theorem foundationMinimalCutDerivativeClass_span (φ : Q.Potential k) (i j : Q.Vertex) :
    Submodule.span k (Set.range (Q.foundationMinimalCutDerivativeClass k φ i j)) = ⊤ := by
  have hr : Set.range (Q.foundationMinimalCutDerivativeClass k φ i j) =
      Set.range (Q.generatedMinimalRelationClass k (Q.jacobianGenerators k φ)
        (i.val : ℤ) (j.val : ℤ)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Q.foundationCutDerivativeGenerator k φ i j a, rfl⟩
    · rintro ⟨s, rfl⟩
      obtain ⟨a, rfl⟩ := Q.foundationCutDerivativeGenerator_surjective k φ i j s
      exact ⟨a, rfl⟩
  rw [hr]
  exact Q.generatedMinimalRelationClass_span k (Q.jacobianGenerators k φ) _ _

end ASGinzburg.CutQuiver
