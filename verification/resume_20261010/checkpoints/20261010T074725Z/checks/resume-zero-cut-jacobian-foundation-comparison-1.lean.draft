import work.ASGinzburgDraft.ZeroCutJacobianIsomorphismPathLift
import work.ASGinzburgDraft.ZeroCutJacobianContextGeneration

/-! For every original potential, its genuine noncut Jacobian ring is
the actual foundation of its unrolled Jacobian Z-algebra. The kernel is
proved to be the two-sided ideal of the actual cut derivatives. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem zeroCutJacobianFoundationAlgHom_surjective (φ : Q.Potential k) :
    Function.Surjective (Q.zeroCutJacobianFoundationAlgHom k φ) := by
  classical
  intro x
  refine ⟨fun i j => (Q.zeroCutJacobianComponentProjection_surjective k φ i j (x i j)).choose,?_⟩
  funext i j
  exact (Q.zeroCutJacobianComponentProjection_surjective k φ i j (x i j)).choose_spec

theorem zeroCutJacobianGenerator_evaluation_zero (φ : Q.Potential k)
    (b : {a : Q.Arrow // Q.cut a = true}) :
    Q.zeroCutJacobianFoundationAlgHom k φ
      ((Q.zeroCutPathComponentAlgebra k).totalComponent (Q.target b.val) (Q.source b.val)
        (Q.zeroCutCyclicDerivative k φ b)) = 0 := by
  classical
  have hz : Q.zeroCutJacobianComponentProjection k φ (Q.target b.val) (Q.source b.val)
      (Q.zeroCutCyclicDerivative k φ b) = 0 :=
    (Q.zeroCutJacobianComponentProjection_eq_zero_iff k φ _ _ _).mpr
      (Q.pathCyclicDerivative_mem_pathJacobianIdeal k φ b.val)
  funext i j
  change Q.zeroCutJacobianComponentProjection k φ i j
    ((Q.zeroCutPathComponentAlgebra k).totalComponent (Q.target b.val) (Q.source b.val)
      (Q.zeroCutCyclicDerivative k φ b) i j) = 0
  by_cases hi : i = Q.target b.val
  · subst i
    by_cases hj : j = Q.source b.val
    · subst j
      rw [LinearComponentAlgebra.totalComponent_apply_same]
      exact hz
    · simp [LinearComponentAlgebra.totalComponent,hj]
  · rw [LinearComponentAlgebra.totalComponent_apply_source_ne _ _ _ _ _ _ hi,map_zero]

theorem zeroCutJacobianIdeal_le_foundationKernel (φ : Q.Potential k) :
    Q.zeroCutJacobianIdeal k φ ≤
      RingHom.ker (Q.zeroCutJacobianFoundationAlgHom k φ).toRingHom := by
  have H : TwoSidedIdeal.span (Q.zeroCutJacobianGenerators k φ) ≤
      (RingHom.ker (Q.zeroCutJacobianFoundationAlgHom k φ).toRingHom).toTwoSided := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨b,rfl⟩
    apply Ideal.mem_toTwoSided.mpr
    exact Q.zeroCutJacobianGenerator_evaluation_zero k φ b
  simpa only [Ideal.asIdeal_toTwoSided] using TwoSidedIdeal.asIdeal.monotone H

theorem zeroCutJacobianFoundationKernel_le_ideal (φ : Q.Potential k) :
    RingHom.ker (Q.zeroCutJacobianFoundationAlgHom k φ).toRingHom ≤
      Q.zeroCutJacobianIdeal k φ := by
  intro x hx
  change Q.zeroCutJacobianFoundationAlgHom k φ x = 0 at hx
  have hc : ∀ i j : Q.Vertex,
      (Q.zeroCutPathComponentAlgebra k).totalComponent i j (x i j) ∈ Q.zeroCutJacobianIdeal k φ := by
    intro i j
    apply Q.zeroCutJacobianComponent_embedding_mem k φ i j (x i j)
    apply (Q.zeroCutJacobianComponentProjection_eq_zero_iff k φ i j (x i j)).mp
    exact congrFun (congrFun hx i) j
  rw [← (Q.zeroCutPathComponentAlgebra k).sum_totalComponent x]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact hc i j

theorem zeroCutJacobianIdeal_eq_foundationKernel (φ : Q.Potential k) :
    Q.zeroCutJacobianIdeal k φ =
      RingHom.ker (Q.zeroCutJacobianFoundationAlgHom k φ).toRingHom :=
  le_antisymm (Q.zeroCutJacobianIdeal_le_foundationKernel k φ)
    (Q.zeroCutJacobianFoundationKernel_le_ideal k φ)

noncomputable def zeroCutJacobianFoundationAlgEquiv (φ : Q.Potential k) :
    Q.ZeroCutJacobianRing k φ ≃ₐ[k] (Q.unrolledJacobianZAlgebra k φ).FoundationAlgebra Q :=
  (Ideal.quotientEquivAlgOfEq k (Q.zeroCutJacobianIdeal_eq_foundationKernel k φ)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (Q.zeroCutJacobianFoundationAlgHom_surjective k φ))

theorem zeroCutJacobianFoundationAlgEquiv_apply_mk (φ : Q.Potential k) (x : Q.ZeroCutPathRing k) :
    Q.zeroCutJacobianFoundationAlgEquiv k φ (Ideal.Quotient.mk (Q.zeroCutJacobianIdeal k φ) x) =
      Q.zeroCutJacobianFoundationAlgHom k φ x := by
  rw [zeroCutJacobianFoundationAlgEquiv,AlgEquiv.trans_apply,Ideal.quotientEquivAlgOfEq_mk]
  rfl

end ASGinzburg.CutQuiver
