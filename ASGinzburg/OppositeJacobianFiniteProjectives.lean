import ASGinzburg.OppositeJacobianSimpleModules
import ASGinzburg.FiniteProjectiveClosure

/-! The actual left/right equivalence preserves the existing finitely
generated projectives in both directions by finite sums and retracts. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

noncomputable def oppositeJacobianRightRepresentableInverseAtIso (j : ℤ) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).inverse.obj
      ((Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).representable j) ≅
        (Q.unrolledJacobianZAlgebra k φ).leftRepresentable ((Q.vertices : ℤ)-1-j) := by
  let B := Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)
  have hj : j = (Q.vertices : ℤ)-1-((Q.vertices : ℤ)-1-j) := by ring
  exact (Q.oppositeJacobianLeftRightEquivalence k φ).inverse.mapIso
    (eqToIso (congrArg B.representable hj)) ≪≫
    Q.oppositeJacobianRightRepresentableInverseIso k φ ((Q.vertices : ℤ)-1-j)

noncomputable def oppositeJacobianLeftFiniteSumIso (n : ℕ) (i : Fin n → ℤ) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).functor.obj
      (∐ fun a => (Q.unrolledJacobianZAlgebra k φ).leftRepresentable (i a)) ≅
        ∐ fun a => (Q.opposite.unrolledJacobianZAlgebra k
          (Q.oppositePotentialEquiv k φ)).representable ((Q.vertices : ℤ)-1-i a) :=
  PreservesCoproduct.iso (Q.oppositeJacobianLeftRightEquivalence k φ).functor _ ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso (fun a : Discrete (Fin n) =>
      Q.oppositeJacobianLeftRepresentableIso k φ (i a.as)))

noncomputable def oppositeJacobianRightFiniteSumInverseIso (n : ℕ) (i : Fin n → ℤ) :
    (Q.oppositeJacobianLeftRightEquivalence k φ).inverse.obj
      (∐ fun a => (Q.opposite.unrolledJacobianZAlgebra k
        (Q.oppositePotentialEquiv k φ)).representable (i a)) ≅
        ∐ fun a => (Q.unrolledJacobianZAlgebra k φ).leftRepresentable
          ((Q.vertices : ℤ)-1-i a) :=
  PreservesCoproduct.iso (Q.oppositeJacobianLeftRightEquivalence k φ).inverse _ ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso (fun a : Discrete (Fin n) =>
      Q.oppositeJacobianRightRepresentableInverseAtIso k φ (i a.as)))

theorem oppositeJacobianLeftFiniteProjective {P : (Q.unrolledJacobianZAlgebra k φ).LeftModule}
    (hP : (Q.unrolledJacobianZAlgebra k φ).leftFiniteProjectiveProperty P) :
    (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).rightFiniteProjectiveProperty
      ((Q.oppositeJacobianLeftRightEquivalence k φ).functor.obj P) := by
  obtain ⟨n,i,⟨r⟩⟩ := hP
  refine ⟨n, (fun a => (Q.vertices : ℤ)-1-i a), ⟨?_⟩⟩
  exact (r.map (Q.oppositeJacobianLeftRightEquivalence k φ).functor).trans
    (Retract.ofIso (Q.oppositeJacobianLeftFiniteSumIso k φ n i))

theorem oppositeJacobianRightFiniteProjective
    {P : (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).RightModule}
    (hP : (Q.opposite.unrolledJacobianZAlgebra k
      (Q.oppositePotentialEquiv k φ)).rightFiniteProjectiveProperty P) :
    (Q.unrolledJacobianZAlgebra k φ).leftFiniteProjectiveProperty
      ((Q.oppositeJacobianLeftRightEquivalence k φ).inverse.obj P) := by
  obtain ⟨n,i,⟨r⟩⟩ := hP
  refine ⟨n, (fun a => (Q.vertices : ℤ)-1-i a), ⟨?_⟩⟩
  exact (r.map (Q.oppositeJacobianLeftRightEquivalence k φ).inverse).trans
    (Retract.ofIso (Q.oppositeJacobianRightFiniteSumInverseIso k φ n i))

end ASGinzburg.CutQuiver
