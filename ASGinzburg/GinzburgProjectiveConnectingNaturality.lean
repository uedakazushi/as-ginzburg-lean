import ASGinzburg.GinzburgProjectiveConnectingComponents
import ASGinzburg.GinzburgCutZeroClassSurjectivity

/-! The actual connecting components commute with every element of A(Phi),
by choosing a genuine degree-zero Ginzburg representative. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgLoopDualProjectiveComponent_algebra_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (a : (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height y)) :
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-2)).obj.map
        (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from a).op ≫
        Q.ginzburgLoopDualProjectiveComponent k φ x v =
      Q.ginzburgLoopDualProjectiveComponent k φ y v ≫
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1)).obj.map
          (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from a).op := by
  obtain ⟨f,rfl⟩ := Q.ginzburgCutZeroUnrolledClass_surjective k φ x y a
  exact Q.ginzburgLoopDualProjectiveComponent_left_naturality k φ f

theorem ginzburgDualOriginalProjectiveComponent_algebra_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (a : (Q.unrolledJacobianZAlgebra k φ).Hom (Q.height x) (Q.height y)) :
    ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v (-1)).obj.map
        (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from a).op ≫
        Q.ginzburgDualOriginalProjectiveComponent k φ x v =
      Q.ginzburgDualOriginalProjectiveComponent k φ y v ≫
        ((Q.unrolledJacobianZAlgebra k φ).ginzburgGeneratorCoefficientModule Q v 0).obj.map
          (show (⟨Q.height x⟩ : (Q.unrolledJacobianZAlgebra k φ).Obj) ⟶ ⟨Q.height y⟩ from a).op := by
  obtain ⟨f,rfl⟩ := Q.ginzburgCutZeroUnrolledClass_surjective k φ x y a
  exact Q.ginzburgDualOriginalProjectiveComponent_left_naturality k φ f

end ASGinzburg.CutQuiver
