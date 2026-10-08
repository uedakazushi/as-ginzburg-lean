import ASGinzburg.GinzburgHomologyUnits
import ASGinzburg.PathJacobianRing
import ASGinzburg.FiniteComponentAlgebraEquiv
import ASGinzburg.GinzburgTotalHomologyZero

/-! The genuine component H-zero products form the full unital finite
quiver algebra, isomorphic to the actual Jacobian quotient algebra. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgHomologyComponentAlgebra (φ : Q.Potential k) :
    LinearComponentAlgebra k Q.Vertex where
  Hom i j := Q.ginzburgHomology k φ i j 0
  id := Q.ginzburgHomologyZeroId k φ
  comp := Q.ginzburgHomologyZeroComp k φ
  comp_id := Q.ginzburgHomologyZeroComp_id k φ
  id_comp := Q.id_ginzburgHomologyZeroComp k φ
  comp_assoc := Q.ginzburgHomologyZeroComp_assoc k φ

noncomputable abbrev GinzburgHomologyRing (φ : Q.Potential k) :=
  (Q.ginzburgHomologyComponentAlgebra k φ).Total

noncomputable def ginzburgHomologyJacobianComponentIsomorphism (φ : Q.Potential k) :
    LinearComponentAlgebra.Isomorphism (Q.ginzburgHomologyComponentAlgebra k φ)
      (Q.pathQuotientComponentAlgebra k (Q.pathJacobianIdeal k φ)) where
  map i j := (Q.ginzburgHomologyZeroJacobianIso k φ i j).toLinearEquiv
  map_id := Q.ginzburgHomologyZeroJacobianIso_id k φ
  map_comp := Q.ginzburgHomologyZeroJacobianIso_comp k φ

noncomputable def ginzburgHomologyJacobianAlgEquiv (φ : Q.Potential k) :
    Q.GinzburgHomologyRing k φ ≃ₐ[k] Q.PathJacobianRing k φ :=
  (Q.ginzburgHomologyJacobianComponentIsomorphism k φ).totalAlgEquiv

noncomputable def finiteComponentCurryEquiv (B : LinearComponentAlgebra k Q.Vertex) :
    (∀ uv : Q.Vertex×Q.Vertex, B.Hom uv.1 uv.2) ≃ₗ[k] B.Total where
  toFun f i j := f (i,j)
  invFun f uv := f uv.1 uv.2
  left_inv := by intro f; funext uv; rfl
  right_inv := by intro f; rfl
  map_add' := by intro f g; rfl
  map_smul' := by intro a f; rfl

noncomputable def ginzburgTotalHomologyZeroComponentRingIso (φ : Q.Potential k) :
    Q.ginzburgTotalHomology k φ 0 ≅ ModuleCat.of k (Q.GinzburgHomologyRing k φ) :=
  Q.ginzburgTotalHomologyComponentIso k φ 0 ≪≫
    ModuleCat.coprodIsoDirectSum _ ≪≫
      ((DirectSum.linearEquivFunOnFintype k (Q.Vertex×Q.Vertex)
        (fun uv => Q.ginzburgHomology k φ uv.1 uv.2 0)).trans
          (Q.finiteComponentCurryEquiv k (Q.ginzburgHomologyComponentAlgebra k φ))).toModuleIso

noncomputable def ginzburgTotalHomologyZeroJacobianRingIso (φ : Q.Potential k) :
    Q.ginzburgTotalHomology k φ 0 ≅ ModuleCat.of k (Q.PathJacobianRing k φ) :=
  Q.ginzburgTotalHomologyZeroComponentRingIso k φ ≪≫
    (Q.ginzburgHomologyJacobianAlgEquiv k φ).toLinearEquiv.toModuleIso

end ASGinzburg.CutQuiver
