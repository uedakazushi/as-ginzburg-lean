import ASGinzburg.GinzburgCutAugmentation
import ASGinzburg.JacobianUnrollingQuotient

/-! Genuine augmentation to the existing algebra A(Phi)'s components.
Regularity is exactly the quasi-isomorphism of these actual chain maps. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgUnrolledAugmentation (φ : Q.Potential k) (u v : Q.LiftVertex) :
    Q.ginzburgCutCochainComplex k φ u.1 v.1 (v.2-u.2) ⟶
      (HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of k ((Q.unrolledJacobianZAlgebra k φ).Hom (Q.height u) (Q.height v))) :=
  Q.ginzburgCutHomologyAugmentation k φ u.1 v.1 (v.2-u.2) ≫
    (HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℤ) 0).map
      (Q.ginzburgCutHomologyZeroUnrolledIso k φ u v).hom

theorem ginzburgUnrolledAugmentation_quasiIso_iff (φ : Q.Potential k) (u v : Q.LiftVertex) :
    QuasiIso (Q.ginzburgUnrolledAugmentation k φ u v) ↔
      ∀ q : ℤ, q<0 → IsZero (Q.ginzburgCutHomology k φ u.1 v.1 (v.2-u.2) q) := by
  rw [ginzburgUnrolledAugmentation,quasiIso_iff_comp_right]
  exact Q.ginzburgCutHomologyAugmentation_quasiIso_iff k φ u.1 v.1 (v.2-u.2)

theorem ginzburgRegular_iff_unrolledAugmentation_quasiIso (φ : Q.Potential k) :
    Q.GinzburgRegular k φ ↔ ∀ u v : Q.LiftVertex,
      QuasiIso (Q.ginzburgUnrolledAugmentation k φ u v) := by
  rw [Q.ginzburgRegular_iff_cutHomology]
  constructor
  · intro h u v
    exact (Q.ginzburgUnrolledAugmentation_quasiIso_iff k φ u v).mpr
      (h u.1 v.1 (v.2-u.2))
  · intro h u v c
    have h' := (Q.ginzburgUnrolledAugmentation_quasiIso_iff k φ (u,0) (v,c)).mp (h (u,0) (v,c))
    simpa only [sub_zero] using h'

end ASGinzburg.CutQuiver
