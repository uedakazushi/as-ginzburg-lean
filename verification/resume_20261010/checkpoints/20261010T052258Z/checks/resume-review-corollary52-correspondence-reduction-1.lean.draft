import work.ASGinzburgDraft.TriangleQuadraticASClasses
import work.ASGinzburgDraft.TriangleTensorPathAutomorphismOrbits

/-! The actual Corollary 5.2 target reduces to the actual triangle
instance of Theorem 3.2, using the proved tensor/potential identification,
the proved quadratic-resolution comparison, and the proved GL/path
automorphism orbit comparison. The base correspondence remains an
explicit argument; this file does not assert its unproved truth. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k]

theorem regularTensorOrbitClass_eq_iff_potentialPathClass
    (w w' : GinzburgRegularTensor333 k) :
    w.orbitClass k = w'.orbitClass k ↔
      (ginzburgRegularTensorPotentialEquiv333 k w).pathAutomorphismClass k triangle333 =
        (ginzburgRegularTensorPotentialEquiv333 k w').pathAutomorphismClass k triangle333 := by
  rw [GinzburgRegularTensor333.orbitClass_eq_iff,
    GinzburgRegularPotential.pathAutomorphismClass_eq_iff_smul]
  exact triangleTensor_orbit_iff_pathAutomorphism k w.val w'.val

theorem corollary52ClassStatement_iff_triangleClassCorrespondence :
    Corollary52ClassStatement k ↔
      (∀ φ ψ : GinzburgRegularPotential k triangle333,
        φ.pathAutomorphismClass k triangle333 = ψ.pathAutomorphismClass k triangle333 ↔
          φ.asIsomorphismClass k triangle333 = ψ.asIsomorphismClass k triangle333) := by
  constructor
  · intro h φ ψ
    let w := (ginzburgRegularTensorPotentialEquiv333 k).symm φ
    let w' := (ginzburgRegularTensorPotentialEquiv333 k).symm ψ
    have hw := h w w'
    rw [regularTensorOrbitClass_eq_iff_potentialPathClass,
      regularTensorQuadraticClass_eq_iff_potentialASClass] at hw
    simpa only [w, w', Equiv.apply_symm_apply] using hw
  · intro h w w'
    rw [regularTensorOrbitClass_eq_iff_potentialPathClass,
      regularTensorQuadraticClass_eq_iff_potentialASClass]
    exact h _ _

theorem corollary52Statement_iff_triangleCorrespondence :
    Corollary52Statement.{u,v} k ↔
      ASGinzburgCorrespondenceStatement.{u,v} k triangle333 := by
  constructor
  · intro h
    apply (asGinzburgCorrespondenceStatement_iff k triangle333).mpr
    exact ⟨(corollary52ClassStatement_iff_triangleClassCorrespondence k).mp h.1,
      (corollary52TensorRecovery_iff_asGinzburgRecovery k).mp h.2⟩
  · intro h
    obtain ⟨hC,hR⟩ := (asGinzburgCorrespondenceStatement_iff k triangle333).mp h
    exact ⟨(corollary52ClassStatement_iff_triangleClassCorrespondence k).mpr hC,
      (corollary52TensorRecovery_iff_asGinzburgRecovery k).mpr hR⟩

theorem corollary52Statement_of_triangleCorrespondence
    (h : ASGinzburgCorrespondenceStatement.{u,v} k triangle333) :
    Corollary52Statement.{u,v} k :=
  (corollary52Statement_iff_triangleCorrespondence k).mpr h

noncomputable def corollary52ClassEquiv_of_triangleCorrespondence
    (h : ASGinzburgCorrespondenceStatement.{u,u} k triangle333) :
    GinzburgRegularTensorOrbit333 k ≃ QuadraticASIsomorphismClass.{u,u} k :=
  corollary52ClassEquiv k (corollary52Statement_of_triangleCorrespondence k h)

end ASGinzburg
