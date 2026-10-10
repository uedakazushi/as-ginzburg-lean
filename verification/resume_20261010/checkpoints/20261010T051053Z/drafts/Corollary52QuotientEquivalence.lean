import work.ASGinzburgDraft.Corollary52Statement
import work.ASGinzburgDraft.ASGinzburgCorrespondenceStatement

/-! Genuine quotient consequences of the explicitly stated source
correspondence. No recovery or orbit-identification obligation is silently
assumed: the class equivalence below takes Corollary52Statement itself as
its displayed argument. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k]

noncomputable def ginzburgRegularTensorPotentialEquiv333 :
    GinzburgRegularTensor333 k ≃ GinzburgRegularPotential k triangle333 where
  toFun w := ⟨triangleTensorPotentialEquiv k w.val, w.property⟩
  invFun φ := ⟨(triangleTensorPotentialEquiv k).symm φ.val, by
    change triangle333.GinzburgRegular k
      (triangleTensorPotentialEquiv k ((triangleTensorPotentialEquiv k).symm φ.val))
    rw [LinearEquiv.apply_symm_apply]
    exact φ.property⟩
  left_inv w := Subtype.ext ((triangleTensorPotentialEquiv k).symm_apply_apply w.val)
  right_inv φ := Subtype.ext ((triangleTensorPotentialEquiv k).apply_symm_apply φ.val)

theorem corollary52TensorRecovery_iff_asGinzburgRecovery :
    Corollary52TensorRecoveryStatement.{u,v} k ↔
      ASGinzburgRegularPotentialRecoveryStatement.{u,v} k triangle333 := by
  constructor
  · intro h A hA
    obtain ⟨w,hw⟩ := h A ((A.quadraticASRegular_iff_triangleASRegular).mpr hA)
    exact ⟨ginzburgRegularTensorPotentialEquiv333 k w, hw⟩
  · intro h A hA
    obtain ⟨φ,hφ⟩ := h A ((A.quadraticASRegular_iff_triangleASRegular).mp hA)
    refine ⟨(ginzburgRegularTensorPotentialEquiv333 k).symm φ, ?_⟩
    change Nonempty (ZAlgebra.Isomorphism A
      (triangle333.unrolledJacobianZAlgebra k
        (triangleTensorPotentialEquiv k ((triangleTensorPotentialEquiv k).symm φ.val))))
    rw [LinearEquiv.apply_symm_apply]
    exact hφ

noncomputable def corollary52ClassMap (h : Corollary52ClassStatement k) :
    GinzburgRegularTensorOrbit333 k → QuadraticASIsomorphismClass.{u,u} k :=
  Quotient.lift (GinzburgRegularTensor333.asQuadraticASClass k) (by
    intro w w' hw
    exact (h w w').mp (Quotient.sound hw))

theorem corollary52ClassMap_injective (h : Corollary52ClassStatement k) :
    Function.Injective (corollary52ClassMap k h) := by
  intro c c'
  refine Quotient.inductionOn₂ c c' ?_
  intro w w' hw
  exact (h w w').mpr hw

theorem corollary52ClassMap_surjective (h : Corollary52Statement.{u,u} k) :
    Function.Surjective (corollary52ClassMap k h.1) := by
  intro C
  refine Quotient.inductionOn C ?_
  intro A
  obtain ⟨w,⟨E⟩⟩ := h.2 A.val A.property
  exact ⟨w.orbitClass k, Quotient.sound ⟨E.symm⟩⟩

noncomputable def corollary52ClassEquiv (h : Corollary52Statement.{u,u} k) :
    GinzburgRegularTensorOrbit333 k ≃ QuadraticASIsomorphismClass.{u,u} k :=
  Equiv.ofBijective (corollary52ClassMap k h.1)
    ⟨corollary52ClassMap_injective k h.1, corollary52ClassMap_surjective k h⟩

theorem corollary52ClassEquiv_apply (h : Corollary52Statement.{u,u} k)
    (w : GinzburgRegularTensor333 k) :
    corollary52ClassEquiv k h (w.orbitClass k) = w.asQuadraticASClass k := rfl

end ASGinzburg
