import work.ASGinzburgDraft.TriangleGinzburgGLCochainInvariance
import ASGinzburg.Corollary52Statement
import ASGinzburg.PotentialPathAutomorphismOrbitComparison

/-! The proved actual cochain invariance restricts the genuine GL and
path-automorphism actions to Ginzburg-regular tensors and potentials.
Their actual orbit relations agree with the existing source setoids. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable instance triangleRegularTensorMulAction :
    MulAction (TriangleGL333 k) (GinzburgRegularTensor333 k) where
  smul g w := ⟨g • w.val, (triangleTensorGinzburgRegular_GL_iff k g w.val).mp w.property⟩
  one_smul w := Subtype.ext (one_smul (TriangleGL333 k) w.val)
  mul_smul g h w := Subtype.ext (mul_smul g h w.val)

@[simp] theorem triangleRegularTensor_smul_val (g : TriangleGL333 k)
    (w : GinzburgRegularTensor333 k) : (g • w).val = g • w.val := rfl

theorem ginzburgRegularTensorSetoid333_eq_orbitRel :
    ginzburgRegularTensorSetoid333 k =
      MulAction.orbitRel (TriangleGL333 k) (GinzburgRegularTensor333 k) := by
  apply Setoid.ext
  intro w w'
  change w.val ∈ MulAction.orbit (TriangleGL333 k) w'.val ↔
    w ∈ MulAction.orbit (TriangleGL333 k) w'
  rw [MulAction.mem_orbit_iff,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g,Subtype.ext hg⟩
  · rintro ⟨g,hg⟩
    exact ⟨g,congrArg Subtype.val hg⟩

noncomputable instance triangleRegularPotentialMulAction :
    MulAction (triangle333.VertexCutPathAutomorphism k)
      (GinzburgRegularPotential k triangle333) where
  smul E φ := ⟨CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k E φ.val,
    (triangleGinzburgRegular_pathAutomorphism_iff k E φ.val).mp φ.property⟩
  one_smul φ := Subtype.ext (congrArg (fun E : triangle333.Potential k ≃ₗ[k]
    triangle333.Potential k => E φ.val) (triangle333.vertexCutPotentialAutomorphismHom k).map_one)
  mul_smul E F φ := Subtype.ext (congrArg (fun E : triangle333.Potential k ≃ₗ[k]
    triangle333.Potential k => E φ.val)
      ((triangle333.vertexCutPotentialAutomorphismHom k).map_mul E F))

@[simp] theorem triangleRegularPotential_smul_val
    (E : triangle333.VertexCutPathAutomorphism k)
    (φ : GinzburgRegularPotential k triangle333) :
    (E • φ).val = CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k E φ.val := rfl

theorem ginzburgRegularPotentialPathAutomorphismSetoid_triangle_eq_orbitRel :
    ginzburgRegularPotentialPathAutomorphismSetoid k triangle333 =
      MulAction.orbitRel (triangle333.VertexCutPathAutomorphism k)
        (GinzburgRegularPotential k triangle333) := by
  apply Setoid.ext
  intro φ ψ
  change (triangle333.potentialPathAutomorphismSetoid k).r φ.val ψ.val ↔
    φ ∈ MulAction.orbit (triangle333.VertexCutPathAutomorphism k) ψ
  rw [triangle333.potentialPathAutomorphismSetoid_eq_orbitRel k]
  change φ.val ∈ MulAction.orbit (triangle333.VertexCutPathAutomorphism k) ψ.val ↔ _
  rw [MulAction.mem_orbit_iff,MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨E,hE⟩
    exact ⟨E,Subtype.ext hE⟩
  · rintro ⟨E,hE⟩
    exact ⟨E,congrArg Subtype.val hE⟩

end ASGinzburg
