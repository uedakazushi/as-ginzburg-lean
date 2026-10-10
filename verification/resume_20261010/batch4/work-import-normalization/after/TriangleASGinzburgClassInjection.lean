import work.ASGinzburgDraft.TriangleGinzburgJacobianIsomorphismOrbits
import ASGinzburg.PathAutomorphismJacobianDescent
import ASGinzburg.Corollary52CorrespondenceReduction

/-! The genuine triangle class correspondence follows from actual
Jacobian isomorphisms and the original two Ginzburg regularity conditions.
This proves the class assertion of Corollary 5.2. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleGinzburgRegular_pathClass_iff_JacobianIso
    (φ ψ : triangle333.Potential k)
    (hGφ : triangle333.GinzburgRegular k φ) (hGψ : triangle333.GinzburgRegular k ψ) :
    triangle333.potentialPathAutomorphismClass k φ =
        triangle333.potentialPathAutomorphismClass k ψ ↔
      Nonempty (ZAlgebra.Isomorphism (triangle333.unrolledJacobianZAlgebra k φ)
        (triangle333.unrolledJacobianZAlgebra k ψ)) := by
  constructor
  · exact triangle333.unrolledJacobian_isomorphism_of_potentialPathClass k φ ψ
  · rintro ⟨F⟩
    apply (triangle333.potentialPathAutomorphismClass_eq_iff_smul k φ ψ).mpr
    exact triangleGinzburgRegular_JacobianIso_pathAutomorphism k φ ψ F hGφ hGψ

theorem triangleASGinzburgClassInjection : ASGinzburgClassInjectionStatement k triangle333 := by
  intro φ ψ h
  obtain ⟨F⟩ := (GinzburgRegularPotential.asIsomorphismClass_eq_iff k triangle333 φ ψ).mp h
  apply (GinzburgRegularPotential.pathAutomorphismClass_eq_iff_smul k triangle333 φ ψ).mpr
  exact triangleGinzburgRegular_JacobianIso_pathAutomorphism k φ.val ψ.val F φ.property ψ.property

theorem triangleASGinzburgClassIff (φ ψ : GinzburgRegularPotential k triangle333) :
    φ.pathAutomorphismClass k triangle333 = ψ.pathAutomorphismClass k triangle333 ↔
      φ.asIsomorphismClass k triangle333 = ψ.asIsomorphismClass k triangle333 :=
  ⟨asGinzburgClassDescent k triangle333 φ ψ,triangleASGinzburgClassInjection k φ ψ⟩

theorem triangleGinzburgRegularPotentialASClassMap_injective :
    Function.Injective (ginzburgRegularPotentialASClassMap k triangle333) := by
  intro C D
  refine Quotient.inductionOn₂ C D ?_
  intro φ ψ h
  change φ.asIsomorphismClass k triangle333 = ψ.asIsomorphismClass k triangle333 at h
  exact triangleASGinzburgClassInjection k φ ψ h

theorem corollary52Class : Corollary52ClassStatement k :=
  (corollary52ClassStatement_iff_triangleClassCorrespondence k).mpr
    (triangleASGinzburgClassIff k)

theorem corollary52ClassMap_triangle_injective :
    Function.Injective (corollary52ClassMap k (corollary52Class k)) :=
  corollary52ClassMap_injective k (corollary52Class k)

end ASGinzburg
