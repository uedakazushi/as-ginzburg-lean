import ASGinzburg.PathCutGrading
import ASGinzburg.GinzburgCutCochainComplex
import ASGinzburg.GinzburgBoundaryProducts

/-! The genuine cut-c degree-zero extended paths are precisely the
ordinary paths of cut degree c, as finite-dimensional vector spaces. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def originalGinzburgCutDegreeZeroMap (u v : Q.Vertex) (c : ℤ) :
    Q.pathCutComponent k u v c →ₗ[k] Q.ginzburgCutCohomologicalComponent k u v 0 c :=
  ((Q.originalGinzburgLinearMap k u v).comp
    (Q.pathCutComponent k u v c).subtype).codRestrict _ (fun f =>
      ⟨Q.originalGinzburgLinearMap_degreeZero k f.val,
        Q.originalGinzburgLinearMap_cut k f.property⟩)

theorem originalGinzburgCutDegreeZeroMap_bijective (u v : Q.Vertex) (c : ℤ) :
    Function.Bijective (Q.originalGinzburgCutDegreeZeroMap k u v c) := by
  constructor
  · intro f g h
    apply Subtype.ext
    apply Q.originalGinzburgLinearMap_injective k u v
    exact congrArg (fun f : Q.ginzburgCutCohomologicalComponent k u v 0 c => f.val) h
  · intro f
    let g := (Q.originalGinzburgDegreeZeroEquiv k u v).symm ⟨f.val,f.property.1⟩
    have hg : Q.originalGinzburgLinearMap k u v g=f.val := by
      rw [←Q.originalGinzburgDegreeZeroEquiv_coe k]
      change ((Q.originalGinzburgDegreeZeroEquiv k u v)
        ((Q.originalGinzburgDegreeZeroEquiv k u v).symm _)).val=_
      rw [LinearEquiv.apply_symm_apply]
    have hc : g ∈ Q.pathCutComponent k u v c := by
      apply (Q.originalGinzburgLinearMap_cut_iff k c g).mp
      rw [hg]
      exact f.property.2
    exact ⟨⟨g,hc⟩,Subtype.ext hg⟩

noncomputable def originalGinzburgCutDegreeZeroEquiv (u v : Q.Vertex) (c : ℤ) :
    Q.pathCutComponent k u v c ≃ₗ[k] Q.ginzburgCutCohomologicalComponent k u v 0 c :=
  LinearEquiv.ofBijective (Q.originalGinzburgCutDegreeZeroMap k u v c)
    (Q.originalGinzburgCutDegreeZeroMap_bijective k u v c)

theorem originalGinzburgCutDegreeZeroEquiv_coe (u v : Q.Vertex) (c : ℤ)
    (f : Q.pathCutComponent k u v c) :
    (Q.originalGinzburgCutDegreeZeroEquiv k u v c f).val=
      Q.originalGinzburgLinearMap k u v f.val := rfl

theorem originalGinzburgCutDegreeZeroEquiv_symm_coe (u v : Q.Vertex) (c : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k u v 0 c) :
    Q.originalGinzburgLinearMap k u v
      ((Q.originalGinzburgCutDegreeZeroEquiv k u v c).symm f).val=f.val := by
  rw [←Q.originalGinzburgCutDegreeZeroEquiv_coe k]
  rw [LinearEquiv.apply_symm_apply]

end ASGinzburg.CutQuiver
