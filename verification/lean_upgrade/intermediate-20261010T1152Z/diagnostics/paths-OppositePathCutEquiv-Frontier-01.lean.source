import ASGinzburg.OppositePathAlgebra
import ASGinzburg.PathCutGrading
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Genuine cut-homogeneous path components are preserved by reflection. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem oppositePathComponentEquiv_toLinearMap (u v : Q.Vertex) :
    (Q.oppositePathComponentEquiv k u v).toLinearMap =
      Finsupp.lmapDomain k k (oppositePathEquiv u v) := by
  apply Finsupp.lhom_ext
  intro p c
  simp only [LinearEquiv.coe_toLinearMap, oppositePathComponentEquiv_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

theorem oppositePathComponentEquiv_cut_map (u v : Q.Vertex) (c : ℤ) :
    (Q.pathCutComponent k u v c).map (Q.oppositePathComponentEquiv k u v).toLinearMap =
      Q.opposite.pathCutComponent k v.rev u.rev c := by
  rw [oppositePathComponentEquiv_toLinearMap, pathCutComponent, pathCutComponent,
    Finsupp.lmapDomain_supported]
  congr 1
  ext p
  constructor
  · rintro ⟨r,hr,rfl⟩
    simpa [oppositePathEquiv, Path.opposite_cutDegree] using hr
  · intro hp
    obtain ⟨r,rfl⟩ := (oppositePathEquiv u v).surjective p
    refine ⟨r, ?_, rfl⟩
    simpa [oppositePathEquiv, Path.opposite_cutDegree] using hp

noncomputable def oppositePathCutEquiv (u v : Q.Vertex) (c : ℤ) :
    Q.pathCutComponent k u v c ≃ₗ[k] Q.opposite.pathCutComponent k v.rev u.rev c :=
  (Q.oppositePathComponentEquiv k u v).ofSubmodules _ _
    (Q.oppositePathComponentEquiv_cut_map k u v c)

@[simp] theorem oppositePathCutEquiv_coe (u v : Q.Vertex) (c : ℤ)
    (f : Q.pathCutComponent k u v c) :
    (Q.oppositePathCutEquiv k u v c f).val = Q.oppositePathComponentEquiv k u v f.val := rfl

end ASGinzburg.CutQuiver
