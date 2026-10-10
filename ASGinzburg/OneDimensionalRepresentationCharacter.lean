import ASGinzburg.LinearRepresentationEquivalence

/-! An actual one-dimensional algebra representation determines an
actual algebra character, and its action is that character's scalar action. -/
namespace ASGinzburg
universe u v w
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : R →ₐ[k] Module.End k V) (e : V ≃ₗ[k] k)

noncomputable def oneDimensionalRepresentationValue (r : R) : k := e (ρ r (e.symm 1))

theorem oneDimensionalRepresentation_scalar_action (r : R) (x : V) :
    e (ρ r x)=oneDimensionalRepresentationValue ρ e r*e x := by
  have hx : x=(e x) • e.symm 1 := by
    apply e.injective
    rw [e.map_smul,e.apply_symm_apply,smul_eq_mul,mul_one]
  conv_lhs => rw [hx]
  rw [map_smul,map_smul]
  change e x*e (ρ r (e.symm 1))=e (ρ r (e.symm 1))*e x
  exact mul_comm _ _

noncomputable def oneDimensionalRepresentationCharacter : R →ₐ[k] k where
  toFun := oneDimensionalRepresentationValue ρ e
  map_zero' := by
    change e (ρ 0 (e.symm 1))=0
    rw [map_zero,LinearMap.zero_apply,map_zero]
  map_one' := by
    change e (ρ 1 (e.symm 1))=1
    rw [map_one]
    exact e.apply_symm_apply 1
  map_add' r s := by
    change e (ρ (r+s) (e.symm 1))=e (ρ r (e.symm 1))+e (ρ s (e.symm 1))
    rw [map_add,LinearMap.add_apply,map_add]
  map_mul' r s := by
    change e (ρ (r*s) (e.symm 1))=_
    rw [map_mul]
    exact oneDimensionalRepresentation_scalar_action ρ e r (ρ s (e.symm 1))
  commutes' c := by
    change e (ρ (algebraMap k R c) (e.symm 1))=c
    rw [AlgHom.commutes]
    change e (c • e.symm 1)=c
    rw [e.map_smul,e.apply_symm_apply,smul_eq_mul,mul_one]

end ASGinzburg
