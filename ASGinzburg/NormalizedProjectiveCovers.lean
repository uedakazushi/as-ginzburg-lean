import ASGinzburg.RightModuleProjectives
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rigidity and uniqueness of normalized projective covers

The hypotheses below are proved for actual truncated representables and their
Nakayama images. They are not added to the AS regularity condition.
-/

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

theorem endomorphism_eq_id_of_preserves_nonzero_map {P S : C}
    (hEnd : Module.finrank k (P ⟶ P) = 1) (p : P ⟶ S) (hp : p ≠ 0)
    (t : P ⟶ P) (ht : t ≫ p = p) : t = 𝟙 P := by
  have hId : (𝟙 P : P ⟶ P) ≠ 0 := by
    intro h
    apply hp
    rw [← Category.id_comp p,h,zero_comp]
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hEnd hId t
  rw [← hc,Linear.smul_comp,Category.id_comp] at ht
  have hz : (c-1) • p = 0 := by rw [sub_smul,one_smul,ht,sub_self]
  have hc1 : c = 1 := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hp)
  simpa [hc1] using hc.symm

end ASGinzburg

namespace ASGinzburg
open CategoryTheory
universe v w
variable {C : Type v} [Category.{w} C]

noncomputable def normalizedProjectiveIso {P Q S : C} [Projective P] [Projective Q]
    (p : P ⟶ S) (q : Q ⟶ S) [Epi p] [Epi q]
    (hP : ∀ t : P ⟶ P, t ≫ p = p → t = 𝟙 P)
    (hQ : ∀ t : Q ⟶ Q, t ≫ q = q → t = 𝟙 Q) : P ≅ Q where
  hom := Projective.factorThru p q
  inv := Projective.factorThru q p
  hom_inv_id := hP _ (by simp)
  inv_hom_id := hQ _ (by simp)

@[reassoc] theorem normalizedProjectiveIso_hom_comp {P Q S : C} [Projective P] [Projective Q]
    (p : P ⟶ S) (q : Q ⟶ S) [Epi p] [Epi q]
    (hP : ∀ t : P ⟶ P, t ≫ p = p → t = 𝟙 P)
    (hQ : ∀ t : Q ⟶ Q, t ≫ q = q → t = 𝟙 Q) :
    (normalizedProjectiveIso p q hP hQ).hom ≫ q = p := Projective.factorThru_comp _ _

theorem normalizedProjectiveIso_hom_unique {P Q S : C} [Projective P] [Projective Q]
    (p : P ⟶ S) (q : Q ⟶ S) [Epi p] [Epi q]
    (hP : ∀ t : P ⟶ P, t ≫ p = p → t = 𝟙 P)
    (hQ : ∀ t : Q ⟶ Q, t ≫ q = q → t = 𝟙 Q)
    (f : P ⟶ Q) (hf : f ≫ q = p) : f = (normalizedProjectiveIso p q hP hQ).hom := by
  let e := normalizedProjectiveIso p q hP hQ
  have h : f ≫ e.inv = 𝟙 P := hP _ (by dsimp [e,normalizedProjectiveIso]; simp [hf])
  apply (cancel_mono e.inv).mp
  exact h.trans e.hom_inv_id.symm

theorem epi_of_comp_epi_of_rigid_projective {P S X : C} [Projective P]
    (p : P ⟶ S) (hP : ∀ t : P ⟶ P, t ≫ p = p → t = 𝟙 P)
    (f : X ⟶ P) [Epi (f ≫ p)] : Epi f := by
  have h : Projective.factorThru p (f ≫ p) ≫ f = 𝟙 P := hP _ (by simp)
  exact epi_of_epi_fac h
end ASGinzburg
