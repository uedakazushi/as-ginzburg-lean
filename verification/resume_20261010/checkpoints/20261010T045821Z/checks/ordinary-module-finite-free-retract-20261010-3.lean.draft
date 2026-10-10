import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Retract

/-! Finite projective ordinary modules are precisely actual retracts of
finite free modules. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe v
variable (R : Type v) [Ring R]

def ordinaryFiniteProjectiveProperty (P : ModuleCat.{v} R) : Prop :=
  ∃ n : ℕ, Nonempty (Retract P (ModuleCat.of R (Fin n → R)))

theorem ordinaryModule_finiteFreeRetract (P : ModuleCat.{v} R)
    [Module.Finite R P] [Projective P] :
    ∃ n : ℕ, Nonempty (Retract P (ModuleCat.of R (Fin n → R))) := by
  letI : Module.Projective R P := inferInstance
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R P
  exact ⟨n, ⟨{
    i := ModuleCat.ofHom g
    r := ModuleCat.ofHom f
    retract := ModuleCat.hom_ext hfg }⟩⟩

theorem ordinaryFiniteProjectiveProperty_iff (P : ModuleCat.{v} R) :
    ordinaryFiniteProjectiveProperty R P ↔ Module.Finite R P ∧ Projective P := by
  constructor
  · rintro ⟨n, ⟨r⟩⟩
    letI : Projective (ModuleCat.of R (Fin n → R)) :=
      ModuleCat.projective_of_free (Pi.basisFun R (Fin n))
    refine ⟨Module.Finite.of_surjective r.r.hom
      ((ModuleCat.epi_iff_surjective r.r).mp inferInstance), ?_⟩
    refine ⟨fun f e _ => ?_⟩
    exact ⟨r.i ≫ Projective.factorThru (r.r ≫ f) e, by simp⟩
  · rintro ⟨hfinite, hprojective⟩
    letI := hfinite
    letI := hprojective
    exact ordinaryModule_finiteFreeRetract R P

theorem ordinaryFiniteProjectiveProperty_of_retract {P Q : ModuleCat.{v} R}
    (r : Retract P Q) (hQ : ordinaryFiniteProjectiveProperty R Q) :
    ordinaryFiniteProjectiveProperty R P := by
  obtain ⟨n, ⟨rQ⟩⟩ := hQ
  exact ⟨n, ⟨r.trans rQ⟩⟩

theorem ordinaryFiniteProjectiveProperty_of_iso {P Q : ModuleCat.{v} R}
    (e : P ≅ Q) (hQ : ordinaryFiniteProjectiveProperty R Q) :
    ordinaryFiniteProjectiveProperty R P :=
  ordinaryFiniteProjectiveProperty_of_retract R (Retract.ofIso e) hQ

theorem ordinaryFiniteProjectiveProperty_of_isZero {P : ModuleCat.{v} R}
    (hP : IsZero P) : ordinaryFiniteProjectiveProperty R P := by
  exact ⟨0, ⟨{
    i := 0
    r := 0
    retract := hP.eq_of_src _ _ }⟩⟩

end ASGinzburg
