import ASGinzburg.ModuleBidualEvaluation
import Mathlib.CategoryTheory.Retract
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] {G : C ⥤ C}

theorem isIso_natTrans_app_retract (η : 𝟭 C ⟶ G) {X Y : C}
    (r : Retract X Y) [IsIso (η.app Y)] : IsIso (η.app X) := by
  have hi : η.app X ≫ G.map r.i = r.i ≫ η.app Y := by
    exact (η.naturality r.i).symm
  have hr : r.r ≫ η.app X = η.app Y ≫ G.map r.r := by
    exact η.naturality r.r
  refine ⟨⟨G.map r.i ≫ inv (η.app Y) ≫ r.r, ?_, ?_⟩⟩
  · rw [← Category.assoc, hi, Category.assoc,
      IsIso.hom_inv_id_assoc, r.retract]
    rfl
  · rw [Category.assoc, Category.assoc, hr,
      ← Category.assoc (inv (η.app Y)), IsIso.inv_hom_id, Category.id_comp,
      ← G.map_comp, r.retract, G.map_id]

theorem isIso_natTrans_app_coproduct {I : Type} [HasCoproductsOfShape I C]
    (η : 𝟭 C ⟶ G) (f : I → C) [PreservesColimit (Discrete.functor f) G]
    [∀ i, IsIso (η.app (f i))] : IsIso (η.app (∐ f)) := by
  have h : η.app (∐ f) = CategoryTheory.Limits.Sigma.map (fun i => η.app (f i)) ≫ sigmaComparison G f := by
    apply Sigma.hom_ext
    intro i
    erw [ι_colimMap_assoc]
    rw [ι_comp_sigmaComparison]
    exact η.naturality (Sigma.ι f i)
  rw [h]
  infer_instance
end ASGinzburg
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable instance rightFiniteSumBidualEvaluationIsIso (n : ℕ) (i : Fin n → ℤ) :
    IsIso (A.rightModuleBidualEvaluation (∐ fun j : Fin n => A.representable (i j))) := by
  letI : ∀ j : Fin n, IsIso
      (A.rightModuleBidualEvaluationNatTrans.app (A.representable (i j))) :=
    fun j => A.representableBidualEvaluationIsIso (i j)
  exact ASGinzburg.isIso_natTrans_app_coproduct A.rightModuleBidualEvaluationNatTrans
    (fun j : Fin n => A.representable (i j))

noncomputable instance leftFiniteSumBidualEvaluationIsIso (n : ℕ) (i : Fin n → ℤ) :
    IsIso (A.leftModuleBidualEvaluation (∐ fun j : Fin n => A.leftRepresentable (i j))) := by
  letI : ∀ j : Fin n, IsIso
      (A.leftModuleBidualEvaluationNatTrans.app (A.leftRepresentable (i j))) :=
    fun j => A.leftRepresentableBidualEvaluationIsIso (i j)
  exact ASGinzburg.isIso_natTrans_app_coproduct A.leftModuleBidualEvaluationNatTrans
    (fun j : Fin n => A.leftRepresentable (i j))

/-- The original paper's definition: a retract of a finite sum of right P_i. -/
def rightFiniteProjectiveProperty : ObjectProperty A.RightModule :=
  fun P => ∃ (n : ℕ) (i : Fin n → ℤ), Nonempty (Retract P (∐ fun j => A.representable (i j)))

/-- A retract of a finite sum of left A e_i, with actual splitting maps. -/
def leftFiniteProjectiveProperty : ObjectProperty A.LeftModule :=
  fun P => ∃ (n : ℕ) (i : Fin n → ℤ), Nonempty (Retract P (∐ fun j => A.leftRepresentable (i j)))

theorem rightFiniteProjectiveProperty_bidual {P : A.RightModule}
    (h : A.rightFiniteProjectiveProperty P) : IsIso (A.rightModuleBidualEvaluation P) := by
  obtain ⟨n,i,⟨r⟩⟩ := h
  letI : IsIso (A.rightModuleBidualEvaluationNatTrans.app (∐ fun j => A.representable (i j))) :=
    A.rightFiniteSumBidualEvaluationIsIso n i
  exact ASGinzburg.isIso_natTrans_app_retract A.rightModuleBidualEvaluationNatTrans r

theorem leftFiniteProjectiveProperty_bidual {P : A.LeftModule}
    (h : A.leftFiniteProjectiveProperty P) : IsIso (A.leftModuleBidualEvaluation P) := by
  obtain ⟨n,i,⟨r⟩⟩ := h
  letI : IsIso (A.leftModuleBidualEvaluationNatTrans.app (∐ fun j => A.leftRepresentable (i j))) :=
    A.leftFiniteSumBidualEvaluationIsIso n i
  exact ASGinzburg.isIso_natTrans_app_retract A.leftModuleBidualEvaluationNatTrans r
end ASGinzburg.ZAlgebra
