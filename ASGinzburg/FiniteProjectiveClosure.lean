import ASGinzburg.FiniteProjectiveDuality
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightFiniteProjectiveProperty_of_isZero {P : A.RightModule} (h : IsZero P) :
    A.rightFiniteProjectiveProperty P := by
  refine ⟨0, (fun i => Fin.elim0 i), ⟨{ i := 0, r := 0, retract := ?_ }⟩⟩
  rw [zero_comp]
  exact h.eq_of_src _ _

theorem leftFiniteProjectiveProperty_of_isZero {P : A.LeftModule} (h : IsZero P) :
    A.leftFiniteProjectiveProperty P := by
  refine ⟨0, (fun i => Fin.elim0 i), ⟨{ i := 0, r := 0, retract := ?_ }⟩⟩
  rw [zero_comp]
  exact h.eq_of_src _ _

theorem rightFiniteProjectiveProperty_representable (i : ℤ) :
    A.rightFiniteProjectiveProperty (A.representable i) :=
  ⟨1,(fun _ => i),⟨Retract.ofIso (coproductUniqueIso (fun _ : Fin 1 => A.representable i)).symm⟩⟩

theorem leftFiniteProjectiveProperty_representable (i : ℤ) :
    A.leftFiniteProjectiveProperty (A.leftRepresentable i) :=
  ⟨1,(fun _ => i),⟨Retract.ofIso (coproductUniqueIso (fun _ : Fin 1 => A.leftRepresentable i)).symm⟩⟩

theorem rightFiniteProjectiveProperty_coproduct {B : Type*} [Fintype B] (i : B → ℤ) :
    A.rightFiniteProjectiveProperty (∐ fun b => A.representable (i b)) := by
  refine ⟨Fintype.card B, (i ∘ (Fintype.equivFin B).symm), ⟨?_⟩⟩
  exact Retract.ofIso (Sigma.reindex (Fintype.equivFin B).symm (fun b => A.representable (i b))).symm

theorem leftFiniteProjectiveProperty_coproduct {B : Type*} [Fintype B] (i : B → ℤ) :
    A.leftFiniteProjectiveProperty (∐ fun b => A.leftRepresentable (i b)) := by
  refine ⟨Fintype.card B, (i ∘ (Fintype.equivFin B).symm), ⟨?_⟩⟩
  exact Retract.ofIso (Sigma.reindex (Fintype.equivFin B).symm (fun b => A.leftRepresentable (i b))).symm

noncomputable instance rightFiniteProjectiveHasZeroObject : HasZeroObject A.RightFiniteProjective := by
  refine ⟨⟨⟨0, A.rightFiniteProjectiveProperty_of_isZero (isZero_zero A.RightModule)⟩,?_⟩⟩
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact (isZero_zero A.RightModule).eq_of_src _ _

noncomputable instance leftFiniteProjectiveHasZeroObject : HasZeroObject A.LeftFiniteProjective := by
  refine ⟨⟨⟨0, A.leftFiniteProjectiveProperty_of_isZero (isZero_zero A.LeftModule)⟩,?_⟩⟩
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact (isZero_zero A.LeftModule).eq_of_src _ _
end ASGinzburg.ZAlgebra
