import ASGinzburg.RightModuleRadical
import ASGinzburg.RightModuleAbelian

/-! A genuine graded Nakayama lemma in the directed cover model.
A right module supported below an upper vertex bound vanishes when
every component is spanned by its positive-degree right products. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModule_eq_zero_of_boundedAbove_radical_top
    (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → ∀ x : (A.rightModuleEvaluation i).obj M, x = 0)
    (hr : ∀ i : ℤ, A.positiveActionSpan M i = ⊤) :
    ∀ i : ℤ, ∀ x : (A.rightModuleEvaluation i).obj M, x = 0 := by
  have H : ∀ n : ℕ, ∀ i : ℤ, b+1-(n:ℤ) ≤ i →
      ∀ x : (A.rightModuleEvaluation i).obj M, x = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi x
      exact hb i (by omega) x
    | succ n ih =>
      intro i hi x
      by_cases hit : b+1-(n:ℤ) ≤ i
      · exact ih i hit x
      · have hx : x ∈ A.positiveActionSpan M i := by
          rw [hr i]
          exact Submodule.mem_top
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨j, hij, z, a, rfl⟩ := hy
          rw [ih j (by omega) z, map_zero]
        | zero => rfl
        | add y z hy hz ihy ihz => rw [ihy, ihz, add_zero]
        | smul c y hy ihy => rw [ihy, smul_zero]
  intro i x
  exact H (b+1-i).toNat i (by omega) x

theorem rightModule_isZero_of_boundedAbove_radical_top
    (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M))
    (hr : ∀ i : ℤ, A.positiveActionSpan M i = ⊤) : IsZero M := by
  have hzero := A.rightModule_eq_zero_of_boundedAbove_radical_top M b
    (fun i hi x => by
      letI := ModuleCat.isZero_iff_subsingleton.mp (hb i hi)
      exact Subsingleton.elim x 0) hr
  apply (IsZero.iff_id_eq_zero M).mpr
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hzero X.unop.index x

end ASGinzburg.ZAlgebra
