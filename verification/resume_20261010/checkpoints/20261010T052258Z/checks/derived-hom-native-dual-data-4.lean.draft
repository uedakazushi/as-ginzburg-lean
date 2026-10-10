import work.ASGinzburgDraft.GradedOrdinaryRingDualInternalGrading
import work.ASGinzburgDraft.GradedOrdinaryRingDualBoundedBelow
import work.ASGinzburgDraft.OrdinaryRingDualTensorEvaluation

/-! Native internally graded ordinary ring duals are genuine opposite-ring
graded module data. Their action and grading are the actual ring-dual
action and homogeneous subspaces, and nonnegative rings give lower bounds. -/
namespace ASGinzburg
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]

def ordinaryOppositeRingGrade (G : ℤ → Submodule k R) (q : ℤ) : Submodule k Rᵐᵒᵖ where
  carrier := {r | r.unop ∈ G q}
  zero_mem' := (G q).zero_mem
  add_mem' := (G q).add_mem
  smul_mem' := fun c _ hr => (G q).smul_mem c hr

@[simp] theorem ordinaryOppositeRingGrade_mem_iff
    (G : ℤ → Submodule k R) (q : ℤ) (r : Rᵐᵒᵖ) :
    r ∈ ordinaryOppositeRingGrade G q ↔ r.unop ∈ G q := Iff.rfl

namespace GradedOrdinaryModuleData
attribute [local instance 2100] ordinaryRingDualTensorModuleK
variable {G : ℤ → Submodule k R} [DirectSum.Decomposition G]
variable (M : GradedOrdinaryModuleData k R G)
variable (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))

def ringDualNativeGrade (q : ℤ) : Submodule k (ordinaryRingDual R M.ringModule) where
  carrier := {f | ∀ p : ℤ, ∀ x : M.ringModule, x ∈ M.grade p → f x ∈ G (p + q)}
  zero_mem' := fun _ _ _ => (G _).zero_mem
  add_mem' := fun hf hg p x hx => (G _).add_mem (hf p x hx) (hg p x hx)
  smul_mem' c f hf p x hx := by
    change (((algebraMap k Rᵐᵒᵖ c) • f) x) ∈ G (p + q)
    rw [ordinaryRingDual_smul_apply,
      MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      ← Algebra.commutes c (f x), ← Algebra.smul_def]
    exact (G _).smul_mem c (hf p x hx)

omit [DirectSum.Decomposition G] in
@[simp] theorem ringDualNativeGrade_mem_iff (q : ℤ)
    (f : ordinaryRingDual R M.ringModule) :
    f ∈ M.ringDualNativeGrade q ↔ f ∈ M.ringDualGrade q := Iff.rfl

omit [DirectSum.Decomposition G] in
theorem ringDualNativeGrade_eq_bot (q : ℤ) (hq : M.ringDualGrade q = ⊥) :
    M.ringDualNativeGrade q = ⊥ := by
  ext f
  change f ∈ M.ringDualGrade q ↔ f = 0
  rw [hq]
  rfl

noncomputable def ringDualData [Module.Finite R M.ringModule] :
    GradedOrdinaryModuleData k Rᵐᵒᵖ (ordinaryOppositeRingGrade G) where
  ringModule := ordinaryRingDual R M.ringModule
  grade := M.ringDualNativeGrade
  isInternal := by
    change DirectSum.IsInternal M.ringDualGrade
    exact M.ringDualGrade_isInternal hG
  smul_mem p q r hr f hf := by
    simpa only [MulOpposite.op_unop] using M.ringDualGrade_smul_mem hG p q r.unop hr f hf

theorem ringDualData_exists_lower_bound [Module.Finite R M.ringModule]
    (hGneg : ∀ p : ℤ, p < 0 → G p = ⊥) :
    ∃ b : ℤ, (M.ringDualData hG).BoundedBelow b := by
  obtain ⟨b, hb⟩ := M.ringDualGrade_exists_lower_bound hGneg
  exact ⟨b, fun q hq => M.ringDualNativeGrade_eq_bot q (hb q hq)⟩

theorem ringDualData_map_preservesGrade
    (N : GradedOrdinaryModuleData k R G)
    [Module.Finite R M.ringModule] [Module.Finite R N.ringModule]
    (f : M.ringModule ⟶ N.ringModule) (hf : M.PreservesGrade N f) :
    (N.ringDualData hG).PreservesGrade (M.ringDualData hG)
      (ModuleCat.ofHom (ordinaryRingDualMap R f)) :=
  fun q g hg => M.ringDualMap_preservesGrade N f hf q g hg

end GradedOrdinaryModuleData
end ASGinzburg
