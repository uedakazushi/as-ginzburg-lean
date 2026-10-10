import ASGinzburg.GradedActionQuotientSpan
import ASGinzburg.GradedNilpotentNakayamaLinearGrading
import ASGinzburg.HomogeneousQuotientDecomposition

/-! Graded Nakayama on a genuine homogeneous quotient turns surjectivity
on the actual radical top into surjectivity of an ordinary module cover.
Neither the cover nor its source is assumed finitely generated. -/
namespace ASGinzburg
open scoped DirectSum
universe u v w z t s
variable (k : Type u) [Field k]
variable (R₀ : Type v) [Ring R₀] [Algebra k R₀]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module R₀ M]
  [IsScalarTower k R₀ M]
variable (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable (h₀ : ∀ (q : ℤ) (r : R₀) (x : M), x ∈ G q → r • x ∈ G q)
variable {ι : Type t} (d : ι → ℕ) (f : ι → M →ₗ[k] M) (I₀ : Ideal R₀)

include h₀ in
theorem homogeneousSubmodule_eq_top_of_radical_top
    (S : Submodule R₀ M)
    (hS : ∀ (q : ℤ) (x : M), x ∈ S → (DirectSum.decompose G x q : M) ∈ S)
    (hF : ∀ (i : ι) (x : M), x ∈ S → f i x ∈ S)
    (N₀ : ℕ) (hN₀ : I₀^N₀=⊥) (hd : ∀ i : ι, 0 < d i)
    (hf : ∀ (i : ι) (q : ℤ) (x : M), x ∈ G q → f i x ∈ G (q+(d i:ℤ)))
    (b : ℤ) (hb : ∀ q : ℤ, q < b → G q=⊥)
    (hTop : S.restrictScalars k ⊔ gradedNilpotentActionSpan k R₀ M f I₀=⊤) :
    S=⊤ := by
  let F := scalarSubmoduleQuotientOperator k R₀ M S f hF
  let QG : ℤ → Submodule k (M ⧸ S) :=
    homogeneousQuotientGrade k M G (S.restrictScalars k)
  letI : DirectSum.Decomposition QG :=
    homogeneousQuotientDecomposition k M G (S.restrictScalars k) hS
  have hQ₀ : ∀ (q : ℤ) (r : R₀) (x : M ⧸ S), x ∈ QG q → r • x ∈ QG q := by
    intro q r x hx
    obtain ⟨y,hy,rfl⟩ := hx
    change (S.restrictScalars k).mkQ (r • y) ∈ (G q).map (S.restrictScalars k).mkQ
    exact ⟨r • y,h₀ q r y hy,rfl⟩
  have hQF : ∀ (i : ι) (q : ℤ) (x : M ⧸ S),
      x ∈ QG q → F i x ∈ QG (q+(d i:ℤ)) := by
    intro i q x hx
    obtain ⟨y,hy,rfl⟩ := hx
    change (S.restrictScalars k).mkQ (f i y) ∈
      (G (q+(d i:ℤ))).map (S.restrictScalars k).mkQ
    exact ⟨f i y,hf i q y hy,rfl⟩
  have hQb : ∀ q : ℤ, q < b → QG q=⊥ := by
    intro q hq
    change (G q).map (S.restrictScalars k).mkQ=⊥
    rw [hb q hq,Submodule.map_bot]
  have hQK : gradedNilpotentActionSpan k R₀ (M ⧸ S) F I₀=⊤ :=
    gradedNilpotentActionSpan_quotient_eq_top k R₀ M S f hF I₀ hTop
  letI : Subsingleton (M ⧸ S) :=
    gradedModule_subsingleton_of_linear_grading_nilpotent_action_span_top k R₀ (M ⧸ S)
      QG hQ₀ d F I₀ N₀ hN₀ hd hQF b hQb hQK
  apply Submodule.eq_top_iff'.mpr
  intro x
  exact (Submodule.Quotient.mk_eq_zero S).mp (Subsingleton.elim _ _)

variable (R : Type z) [Ring R] [Algebra k R] [SMul R₀ R]
variable [Module R M] [IsScalarTower k R M] [IsScalarTower R₀ R M]
variable (L : Type s) [AddCommGroup L] [Module R L]

omit [Algebra k R] [IsScalarTower k R M] in
include h₀ in
theorem linearMap_surjective_of_homogeneous_radical_top
    (π : L →ₗ[R] M)
    (hπ : ∀ (q : ℤ) (x : M), x ∈ LinearMap.range π →
      (DirectSum.decompose G x q : M) ∈ LinearMap.range π)
    (a : ι → R) (ha : ∀ (i : ι) (x : M), f i x=a i • x)
    (N₀ : ℕ) (hN₀ : I₀^N₀=⊥) (hd : ∀ i : ι, 0 < d i)
    (hf : ∀ (i : ι) (q : ℤ) (x : M), x ∈ G q → f i x ∈ G (q+(d i:ℤ)))
    (b : ℤ) (hb : ∀ q : ℤ, q < b → G q=⊥)
    (hTop : ∀ y : M ⧸ gradedNilpotentActionSpan k R₀ M f I₀,
      ∃ x : L, (gradedNilpotentActionSpan k R₀ M f I₀).mkQ (π x)=y) :
    Function.Surjective π := by
  let S := (LinearMap.range π).restrictScalars R₀
  let K := gradedNilpotentActionSpan k R₀ M f I₀
  have hImage : (S.restrictScalars k).map K.mkQ=⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro y
    obtain ⟨x,hx⟩ := hTop y
    exact ⟨π x,⟨x,rfl⟩,hx⟩
  have hSK : S.restrictScalars k ⊔ K=⊤ := by
    have h := (Submodule.map_mkQ_eq_top K (S.restrictScalars k)).mp hImage
    simpa only [sup_comm] using h
  have hS : S=⊤ := homogeneousSubmodule_eq_top_of_radical_top k R₀ M G h₀ d f I₀ S hπ
    (fun i x hx => by rw [ha]; exact (LinearMap.range π).smul_mem (a i) hx)
    N₀ hN₀ hd hf b hb hSK
  intro y
  have hy : y ∈ S := by rw [hS]; exact Submodule.mem_top
  exact hy

end ASGinzburg
