import ASGinzburg.PathArrowSubstitutionInverse
import ASGinzburg.VertexCutPathAutomorphisms
import ASGinzburg.PathCutProducts

/-! Actual homogeneous arrow replacements preserve the actual cut
grading. Inverse homogeneous substitutions give genuine automorphisms
in the vertex- and cut-preserving path-algebra subgroup. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathArrowSubstitutionPath_mem_cut (σ : Q.PathArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a:ℤ))
    {i j : Q.Vertex} (p : Q.Path i j) :
    Q.pathArrowSubstitutionPath k σ p ∈ Q.pathCutComponent k i j (p.cutDegree:ℤ) := by
  induction p with
  | nil =>
    simp only [pathArrowSubstitutionPath,Path.cutDegree,Nat.cast_zero]
    exact Finsupp.single_mem_supported k 1 rfl
  | @snoc j p a h ih =>
    subst j
    rw [pathArrowSubstitutionPath]
    simpa only [Path.cutDegree,Nat.cast_add] using Q.pathCutComponent_comp k ih (hσ a)

theorem pathArrowSubstitutionComponent_mem_cut (σ : Q.PathArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a:ℤ))
    (i j : Q.Vertex) (c : ℤ) (f : Q.PathComponent k i j)
    (hf : f ∈ Q.pathCutComponent k i j c) :
    Q.pathArrowSubstitutionComponent k σ i j f ∈ Q.pathCutComponent k i j c := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [Q.pathArrowSubstitutionComponent_single,one_smul]
    change (p.cutDegree:ℤ)=c at hp
    rw [← hp]
    exact Q.pathArrowSubstitutionPath_mem_cut k σ hσ p
  | zero => simpa only [map_zero] using (Q.pathCutComponent k i j c).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (Q.pathCutComponent k i j c).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using (Q.pathCutComponent k i j c).smul_mem a ih

theorem pathArrowSubstitution_mem_cut (σ : Q.PathArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a:ℤ))
    (c : ℤ) (x : Q.PathRing k) (hx : x ∈ Q.pathRingCutSubspace k c) :
    Q.pathArrowSubstitution k σ x ∈ Q.pathRingCutSubspace k c := by
  intro i j
  exact Q.pathArrowSubstitutionComponent_mem_cut k σ hσ i j c (x i j) (hx i j)

noncomputable def pathArrowSubstitutionVertexCutAutomorphism
    (σ τ : Q.PathArrowReplacement k)
    (hσ : ∀ a, σ a ∈ Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a:ℤ))
    (hτ : ∀ a, τ a ∈ Q.pathCutComponent k (Q.source a) (Q.target a) (Q.cutDegree a:ℤ))
    (hστ : ∀ a, Q.pathArrowSubstitutionComponent k σ (Q.source a) (Q.target a) (τ a) =
      Q.pathIdentityArrowReplacement k a)
    (hτσ : ∀ a, Q.pathArrowSubstitutionComponent k τ (Q.source a) (Q.target a) (σ a) =
      Q.pathIdentityArrowReplacement k a) : Q.VertexCutPathAutomorphism k := by
  refine ⟨Q.pathArrowSubstitutionAlgEquiv k σ τ hστ hτσ,?_,?_⟩
  · exact Q.pathArrowSubstitution_fixes_vertex k σ
  · intro c x
    change x ∈ Q.pathRingCutSubspace k c ↔
      Q.pathArrowSubstitution k σ x ∈ Q.pathRingCutSubspace k c
    constructor
    · exact Q.pathArrowSubstitution_mem_cut k σ hσ c x
    · intro hx
      have hback := Q.pathArrowSubstitution_mem_cut k τ hτ c
        (Q.pathArrowSubstitution k σ x) hx
      rw [Q.pathArrowSubstitution_inverse k τ σ hτσ x] at hback
      exact hback

end ASGinzburg.CutQuiver
