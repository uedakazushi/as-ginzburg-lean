import ASGinzburg.ASIncomingBasisSystems
import ASGinzburg.ArbitraryArrowPathEvaluation

/-! Every actual arrow-basis system generates the algebra by genuine
unrolled paths. Surjectivity is derived by height induction. -/
namespace ASGinzburg.ZAlgebra.IncomingBasisSystem
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  (B : A.IncomingBasisSystem Q)

theorem incomingGenerator_mem_path_range (u w : Q.LiftVertex)
    (a : ASResolution.GeneratorIndex (Q := Q) (w := w) (Q.height u)) :
    B.incomingGenerator w (Q.height u) a ∈
      LinearMap.range (A.arrowPathLinearEvaluation Q B.incomingElement u w) := by
  rcases a with ⟨a,ha⟩
  have hu : Q.incomingSource w a=u := Q.height_bijective.injective ha
  subst u
  refine ⟨Finsupp.single (.snoc a (.nil (Q.incomingSource w a))) 1,?_⟩
  simp [incomingGenerator,homTransport,arrowPathEvaluation,A.id_comp]

theorem pathLinearEvaluation_surjective (u v : Q.LiftVertex) :
    Function.Surjective (A.arrowPathLinearEvaluation Q B.incomingElement u v) := by
  have hmain : ∀ d : ℕ, ∀ u v : Q.LiftVertex, (Q.height v-Q.height u).toNat=d →
      ∀ f : A.Hom (Q.height u) (Q.height v),
        f ∈ LinearMap.range (A.arrowPathLinearEvaluation Q B.incomingElement u v) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u v hd f
      rcases lt_trichotomy (Q.height v) (Q.height u) with hlt|heq|hlt
      · rw [A.positive hlt f]
        exact Submodule.zero_mem _
      · have hvu := Q.height_bijective.injective heq
        subst v
        obtain ⟨c,rfl⟩ := A.connected (Q.height u) f
        exact ⟨Finsupp.single (.nil u) c,by simp [arrowPathEvaluation]⟩
      · have hgen : Submodule.span k (Set.range (B.incomingGenerator v (Q.height u))) ≤
            LinearMap.range (A.arrowPathLinearEvaluation Q B.incomingElement u v) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨a,rfl⟩
          exact B.incomingGenerator_mem_path_range u v a
        have hprod : Submodule.span k (A.products (Q.height u) (Q.height v)) ≤
            LinearMap.range (A.arrowPathLinearEvaluation Q B.incomingElement u v) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i,hui,hiv,a,b,rfl⟩
          obtain ⟨w,rfl⟩ := Q.height_bijective.surjective i
          obtain ⟨p,hp⟩ := ih (Q.height w-Q.height u).toNat (by omega) u w rfl a
          obtain ⟨q,hq⟩ := ih (Q.height v-Q.height w).toNat (by omega) w v rfl b
          exact ⟨Q.unrolledPathComp k q p,by rw [A.arrowPathLinearEvaluation_comp,hp,hq]⟩
        have ht : (⊤ : Submodule k (A.Hom (Q.height u) (Q.height v))) ≤
            LinearMap.range (A.arrowPathLinearEvaluation Q B.incomingElement u v) := by
          rw [←B.incomingGenerator_decomposition v (Q.height u) hlt]
          exact sup_le hgen hprod
        exact ht Submodule.mem_top
  intro f
  exact hmain (Q.height v-Q.height u).toNat u v rfl f

end ASGinzburg.ZAlgebra.IncomingBasisSystem
