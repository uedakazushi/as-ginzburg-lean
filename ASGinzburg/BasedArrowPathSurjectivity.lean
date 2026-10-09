import ASGinzburg.ArbitraryArrowPresentation

/-! Actual incoming families whose quotient classes are a specified
basis give surjective free-path presentations. This retains the actual
family, including its chosen representatives, throughout the proof. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q)

noncomputable def incomingElementGenerator (w : Q.LiftVertex) (i : ℤ)
    (a : ASResolution.GeneratorIndex (Q:=Q) (w:=w) i) : A.Hom i (Q.height w) :=
  A.homTransport _ _ i (Q.height w) a.property rfl (G w a.val)

variable (B : A.IncomingBasisSystem Q)
  (hclass : ∀ (w : Q.LiftVertex) (i : ℤ) (hi : i<Q.height w)
    (a : ASResolution.GeneratorIndex (Q:=Q) (w:=w) i),
    (Submodule.span k (A.products i (Q.height w))).mkQ
      (A.incomingElementGenerator Q G w i a)=B.basis w i hi a)

include hclass in
theorem incomingElementGenerator_decomposition (w : Q.LiftVertex) (i : ℤ) (hi : i<Q.height w) :
    Submodule.span k (Set.range (A.incomingElementGenerator Q G w i)) ⊔
      Submodule.span k (A.products i (Q.height w))=⊤ := by
  let p := Submodule.span k (A.products i (Q.height w))
  have hm : Submodule.map p.mkQ
      (Submodule.span k (Set.range (A.incomingElementGenerator Q G w i)))=⊤ := by
    rw [Submodule.map_span,←Set.range_comp]
    have hf : p.mkQ ∘ A.incomingElementGenerator Q G w i=B.basis w i hi :=
      funext (hclass w i hi)
    rw [hf]
    exact (B.basis w i hi).span_eq
  have hs := (p.map_mkQ_eq_top _).mp hm
  simpa only [sup_comm] using hs

theorem incomingElementGenerator_mem_path_range (u w : Q.LiftVertex)
    (a : ASResolution.GeneratorIndex (Q := Q) (w := w) (Q.height u)) :
    A.incomingElementGenerator Q G w (Q.height u) a ∈
      LinearMap.range (A.arrowPathLinearEvaluation Q G u w) := by
  rcases a with ⟨a,ha⟩
  have hu : Q.incomingSource w a=u := Q.height_bijective.injective ha
  subst u
  refine ⟨Finsupp.single (.snoc a (.nil (Q.incomingSource w a))) 1,?_⟩
  simp [incomingElementGenerator,homTransport,arrowPathEvaluation,A.id_comp]

include hclass in
theorem basedArrowPathLinearEvaluation_surjective (u v : Q.LiftVertex) :
    Function.Surjective (A.arrowPathLinearEvaluation Q G u v) := by
  have hmain : ∀ d : ℕ, ∀ u v : Q.LiftVertex, (Q.height v-Q.height u).toNat=d →
      ∀ f : A.Hom (Q.height u) (Q.height v),
        f ∈ LinearMap.range (A.arrowPathLinearEvaluation Q G u v) := by
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
      · have hgen : Submodule.span k (Set.range (A.incomingElementGenerator Q G v (Q.height u))) ≤
            LinearMap.range (A.arrowPathLinearEvaluation Q G u v) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨a,rfl⟩
          exact A.incomingElementGenerator_mem_path_range Q G u v a
        have hprod : Submodule.span k (A.products (Q.height u) (Q.height v)) ≤
            LinearMap.range (A.arrowPathLinearEvaluation Q G u v) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i,hui,hiv,a,b,rfl⟩
          obtain ⟨w,rfl⟩ := Q.height_bijective.surjective i
          obtain ⟨p,hp⟩ := ih (Q.height w-Q.height u).toNat (by omega) u w rfl a
          obtain ⟨q,hq⟩ := ih (Q.height v-Q.height w).toNat (by omega) w v rfl b
          exact ⟨Q.unrolledPathComp k q p,by rw [A.arrowPathLinearEvaluation_comp,hp,hq]⟩
        have ht : (⊤ : Submodule k (A.Hom (Q.height u) (Q.height v))) ≤
            LinearMap.range (A.arrowPathLinearEvaluation Q G u v) := by
          rw [←A.incomingElementGenerator_decomposition Q G B hclass v (Q.height u) hlt]
          exact sup_le hgen hprod
        exact ht Submodule.mem_top
  intro f
  exact hmain (Q.height v-Q.height u).toNat u v rfl f

include hclass in
theorem basedArrowPathPresentation_surjective (i j : ℤ) :
    Function.Surjective ((A.arrowPathPresentation Q G).map i j) :=
  (A.homTransport _ _ i j (Q.height_heightEquiv_symm i)
    (Q.height_heightEquiv_symm j)).surjective.comp
      (A.basedArrowPathLinearEvaluation_surjective Q G B hclass
        (Q.heightEquiv.symm i) (Q.heightEquiv.symm j))

end ASGinzburg.ZAlgebra
