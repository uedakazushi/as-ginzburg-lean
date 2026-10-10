import work.ASGinzburgDraft.TriangleQuadraticPaths
import work.ASGinzburgDraft.TriangleJacobianQuadraticRelations
import ASGinzburg.JacobianUnrollingProducts

/-! The canonical X and Y arrows are actual bases of the adjacent
Jacobian components, for every original triangle potential. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleJacobianHomogeneousContext_cut0_endpoints (φ : triangle333.Potential k)
    {s t : triangle333.Vertex} {f : triangle333.PathComponent k s t}
    (hf : f ∈ triangle333.pathJacobianHomogeneousContexts k φ s t 0) : s = 0 ∧ t = 2 := by
  obtain ⟨a,l,r,hdegree,_⟩ := hf
  have hd : l.cutDegree + (1-triangle333.cutDegree a) + r.cutDegree = 0 := by
    exact_mod_cast hdegree
  have ha : triangle333.cut a = true := by
    cases h : triangle333.cut a
    · simp only [CutQuiver.cutDegree,h,Bool.false_eq_true,ite_false] at hd
      omega
    · rfl
  have hca : triangle333.cutDegree a = 1 := triangle333.cutDegree_true ha
  have hl : l.cutDegree = 0 := by omega
  have hr : r.cutDegree = 0 := by omega
  obtain ⟨z,haz⟩ := triangleCutArrow_eq_Z a ha
  subst a
  have hln := l.winding_nonneg
  have hrn := r.winding_nonneg
  rw [l.winding_eq,hl,triangleZ_target_zero] at hln
  rw [r.winding_eq,hr,triangleZ_source_two] at hrn
  constructor
  · apply Fin.ext
    change (s.val : ℕ) = 0
    simp only [Nat.cast_zero,mul_zero,add_zero,Fin.val_zero] at hln
    omega
  · apply Fin.ext
    change t.val = 2
    have ht : t.val < 3 := t.isLt
    simp only [Nat.cast_zero,mul_zero,add_zero] at hrn
    change 0 ≤ (t.val : ℤ) - 2 at hrn
    omega

theorem triangleJacobianCutIdeal_eq_bot_of_other_endpoints (φ : triangle333.Potential k)
    (s t : triangle333.Vertex) (hst : s ≠ 0 ∨ t ≠ 2) :
    triangle333.pathJacobianCutIdeal k φ s t 0 = ⊥ := by
  have he : triangle333.pathJacobianHomogeneousContexts k φ s t 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hs,ht⟩ := triangleJacobianHomogeneousContext_cut0_endpoints k φ hf
    rcases hst with h | h
    · exact h hs
    · exact h ht
  apply eq_bot_iff.mpr
  intro f hf
  have hf' : f.val ∈ (triangle333.pathJacobianIdeal k φ).hom s t := hf
  have hz := triangle333.pathJacobianCut_mem_homogeneousContextSpan k φ 0 hf' f.property
  rw [he,Submodule.span_empty] at hz
  change f = 0
  apply Subtype.ext
  simpa using hz

theorem triangleCutZeroEdgeComponent_eq_arrow (s : Fin 3) (hs : s.val < 2) :
    triangle333.pathCutComponent k s (triangleEdgeTarget s) 0 =
      triangleArrowComponent k s (triangleEdgeTarget s) := by
  unfold CutQuiver.pathCutComponent triangleArrowComponent
  congr 1
  ext p
  change (p.cutDegree : ℤ) = 0 ↔ p.length = 1
  have ht : (triangleEdgeTarget s).val = s.val + 1 := by
    dsimp [triangleEdgeTarget]
    omega
  have hw := p.winding_eq
  rw [triangle_path_winding,ht] at hw
  change (p.length : ℤ) = ((s.val + 1 : ℕ) : ℤ) - s.val + 3 * p.cutDegree at hw
  omega

noncomputable def triangleXArrowCutEquiv :
    ArrowSpace333 k ≃ₗ[k] triangle333.pathCutComponent k 0 1 0 :=
  (triangleXArrowEquiv k).trans (LinearEquiv.ofEq _ _
    (triangleCutZeroEdgeComponent_eq_arrow k 0 (by decide)).symm)

noncomputable def triangleYArrowCutEquiv :
    ArrowSpace333 k ≃ₗ[k] triangle333.pathCutComponent k 1 2 0 :=
  (triangleYArrowEquiv k).trans (LinearEquiv.ofEq _ _
    (triangleCutZeroEdgeComponent_eq_arrow k 1 (by decide)).symm)

@[simp] theorem triangleXArrowCutEquiv_single (i : Fin 3) (c : k) :
    (triangleXArrowCutEquiv k (Pi.single i c)).val = Finsupp.single (triangleXPath i) c := by
  exact triangleXArrowEquiv_single k i c

@[simp] theorem triangleYArrowCutEquiv_single (i : Fin 3) (c : k) :
    (triangleYArrowCutEquiv k (Pi.single i c)).val = Finsupp.single (triangleYPath i) c := by
  exact triangleYArrowEquiv_single k i c

noncomputable def triangleJacobianXArrowEquiv (φ : triangle333.Potential k) :
    ArrowSpace333 k ≃ₗ[k] (triangle333.unrolledJacobianZAlgebra k φ).Hom 0 1 :=
  ((triangleXArrowCutEquiv k).trans
    ((triangle333.pathJacobianCutIdeal k φ 0 1 0).quotEquivOfEqBot
      (triangleJacobianCutIdeal_eq_bot_of_other_endpoints k φ 0 1 (by
        right; decide))).symm).trans
          (triangle333.homogeneousJacobianUnrolledEquiv k φ (0,0) (1,0))

noncomputable def triangleJacobianYArrowEquiv (φ : triangle333.Potential k) :
    ArrowSpace333 k ≃ₗ[k] (triangle333.unrolledJacobianZAlgebra k φ).Hom 1 2 :=
  ((triangleYArrowCutEquiv k).trans
    ((triangle333.pathJacobianCutIdeal k φ 1 2 0).quotEquivOfEqBot
      (triangleJacobianCutIdeal_eq_bot_of_other_endpoints k φ 1 2 (by
        left; decide))).symm).trans
          (triangle333.homogeneousJacobianUnrolledEquiv k φ (1,0) (2,0))

noncomputable def triangleJacobianXArrow (φ : triangle333.Potential k) (i : Fin 3) :
    (triangle333.unrolledJacobianZAlgebra k φ).Hom 0 1 :=
  triangle333.homogeneousJacobianUnrolledEquiv k φ (0,0) (1,0)
    (Submodule.Quotient.mk ⟨Finsupp.single (triangleXPath i) 1,
      Finsupp.single_mem_supported _ _ (by simp)⟩)

noncomputable def triangleJacobianYArrow (φ : triangle333.Potential k) (i : Fin 3) :
    (triangle333.unrolledJacobianZAlgebra k φ).Hom 1 2 :=
  triangle333.homogeneousJacobianUnrolledEquiv k φ (1,0) (2,0)
    (Submodule.Quotient.mk ⟨Finsupp.single (triangleYPath i) 1,
      Finsupp.single_mem_supported _ _ (by simp)⟩)

@[simp] theorem triangleJacobianXArrowEquiv_single (φ : triangle333.Potential k) (i : Fin 3) :
    triangleJacobianXArrowEquiv k φ (Pi.single i 1) = triangleJacobianXArrow k φ i := by
  unfold triangleJacobianXArrowEquiv triangleJacobianXArrow
  simp only [LinearEquiv.trans_apply,Submodule.quotEquivOfEqBot_symm_apply]
  congr 2
  apply Subtype.ext
  exact triangleXArrowCutEquiv_single k i 1

@[simp] theorem triangleJacobianYArrowEquiv_single (φ : triangle333.Potential k) (i : Fin 3) :
    triangleJacobianYArrowEquiv k φ (Pi.single i 1) = triangleJacobianYArrow k φ i := by
  unfold triangleJacobianYArrowEquiv triangleJacobianYArrow
  simp only [LinearEquiv.trans_apply,Submodule.quotEquivOfEqBot_symm_apply]
  congr 2
  apply Subtype.ext
  exact triangleYArrowCutEquiv_single k i 1

noncomputable def triangleJacobianXArrowBasis (φ : triangle333.Potential k) :
    Module.Basis (Fin 3) k ((triangle333.unrolledJacobianZAlgebra k φ).Hom 0 1) :=
  (Pi.basisFun k (Fin 3)).map (triangleJacobianXArrowEquiv k φ)

noncomputable def triangleJacobianYArrowBasis (φ : triangle333.Potential k) :
    Module.Basis (Fin 3) k ((triangle333.unrolledJacobianZAlgebra k φ).Hom 1 2) :=
  (Pi.basisFun k (Fin 3)).map (triangleJacobianYArrowEquiv k φ)

@[simp] theorem triangleJacobianXArrowBasis_apply (φ : triangle333.Potential k) (i : Fin 3) :
    triangleJacobianXArrowBasis k φ i = triangleJacobianXArrow k φ i := by
  simp [triangleJacobianXArrowBasis]

@[simp] theorem triangleJacobianYArrowBasis_apply (φ : triangle333.Potential k) (i : Fin 3) :
    triangleJacobianYArrowBasis k φ i = triangleJacobianYArrow k φ i := by
  simp [triangleJacobianYArrowBasis]

end ASGinzburg
