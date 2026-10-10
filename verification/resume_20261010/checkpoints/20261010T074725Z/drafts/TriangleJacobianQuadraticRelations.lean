import ASGinzburg.TrianglePotentialCoordinates
import ASGinzburg.PathJacobianHomogeneousContexts
import ASGinzburg.PathJacobianGrading

/-! The actual cut-zero quadratic corner of the triangle Jacobian ideal
is spanned by the three original Z-arrow cyclic derivatives. -/
namespace ASGinzburg

theorem triangleZ_source_two (z : Fin 3) : triangle333.source (triangleZ z) = 2 := by
  apply Fin.ext
  change (6 + z.val) / 3 = 2
  omega

theorem triangleCutArrow_eq_Z (a : triangle333.Arrow) (ha : triangle333.cut a = true) :
    ∃ z : Fin 3, a = triangleZ z := by
  have hav : 6 ≤ a.val := by simpa [triangle333] using ha
  have hal : a.val < 9 := a.isLt
  let z : Fin 3 := ⟨a.val - 6, by omega⟩
  refine ⟨z, Fin.ext ?_⟩
  dsimp [triangleZ,z]
  omega

namespace CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem transportPathComponent_mem_cut {s t s' t' : Q.Vertex}
    (hs : s = s') (ht : t = t') {c : ℤ} {f : Q.PathComponent k s t}
    (hf : f ∈ Q.pathCutComponent k s t c) :
    Q.transportPathComponent k hs ht f ∈ Q.pathCutComponent k s' t' c := by
  subst s' t'
  exact hf

theorem pathJacobianContext_eq_transport_of_zero_cut (φ : Q.Potential k) (a : Q.Arrow)
    {s t : Q.Vertex} (hs : Q.target a = s) (ht : Q.source a = t)
    (l : Q.Path s (Q.target a)) (r : Q.Path (Q.source a) t)
    (hl : l.cutDegree = 0) (hr : r.cutDegree = 0) :
    Q.pathComp k (Finsupp.single r 1)
      (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)) =
        Q.transportPathComponent k hs ht (Q.pathCyclicDerivative k a φ) := by
  subst s t
  have hl0 := l.zero_cut_has_no_nonempty_cycle hl
  have hr0 := r.zero_cut_has_no_nonempty_cycle hr
  have hln : l = .nil (Q.target a) := by
    apply Path.toList_injective
    change l.toList = []
    apply List.length_eq_zero_iff.mp
    rw [l.length_toList,hl0]
  have hrn : r = .nil (Q.source a) := by
    apply Path.toList_injective
    change r.toList = []
    apply List.length_eq_zero_iff.mp
    rw [r.length_toList,hr0]
  rw [hln,hrn]
  change Q.pathComp k (Q.pathId k (Q.source a))
    (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Q.pathId k (Q.target a))) = _
  rw [Q.id_pathComp k,Q.pathComp_id k]
  rfl

end CutQuiver

universe u
variable (k : Type u) [Field k]

noncomputable def triangleCutZDerivative (φ : triangle333.Potential k) (z : Fin 3) :
    triangle333.pathCutComponent k 0 2 0 :=
  ⟨triangle333.transportPathComponent k (triangleZ_target_zero z) (triangleZ_source_two z)
    (triangle333.pathCyclicDerivative k (triangleZ z) φ), by
      apply triangle333.transportPathComponent_mem_cut k
      simpa [CutQuiver.cutDegree,triangleZ_cut] using
        triangle333.pathCyclicDerivative_mem_pathCut k (triangleZ z) φ⟩

theorem triangleCutZDerivative_mem_ideal (φ : triangle333.Potential k) (z : Fin 3) :
    triangleCutZDerivative k φ z ∈ triangle333.pathJacobianCutIdeal k φ 0 2 0 := by
  change (triangleCutZDerivative k φ z).val ∈ (triangle333.pathJacobianIdeal k φ).hom 0 2
  exact triangle333.subset_generatedPathIdeal k _ _ _
    ⟨triangleZ z,triangleZ_target_zero z,triangleZ_source_two z,rfl⟩

theorem triangleJacobianHomogeneousContext02_eq_cutZ (φ : triangle333.Potential k)
    {f : triangle333.PathComponent k 0 2}
    (hf : f ∈ triangle333.pathJacobianHomogeneousContexts k φ 0 2 0) :
    ∃ z : Fin 3, f = (triangleCutZDerivative k φ z).val := by
  obtain ⟨a,l,r,hdegree,rfl⟩ := hf
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
  refine ⟨z,?_⟩
  exact triangle333.pathJacobianContext_eq_transport_of_zero_cut k φ (triangleZ z)
    (triangleZ_target_zero z) (triangleZ_source_two z) l r hl hr

theorem triangleJacobianCutIdeal_eq_span_cutZ (φ : triangle333.Potential k) :
    triangle333.pathJacobianCutIdeal k φ 0 2 0 =
      Submodule.span k (Set.range (triangleCutZDerivative k φ)) := by
  apply le_antisymm
  · intro f hf
    have hf' : f.val ∈ (triangle333.pathJacobianIdeal k φ).hom 0 2 := hf
    have hs := triangle333.pathJacobianCut_mem_homogeneousContextSpan k φ 0 hf' f.property
    have hsub : triangle333.pathJacobianHomogeneousContexts k φ 0 2 0 ⊆
        Set.range (fun z => (triangleCutZDerivative k φ z).val) := by
      intro x hx
      obtain ⟨z,hz⟩ := triangleJacobianHomogeneousContext02_eq_cutZ k φ hx
      exact ⟨z,hz.symm⟩
    have hm := Submodule.span_mono hsub hs
    let P := triangle333.pathCutComponent k 0 2 0
    have himage : P.subtype '' Set.range (triangleCutZDerivative k φ) =
        Set.range (fun z => (triangleCutZDerivative k φ z).val) := by
      ext x
      constructor
      · rintro ⟨y,⟨z,rfl⟩,rfl⟩
        exact ⟨z,rfl⟩
      · rintro ⟨z,rfl⟩
        exact ⟨triangleCutZDerivative k φ z,⟨z,rfl⟩,rfl⟩
    apply (Submodule.apply_mem_span_image_iff_mem_span
      (f := P.subtype) P.injective_subtype).mp
    rw [himage]
    exact hm
  · apply Submodule.span_le.mpr
    rintro f ⟨z,rfl⟩
    exact triangleCutZDerivative_mem_ideal k φ z

end ASGinzburg
