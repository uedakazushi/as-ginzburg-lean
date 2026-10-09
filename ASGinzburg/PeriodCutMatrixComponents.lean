import ASGinzburg.PeriodCutGradedAlgebra

/-! Actual homogeneous matrix component embeddings and their shifted
products. Every finite cut block is the sum of these components. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

noncomputable def cutMatrixComponent (m : ℕ) (i j : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j)) : E.CutGradedBlock vertex m := by
  classical
  exact Pi.single i (Pi.single j f)

noncomputable def cutMatrixComponentLinear (m : ℕ) (i j : ι) :
    E.CutGradedHom m (vertex i) (vertex j) →ₗ[k] E.CutGradedBlock vertex m := by
  classical
  exact (LinearMap.single k (fun r => ∀ s, E.CutGradedHom m (vertex r) (vertex s)) i).comp
    (LinearMap.single k (fun s => E.CutGradedHom m (vertex i) (vertex s)) j)

omit [Fintype ι] in
@[simp] theorem cutMatrixComponent_apply_same (m : ℕ) (i j : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j)) :
    E.cutMatrixComponent vertex m i j f i j=f := by
  classical
  simp [cutMatrixComponent]

omit [Fintype ι] in
theorem cutMatrixComponent_source_ne (m : ℕ) (i j r s : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j)) (h : r≠i) :
    E.cutMatrixComponent vertex m i j f r s=0 := by
  classical
  simp [cutMatrixComponent,h]

theorem cutMatrixComp_component_same (m n : ℕ) (i j l : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j))
    (g : E.CutGradedHom n (vertex j) (vertex l)) :
    E.cutMatrixComp vertex m n (E.cutMatrixComponent vertex n j l g)
      (E.cutMatrixComponent vertex m i j f)=
        E.cutMatrixComponent vertex (m+n) i l (E.cutGradedComp m n g f) := by
  classical
  funext r s
  rw [cutMatrixComp_apply]
  by_cases hr : r=i
  · subst r
    by_cases hs : s=l
    · subst s
      rw [Finset.sum_eq_single j]
      · simp [cutMatrixComponent]
      · intro t ht h
        simp [cutMatrixComponent,h]
      · simp
    · simp [cutMatrixComponent,hs]
      apply Finset.sum_eq_zero
      intro t ht
      by_cases h : t=j
      · subst t
        simp [hs]
      · simp [h]
  · simp [cutMatrixComponent,hr]

theorem cutMatrixComp_component_ne (m n : ℕ) (i j r s : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j))
    (g : E.CutGradedHom n (vertex r) (vertex s)) (h : j≠r) :
    E.cutMatrixComp vertex m n (E.cutMatrixComponent vertex n r s g)
      (E.cutMatrixComponent vertex m i j f)=0 := by
  classical
  funext a b
  rw [cutMatrixComp_apply]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases ha : a=i
  · subst a
    by_cases ht' : t=j
    · subst t
      simp [cutMatrixComponent,h]
    · simp [cutMatrixComponent,ht']
  · simp [cutMatrixComponent,ha]

theorem sum_cutMatrixComponent (m : ℕ) (f : E.CutGradedBlock vertex m) :
    (∑ i : ι,∑ j : ι,E.cutMatrixComponent vertex m i j (f i j))=f := by
  classical
  funext r s
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single s]
    · exact E.cutMatrixComponent_apply_same vertex m r s (f r s)
    · intro j hj h
      simp [cutMatrixComponent,Ne.symm h]
    · simp
  · intro i hi h
    apply Finset.sum_eq_zero
    intro j hj
    exact E.cutMatrixComponent_source_ne vertex m i j r s (f i j) (Ne.symm h)
  · simp

theorem sum_cutMatrixComponent_id :
    (∑ i : ι,E.cutMatrixComponent vertex 0 i i (E.cutGradedId (vertex i)))=
      E.cutMatrixId vertex := by
  classical
  funext r s
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single r]
  · by_cases h : r=s
    · subst s
      simp
    · simp [cutMatrixComponent,cutMatrixId,h,Ne.symm h]
  · intro i hi h
    exact E.cutMatrixComponent_source_ne vertex 0 i i r s (E.cutGradedId (vertex i)) (Ne.symm h)
  · simp

end ASGinzburg.ZAlgebra.PeriodIso
