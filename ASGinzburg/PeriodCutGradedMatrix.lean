import ASGinzburg.PeriodCutGradedUnits

/-! The finite block of a nonnegative cut degree, with the actual
shifted composition summed over intermediate vertices. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

abbrev CutGradedBlock (m : ℕ) := ∀ i j : ι, E.CutGradedHom m (vertex i) (vertex j)

noncomputable def cutMatrixComp (m n : ℕ) :
    E.CutGradedBlock vertex n →ₗ[k] E.CutGradedBlock vertex m →ₗ[k]
      E.CutGradedBlock vertex (m+n) where
  toFun g :=
    { toFun := fun f i l => ∑ j, E.cutGradedComp m n (g j l) (f i j)
      map_add' := by
        intro f h
        funext i l
        simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        funext i l
        simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum] }
  map_add' := by
    intro g h
    ext f i l
    change (∑ j, E.cutGradedComp m n ((g+h) j l) (f i j))=
      (∑ j, E.cutGradedComp m n (g j l) (f i j))+
        (∑ j, E.cutGradedComp m n (h j l) (f i j))
    simp only [Pi.add_apply,map_add,LinearMap.add_apply,Finset.sum_add_distrib]
  map_smul' := by
    intro c g
    ext f i l
    change (∑ j, E.cutGradedComp m n ((c • g) j l) (f i j))=
      c • (∑ j, E.cutGradedComp m n (g j l) (f i j))
    simp only [Pi.smul_apply,map_smul,LinearMap.smul_apply,Finset.smul_sum]

theorem cutMatrixComp_apply (m n : ℕ)
    (f : E.CutGradedBlock vertex m) (g : E.CutGradedBlock vertex n) (i l : ι) :
    E.cutMatrixComp vertex m n g f i l=∑ j, E.cutGradedComp m n (g j l) (f i j) := rfl

noncomputable def cutBlockTransport (m n : ℕ) (h : m=n) :
    E.CutGradedBlock vertex m ≃ₗ[k] E.CutGradedBlock vertex n := by
  subst n
  exact LinearEquiv.refl k _

omit [Fintype ι] in
theorem cutBlockTransport_apply (m n : ℕ) (h : m=n)
    (f : E.CutGradedBlock vertex m) (i j : ι) :
    E.cutBlockTransport vertex m n h f i j =
      A.homTransport (vertex i) (vertex j+(m:ℤ)*p)
        (vertex i) (vertex j+(n:ℤ)*p) rfl (by rw [h]) (f i j) := by
  subst n
  rfl

theorem cutMatrixComp_assoc (m n q : ℕ)
    (f : E.CutGradedBlock vertex m) (g : E.CutGradedBlock vertex n)
    (h : E.CutGradedBlock vertex q) :
    E.cutMatrixComp vertex (m+n) q h (E.cutMatrixComp vertex m n g f)=
      E.cutBlockTransport vertex (m+(n+q)) ((m+n)+q) (Nat.add_assoc m n q).symm
        (E.cutMatrixComp vertex m (n+q) (E.cutMatrixComp vertex n q h g) f) := by
  funext i l
  rw [E.cutBlockTransport_apply]
  simp only [cutMatrixComp_apply,map_sum,LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  exact E.cutGradedComp_assoc m n q (f i j) (g j s) (h s l)

noncomputable def cutMatrixId : E.CutGradedBlock vertex 0 := by
  classical
  exact fun i j => if h : i=j then h ▸ E.cutGradedId (vertex i) else 0

omit [Fintype ι] in
@[simp] theorem cutMatrixId_diag (i : ι) :
    E.cutMatrixId vertex i i=E.cutGradedId (vertex i) := by
  classical
  simp [cutMatrixId]

omit [Fintype ι] in
theorem cutMatrixId_offdiag {i j : ι} (h : i≠j) : E.cutMatrixId vertex i j=0 := by
  classical
  simp [cutMatrixId,h]

theorem cutMatrixComp_id_right (m : ℕ) (f : E.CutGradedBlock vertex m) :
    E.cutMatrixComp vertex m 0 (E.cutMatrixId vertex) f=f := by
  classical
  funext i l
  rw [cutMatrixComp_apply,Finset.sum_eq_single l]
  · rw [cutMatrixId_diag,E.cutGradedComp_id_right]
  · intro j hj h
    rw [E.cutMatrixId_offdiag vertex h]
    simp
  · simp

theorem cutMatrixComp_id_left (m : ℕ) (f : E.CutGradedBlock vertex m) :
    E.cutBlockTransport vertex (0+m) m (Nat.zero_add m)
      (E.cutMatrixComp vertex 0 m f (E.cutMatrixId vertex))=f := by
  classical
  funext i l
  rw [cutBlockTransport_apply,cutMatrixComp_apply,map_sum,Finset.sum_eq_single i]
  · rw [cutMatrixId_diag,E.cutGradedComp_id_left]
  · intro j hj h
    rw [E.cutMatrixId_offdiag vertex (Ne.symm h),map_zero,map_zero]
  · simp

end ASGinzburg.ZAlgebra.PeriodIso
