import work.ASGinzburgDraft.TriangleArrowContragredient

/-! The actual arrow/contragredient contraction is invariant for every
bilinear map, hence for the two genuine loop-differential products. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module k M]

theorem triangleArrow_bilinear_coordinates
    (B : ArrowSpace333 k →ₗ[k] ArrowSpace333 k →ₗ[k] M)
    (x y : ArrowSpace333 k) :
    B x y = ∑ j : Fin 3, ∑ l : Fin 3,
      (x j * y l) • B (Pi.single j 1) (Pi.single l 1) := by
  classical
  calc
    B x y = B (∑ j : Fin 3, x j • (Pi.single j (1 : k) : ArrowSpace333 k)) y := by
      rw [←triangleArrow_basis_expansion]
    _ = ∑ j : Fin 3, x j • B (Pi.single j 1) y := by
      simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        x j • B (Pi.single j 1) y =
            x j • B (Pi.single j 1)
              (∑ l : Fin 3, y l • (Pi.single l (1 : k) : ArrowSpace333 k)) := by
          rw [←triangleArrow_basis_expansion]
        _ = _ := by simp only [map_sum,map_smul,Finset.smul_sum,smul_smul]

theorem triangleArrow_bilinear_contraction_invariant
    (B : ArrowSpace333 k →ₗ[k] ArrowSpace333 k →ₗ[k] M)
    (g : ArrowSpace333 k ≃ₗ[k] ArrowSpace333 k) :
    (∑ i : Fin 3, B (g (Pi.single i 1))
      (triangleArrowContragredient k g (Pi.single i 1))) =
      ∑ i : Fin 3, B (Pi.single i 1) (Pi.single i 1) := by
  classical
  have he : (∑ i : Fin 3, B (g (Pi.single i 1))
      (triangleArrowContragredient k g (Pi.single i 1))) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
        (g (Pi.single i 1) j * triangleArrowContragredient k g (Pi.single i 1) l) •
          B (Pi.single j 1) (Pi.single l 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact triangleArrow_bilinear_coordinates k M B _ _
  rw [he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_smul,triangleArrow_inverse_matrix_sum]
  simp [Pi.single_apply]

end ASGinzburg
