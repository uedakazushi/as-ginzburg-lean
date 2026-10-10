import work.ASGinzburgDraft.FiniteComponentAutomorphismCorners

/-! Actual vertex-fixed algebra automorphisms preserve the identities and
composition in every corner of the finite component algebra. -/
namespace ASGinzburg.LinearComponentAlgebra
universe u v
variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]
  (B : LinearComponentAlgebra k ι)

theorem totalAlgEquivComponentLinearEquiv_id (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i) (i : ι) :
    B.totalAlgEquivComponentLinearEquiv E hE i i (B.id i) = B.id i := by
  change E (B.totalIdempotent i) i i = B.id i
  rw [hE i]
  exact B.totalComponent_apply_same i i (B.id i)

theorem totalAlgEquivComponentLinearEquiv_comp (E : B.Total ≃ₐ[k] B.Total)
    (hE : ∀ i, E (B.totalIdempotent i) = B.totalIdempotent i)
    {i j l : ι} (f : B.Hom i j) (g : B.Hom j l) :
    B.totalAlgEquivComponentLinearEquiv E hE i l (B.comp g f) =
      B.comp (B.totalAlgEquivComponentLinearEquiv E hE j l g)
        (B.totalAlgEquivComponentLinearEquiv E hE i j f) := by
  have h : B.totalComponent i l (B.totalAlgEquivComponentLinearEquiv E hE i l
      (B.comp g f)) = B.totalComponent i l
      (B.comp (B.totalAlgEquivComponentLinearEquiv E hE j l g)
        (B.totalAlgEquivComponentLinearEquiv E hE i j f)) := by
    rw [B.totalAlgEquivComponentLinearEquiv_component,
      ← B.totalComponent_mul_same, map_mul,
      ← B.totalAlgEquivComponentLinearEquiv_component,
      ← B.totalAlgEquivComponentLinearEquiv_component,
      B.totalComponent_mul_same]
  simpa only [B.totalComponent_apply_same] using congrArg (fun x : B.Total => x i l) h

end ASGinzburg.LinearComponentAlgebra
