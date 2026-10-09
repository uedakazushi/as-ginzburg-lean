import ASGinzburg.FiniteComponentAlgebraMaps
import ASGinzburg.FiniteComponentIdempotents

/-! The proved finite component algebra maps carry actual single
matrix embeddings to the corresponding single matrix embeddings. -/
namespace ASGinzburg.LinearComponentAlgebra
universe u v
variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]
  (B C : LinearComponentAlgebra k ι)

omit [Fintype ι] in
theorem totalLinearMapOfComponents_component
    (f : ∀ i j,B.Hom i j →ₗ[k] C.Hom i j) (i j : ι) (a : B.Hom i j) :
    B.totalLinearMapOfComponents C f (B.totalComponent i j a)=C.totalComponent i j (f i j a) := by
  classical
  funext p q
  by_cases hp : p=i
  · subst p
    by_cases hq : q=j
    · subst q
      change f i j (B.totalComponent i j a i j)=C.totalComponent i j (f i j a) i j
      rw [B.totalComponent_apply_same,C.totalComponent_apply_same]
    · change f i q (B.totalComponent i j a i q)=C.totalComponent i j (f i j a) i q
      simp [totalComponent,hq]
  · change f p q (B.totalComponent i j a p q)=C.totalComponent i j (f i j a) p q
    rw [B.totalComponent_apply_source_ne i j p q a hp,
      C.totalComponent_apply_source_ne i j p q (f i j a) hp,map_zero]

theorem totalAlgEquivOfComponents_component
    (e : ∀ i j,B.Hom i j ≃ₗ[k] C.Hom i j) (hid : ∀ i,e i i (B.id i)=C.id i)
    (hmul : ∀ {i j l} (x : B.Hom i j) (y : B.Hom j l),
      e i l (B.comp y x)=C.comp (e j l y) (e i j x)) (i j : ι) (a : B.Hom i j) :
    B.totalAlgEquivOfComponents C e hid hmul (B.totalComponent i j a)=C.totalComponent i j (e i j a) :=
  B.totalLinearMapOfComponents_component C (fun i j => (e i j).toLinearMap) i j a

end ASGinzburg.LinearComponentAlgebra
