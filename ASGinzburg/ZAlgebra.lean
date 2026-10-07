import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Locally finite directed Z-algebras

The convention is `A.Hom u v = e_v A e_u` and `comp g f = g f`.
This is a concrete componentwise algebra, not a predicate standing in for
an algebra. Local finiteness and connectedness are part of its definition.
-/

namespace ASGinzburg

universe u v

structure ZAlgebra (k : Type u) [Field k] where
  Hom : ℤ → ℤ → Type v
  [homAdd : ∀ u v, AddCommGroup (Hom u v)]
  [homModule : ∀ u v, Module k (Hom u v)]
  id : ∀ v, Hom v v
  comp : ∀ {u v w}, Hom v w →ₗ[k] Hom u v →ₗ[k] Hom u w
  comp_id : ∀ {u v} (f : Hom u v), comp (id v) f = f
  id_comp : ∀ {u v} (f : Hom u v), comp f (id u) = f
  comp_assoc : ∀ {u v w x} (f : Hom u v) (g : Hom v w) (h : Hom w x),
    comp h (comp g f) = comp (comp h g) f
  positive : ∀ {u v}, v < u → ∀ f : Hom u v, f = 0
  connected : ∀ v (f : Hom v v), ∃ c : k, f = c • id v
  id_nonzero : ∀ v, id v ≠ 0
  finite : ∀ u v, Module.Finite k (Hom u v)

attribute [instance] ZAlgebra.homAdd ZAlgebra.homModule ZAlgebra.finite

namespace ZAlgebra

variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Periodicity is additional proof data and is not part of `ZAlgebra`. -/
structure PeriodIso (p : ℤ) where
  map : ∀ u v, A.Hom u v ≃ₗ[k] A.Hom (u + p) (v + p)
  map_id : ∀ v, map v v (A.id v) = A.id (v + p)
  map_comp : ∀ {u v w} (f : A.Hom u v) (g : A.Hom v w),
    map u w (A.comp g f) = A.comp (map v w g) (map u v f)

def IsPeriodic (p : ℤ) : Prop := Nonempty (A.PeriodIso p)

/-- A system of component subspaces closed under multiplication and identities. -/
structure LinearSubcategory where
  hom : ∀ u v, Submodule k (A.Hom u v)
  id_mem : ∀ v, A.id v ∈ hom v v
  comp_mem : ∀ {u v w} {f : A.Hom u v} {g : A.Hom v w},
    f ∈ hom u v → g ∈ hom v w → A.comp g f ∈ hom u w

/-- The decomposable positive-degree elements of a component. -/
def products (u v : ℤ) : Set (A.Hom u v) :=
  {x | ∃ w, u < w ∧ w < v ∧
    ∃ (f : A.Hom u w) (g : A.Hom w v), A.comp g f = x}

/-- The degree induction used in (1.10). The decomposition premise is exactly
the information that still has to be extracted from the first minimal
projective differential in Proposition 1.2. -/
theorem generated_of_decomposition
    (G : ∀ u v, Submodule k (A.Hom u v))
    (hdecomp : ∀ u v, u < v → G u v ⊔ Submodule.span k (A.products u v) = ⊤)
    (L : A.LinearSubcategory) (hG : ∀ u v, G u v ≤ L.hom u v) :
    ∀ u v, L.hom u v = ⊤ := by
  have hmain : ∀ d : ℕ, ∀ u v : ℤ, (v - u).toNat = d →
      ∀ f : A.Hom u v, f ∈ L.hom u v := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u v hd f
      rcases lt_trichotomy v u with hvu | hvu | huv
      · rw [A.positive hvu f]
        exact (L.hom u v).zero_mem
      · subst v
        obtain ⟨c, hc⟩ := A.connected u f
        rw [hc]
        exact (L.hom u u).smul_mem c (L.id_mem u)
      · have hprod : Submodule.span k (A.products u v) ≤ L.hom u v := by
          apply Submodule.span_le.mpr
          rintro x ⟨w, huw, hwv, a, b, rfl⟩
          apply L.comp_mem
          · exact ih (w - u).toNat (by omega) u w rfl a
          · exact ih (v - w).toNat (by omega) w v rfl b
        have htop : (⊤ : Submodule k (A.Hom u v)) ≤ L.hom u v := by
          rw [← hdecomp u v huv]
          exact sup_le (hG u v) hprod
        exact htop (Submodule.mem_top)
  intro u v
  apply top_unique
  intro f _
  exact hmain (v - u).toNat u v rfl f

end ZAlgebra
end ASGinzburg
