import ASGinzburg.ZAlgebra

/-!
# Gluing coherent finite-window algebra maps

This proves the last part of Proposition 1.4. The required window maps
are explicit input. Producing them from `D Ext³(-, A)` is not proved.
-/

namespace ASGinzburg.ZAlgebra

universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def InWindow (l r x : ℤ) : Prop := l ≤ x ∧ x ≤ r

theorem InWindow.mono {l r l' r' x : ℤ} (h : InWindow l r x)
    (hl : l' ≤ l) (hr : r ≤ r') : InWindow l' r' x := by
  exact ⟨hl.trans h.1, h.2.trans hr⟩

structure WindowSystem (p : ℤ) where
  map : ∀ l r u v, InWindow l r u → InWindow l r v →
    A.Hom u v ≃ₗ[k] A.Hom (u + p) (v + p)
  coherent : ∀ l r l' r' u v (hu : InWindow l r u) (hv : InWindow l r v)
    (hl : l' ≤ l) (hr : r ≤ r'),
    map l r u v hu hv = map l' r' u v (hu.mono hl hr) (hv.mono hl hr)
  map_id : ∀ l r v (hv : InWindow l r v),
    map l r v v hv hv (A.id v) = A.id (v + p)
  map_comp : ∀ l r u v w (hu : InWindow l r u) (hv : InWindow l r v)
    (hw : InWindow l r w) (f : A.Hom u v) (g : A.Hom v w),
    map l r u w hu hw (A.comp g f) =
      A.comp (map l r v w hv hw g) (map l r u v hu hv f)

namespace WindowSystem

variable {A} {p : ℤ} (W : A.WindowSystem p)

def globalMap (u v : ℤ) : A.Hom u v ≃ₗ[k] A.Hom (u + p) (v + p) :=
  W.map (min u v) (max u v) u v
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩

theorem globalMap_eq_window (l r u v : ℤ) (hu : InWindow l r u) (hv : InWindow l r v) :
    W.globalMap u v = W.map l r u v hu hv := by
  apply W.coherent
  · exact le_min hu.1 hv.1
  · exact max_le hu.2 hv.2

def periodIso : A.PeriodIso p where
  map := W.globalMap
  map_id := by
    intro v
    exact W.map_id (min v v) (max v v) v _
  map_comp := by
    intro u v w f g
    let l := min u (min v w)
    let r := max u (max v w)
    have hu : InWindow l r u := ⟨min_le_left _ _, le_max_left _ _⟩
    have hv : InWindow l r v :=
      ⟨(min_le_right _ _).trans (min_le_left _ _),
        (le_max_left _ _).trans (le_max_right _ _)⟩
    have hw : InWindow l r w :=
      ⟨(min_le_right _ _).trans (min_le_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
    rw [W.globalMap_eq_window l r u w hu hw,
      W.globalMap_eq_window l r v w hv hw,
      W.globalMap_eq_window l r u v hu hv]
    exact W.map_comp l r u v w hu hv hw f g

include W in
theorem isPeriodic : A.IsPeriodic p := ⟨periodIso W⟩

end WindowSystem
end ASGinzburg.ZAlgebra
