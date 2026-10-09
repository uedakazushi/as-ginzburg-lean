import ASGinzburg.PeriodIntegerCorners

/-! R's actual homogeneous subspaces extended by zero to integer degrees. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutIntegerHomogeneousSpace (q : ℤ) :
    Submodule k (E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ))) :=
  if 0≤q then LinearMap.range
    (E.cutHomogeneousLinearInclusion (fun t : Q.Vertex => (t.val:ℤ)) q.toNat) else ⊥

theorem cutIntegerHomogeneousSpace_ofNat (n : ℕ) :
    E.cutIntegerHomogeneousSpace Q (n:ℤ)=LinearMap.range
      (E.cutHomogeneousLinearInclusion (fun t : Q.Vertex => (t.val:ℤ)) n) := by
  simp only [cutIntegerHomogeneousSpace,if_pos (Int.natCast_nonneg n),Int.toNat_natCast]

theorem cutIntegerHomogeneousSpace_negative {q : ℤ} (hq : q<0) :
    E.cutIntegerHomogeneousSpace Q q=⊥ := by
  simp only [cutIntegerHomogeneousSpace,if_neg (not_le.mpr hq)]

theorem integerCorner_le_integerHomogeneousSpace (q : ℤ) (i j : Q.Vertex) :
    E.integerCorner Q q i j≤E.cutIntegerHomogeneousSpace Q q := by
  by_cases hq : 0≤q
  · intro r hr
    rw [E.integerCorner_nonneg Q hq i j] at hr
    obtain ⟨f,rfl⟩ := hr
    rw [cutIntegerHomogeneousSpace,if_pos hq]
    exact ⟨E.cutMatrixComponent (fun t : Q.Vertex => (t.val:ℤ)) q.toNat i j f,rfl⟩
  · rw [E.integerCorner_negative Q (by omega),E.cutIntegerHomogeneousSpace_negative Q (by omega)]

end ASGinzburg.ZAlgebra.PeriodIso
