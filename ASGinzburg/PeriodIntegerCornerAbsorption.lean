import ASGinzburg.PeriodCornerCover

/-! Every actual integer corner is fixed by its source and target idempotents. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem integerCorner_target_absorption (m : ℤ) (i j : Q.Vertex)
    (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
    (hr : r∈E.integerCorner Q m i j) :
    E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) j*r=r := by
  by_cases hm : 0≤m
  · rw [E.integerCorner_nonneg Q hm] at hr
    rcases hr with ⟨f,rfl⟩
    exact E.cutVertexIdempotent_mul_component (fun t : Q.Vertex => (t.val:ℤ)) m.toNat i j f
  · rw [E.integerCorner_negative Q (by omega)] at hr
    have h : r=0 := by simpa only [Submodule.mem_bot] using hr
    rw [h,mul_zero]

theorem integerCorner_source_absorption (m : ℤ) (i j : Q.Vertex)
    (r : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)))
    (hr : r∈E.integerCorner Q m i j) :
    r*E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i=r := by
  by_cases hm : 0≤m
  · rw [E.integerCorner_nonneg Q hm] at hr
    rcases hr with ⟨f,rfl⟩
    exact E.cutComponent_mul_vertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) m.toNat i j f
  · rw [E.integerCorner_negative Q (by omega)] at hr
    have h : r=0 := by simpa only [Submodule.mem_bot] using hr
    rw [h,zero_mul]

end ASGinzburg.ZAlgebra.PeriodIso
