import ASGinzburg.PeriodCutZeroProjection

/-! Actual homogeneous left ideals in the native direct-sum grading.
Every left ideal containing the positive-degree ideal is homogeneous. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutHomogeneousProjection (m : ℕ) :
    E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) →ₗ[k]
      E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)) :=
  (E.cutHomogeneousLinearInclusion (fun i : Q.Vertex => (i.val:ℤ)) m).comp
    (DirectSum.component k ℕ (E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ))) m)

def CutHomogeneousLeftIdeal (I : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))) : Prop :=
  ∀ x∈I,∀ m : ℕ,E.cutHomogeneousProjection Q m x∈I

theorem cutHomogeneousProjection_apply (m : ℕ)
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) :
    E.cutHomogeneousProjection Q m x=
      E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val:ℤ)) m (x m) := rfl

theorem cutHomogeneousProjection_positive_mem (m : ℕ)
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) :
    E.cutHomogeneousProjection Q (m+1) x∈E.cutPositiveIdeal Q := by
  change E.cutZeroProjection Q (E.cutHomogeneousProjection Q (m+1) x)=0
  rw [E.cutHomogeneousProjection_apply,E.cutZeroProjection_homogeneous]
  rfl

theorem cutRemoveZero_mem_positive
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) :
    x-E.cutHomogeneousProjection Q 0 x∈E.cutPositiveIdeal Q := by
  change E.cutZeroProjection Q (x-E.cutHomogeneousProjection Q 0 x)=0
  rw [map_sub,E.cutZeroProjection_apply,E.cutHomogeneousProjection_apply,
    E.cutZeroProjection_homogeneous]
  exact sub_self _

theorem cutHomogeneousLeftIdeal_of_positive_le
    (I : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))))
    (hPI : E.cutPositiveIdeal Q≤I) : E.CutHomogeneousLeftIdeal Q I := by
  intro x hx m
  cases m with
  | zero =>
    have hsub := I.sub_mem hx (hPI (E.cutRemoveZero_mem_positive Q x))
    simpa only [sub_sub_cancel] using hsub
  | succ m => exact hPI (E.cutHomogeneousProjection_positive_mem Q m x)

theorem cutPositiveIdeal_homogeneous : E.CutHomogeneousLeftIdeal Q (E.cutPositiveIdeal Q) :=
  E.cutHomogeneousLeftIdeal_of_positive_le Q _ le_rfl

theorem cutHomogeneousLeftIdeal_sup
    (I J : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))))
    (hI : E.CutHomogeneousLeftIdeal Q I) (hJ : E.CutHomogeneousLeftIdeal Q J) :
    E.CutHomogeneousLeftIdeal Q (I⊔J) := by
  intro x hx m
  rcases Submodule.mem_sup.mp hx with ⟨a,ha,b,hb,rfl⟩
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨E.cutHomogeneousProjection Q m a,hI a ha m,
    E.cutHomogeneousProjection Q m b,hJ b hb m,rfl⟩

theorem cutHomogeneous_sup_positive_ne_top
    (I : Ideal (E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))))
    (hI : E.CutHomogeneousLeftIdeal Q I) (hne : I≠⊤) : I⊔E.cutPositiveIdeal Q≠⊤ := by
  intro htop
  have hone : (1 : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ)))∈I⊔E.cutPositiveIdeal Q := by
    rw [htop]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hone with ⟨a,ha,b,hb,hab⟩
  have ha0 : a 0=1 := by
    have h := congrArg (E.cutZeroProjection Q) hab
    have hb0 := (E.mem_cutPositiveIdeal_iff Q b).mp hb
    rw [map_add,map_one,E.cutZeroProjection_apply,E.cutZeroProjection_apply,hb0,add_zero] at h
    exact h
  apply hne
  apply (Ideal.eq_top_iff_one I).mpr
  have h := hI a ha 0
  rw [E.cutHomogeneousProjection_apply,ha0] at h
  exact h

end ASGinzburg.ZAlgebra.PeriodIso
