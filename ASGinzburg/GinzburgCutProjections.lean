import ASGinzburg.GinzburgDifferentialGradings

/-! Actual cut projections commute with the degree-one differential. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCutProjection (u v : Q.Vertex) (c : ℤ) :
    Q.GinzburgPathComponent k u v →ₗ[k] Q.GinzburgPathComponent k u v :=
  Finsupp.linearCombination k (fun p => if p.cutDegree=c then Finsupp.single p 1 else 0)

@[simp] theorem ginzburgCutProjection_single {u v : Q.Vertex} (c : ℤ)
    (p : Q.GinzburgPath u v) (a : k) :
    Q.ginzburgCutProjection k u v c (Finsupp.single p a)=
      if p.cutDegree=c then Finsupp.single p a else 0 := by
  classical
  by_cases h : p.cutDegree=c <;> simp [ginzburgCutProjection,h]

theorem ginzburgCutProjection_on_cut {u v : Q.Vertex} (c d : ℤ)
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCutComponent k u v d) :
    Q.ginzburgCutProjection k u v c f=if d=c then f else 0 := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    change p.cutDegree=d at hp
    simp only [ginzburgCutProjection_single,hp]
  | zero => simp
  | add f g hf hg ihf ihg => by_cases h : d=c <;> simp [map_add,ihf,ihg,h]
  | smul a f hf ih => by_cases h : d=c <;> simp [map_smul,ih,h]

theorem ginzburgCutProjection_cohomological {u v : Q.Vertex} (c q : ℤ)
    {f : Q.GinzburgPathComponent k u v} (hf : f ∈ Q.ginzburgCohomologicalComponent k u v q) :
    Q.ginzburgCutProjection k u v c f ∈ Q.ginzburgCohomologicalComponent k u v q := by
  change f ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    rw [ginzburgCutProjection_single]
    split_ifs
    · exact Finsupp.single_mem_supported _ _ hp
    · exact Submodule.zero_mem _
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [map_add] using Submodule.add_mem _ ihf ihg
  | smul a f hf ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem ginzburgCutProjection_mem {u v : Q.Vertex} (c : ℤ) (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgCutProjection k u v c f ∈ Q.ginzburgCutComponent k u v c := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | single p a =>
    rw [ginzburgCutProjection_single]
    split_ifs with hp
    · exact Finsupp.single_mem_supported _ _ hp
    · exact Submodule.zero_mem _

theorem ginzburgDifferential_cutProjection (φ : Q.Potential k) {u v : Q.Vertex}
    (c : ℤ) (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgDifferential k φ u v (Q.ginzburgCutProjection k u v c f)=
      Q.ginzburgCutProjection k u v c (Q.ginzburgDifferential k φ u v f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | single p a =>
    rw [ginzburgCutProjection_single,ginzburgDifferential_single,map_smul,
      Q.ginzburgCutProjection_on_cut k c p.cutDegree (p.differential_cut Q k φ)]
    by_cases h : p.cutDegree=c <;> simp [h]

end ASGinzburg.CutQuiver
