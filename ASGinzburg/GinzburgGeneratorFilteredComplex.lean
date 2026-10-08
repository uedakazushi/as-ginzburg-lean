import ASGinzburg.GinzburgGeneratorLayerQuotients

/-! The genuine last-generator filtration consists of actual subcomplexes
of the homogeneous Ginzburg augmentation complex. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDifferential_mem_generatorFiltrationAtDegree (φ : Q.Potential k)
    {u v : Q.Vertex} {r q c : ℤ} {f : Q.GinzburgPathComponent k u v}
    (hf : f ∈ Q.ginzburgGeneratorFiltrationAtDegree k u v r q c) :
    Q.ginzburgDifferential k φ u v f ∈ Q.ginzburgGeneratorFiltrationAtDegree k u v r (q+1) c := by
  rw [Q.ginzburgGeneratorFiltrationAtDegree_eq_inf] at hf ⊢
  exact ⟨Q.ginzburgDifferential_mem_generatorFiltration k φ hf.1,
    Q.ginzburgDifferential_degree k φ q hf.2.1,Q.ginzburgDifferential_cut k φ c hf.2.2⟩

noncomputable def ginzburgGeneratorFilteredDifferential (φ : Q.Potential k)
    (u v : Q.Vertex) (r q c : ℤ) :
    Q.ginzburgGeneratorFiltrationAtDegree k u v r q c →ₗ[k]
      Q.ginzburgGeneratorFiltrationAtDegree k u v r (q+1) c :=
  ((Q.ginzburgDifferential k φ u v).comp
    (Q.ginzburgGeneratorFiltrationAtDegree k u v r q c).subtype).codRestrict _
      (fun f => Q.ginzburgDifferential_mem_generatorFiltrationAtDegree k φ f.property)

theorem ginzburgGeneratorFilteredDifferential_square (φ : Q.Potential k)
    (u v : Q.Vertex) (r q c : ℤ) :
    (Q.ginzburgGeneratorFilteredDifferential k φ u v r (q+1) c).comp
      (Q.ginzburgGeneratorFilteredDifferential k φ u v r q c)=0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact Q.ginzburgDifferential_square k φ f.val

noncomputable def ginzburgGeneratorFilteredComplex (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ :=
  CochainComplex.of
    (fun q => ModuleCat.of k (Q.ginzburgGeneratorFiltrationAtDegree k u v r q c))
    (fun q => ModuleCat.ofHom (Q.ginzburgGeneratorFilteredDifferential k φ u v r q c))
    (fun q => by
      apply ModuleCat.hom_ext
      exact Q.ginzburgGeneratorFilteredDifferential_square k φ u v r q c)

def ginzburgGeneratorHigherLayer (u v : Q.Vertex) (r q c : ℤ) :
    Submodule k (Q.ginzburgGeneratorFiltrationAtDegree k u v r q c) :=
  (Q.ginzburgGeneratorFiltrationAtDegree k u v (r+1) q c).comap
    (Q.ginzburgGeneratorFiltrationAtDegree k u v r q c).subtype

theorem ginzburgGeneratorFilteredDifferential_mem_higherLayer (φ : Q.Potential k)
    {u v : Q.Vertex} {r q c : ℤ}
    {f : Q.ginzburgGeneratorFiltrationAtDegree k u v r q c}
    (hf : f ∈ Q.ginzburgGeneratorHigherLayer k u v r q c) :
    Q.ginzburgGeneratorFilteredDifferential k φ u v r q c f ∈
      Q.ginzburgGeneratorHigherLayer k u v r (q+1) c :=
  Q.ginzburgDifferential_mem_generatorFiltrationAtDegree k φ hf

end ASGinzburg.CutQuiver
