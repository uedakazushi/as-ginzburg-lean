import ASGinzburg.GinzburgGeneratorLayerBasis

/-! Genuine shifted prefix complexes, with the signed Ginzburg
differential, for the finite family of last generators of a fixed degree. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

abbrev GinzburgGeneratorPrefix (u v : Q.Vertex) (r q c : ℤ) :=
  Π a : {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r},
    Q.ginzburgCutCohomologicalComponent k u (a.val.source Q) (q-r) (c-a.val.cutDegree Q)

noncomputable def ginzburgSignedShiftDifferential (φ : Q.Potential k)
    (u v : Q.Vertex) (r q c : ℤ) :
    Q.ginzburgCutCohomologicalComponent k u v (q-r) c →ₗ[k]
      Q.ginzburgCutCohomologicalComponent k u v (q+1-r) c :=
  ginzburgSign k r •
    (((Q.ginzburgDifferential k φ u v).comp
      (Q.ginzburgCutCohomologicalComponent k u v (q-r) c).subtype).codRestrict
      (Q.ginzburgCutCohomologicalComponent k u v (q+1-r) c) (fun f => by
        have he : q+1-r=(q-r)+1 := by omega
        rw [he]
        exact ⟨Q.ginzburgDifferential_degree k φ (q-r) f.property.1,
          Q.ginzburgDifferential_cut k φ c f.property.2⟩))

noncomputable def ginzburgGeneratorPrefixDifferential (φ : Q.Potential k)
    (u v : Q.Vertex) (r q c : ℤ) :
    Q.GinzburgGeneratorPrefix k u v r q c →ₗ[k]
      Q.GinzburgGeneratorPrefix k u v r (q+1) c :=
  LinearMap.pi (fun a =>
    (Q.ginzburgSignedShiftDifferential k φ u (a.val.source Q)
      r q (c-a.val.cutDegree Q)).comp
      (LinearMap.proj a))

theorem ginzburgGeneratorPrefixDifferential_square (φ : Q.Potential k)
    (u v : Q.Vertex) (r q c : ℤ) :
    (Q.ginzburgGeneratorPrefixDifferential k φ u v r (q+1) c).comp
      (Q.ginzburgGeneratorPrefixDifferential k φ u v r q c)=0 := by
  apply LinearMap.ext
  intro f
  funext a
  apply Subtype.ext
  change ginzburgSign k r • Q.ginzburgDifferential k φ u (a.val.source Q)
    (ginzburgSign k r • Q.ginzburgDifferential k φ u (a.val.source Q) (f a).val)=0
  rw [map_smul,Q.ginzburgDifferential_square,smul_zero,smul_zero]

noncomputable def ginzburgGeneratorPrefixComplex (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) : CochainComplex (ModuleCat.{u} k) ℤ :=
  CochainComplex.of (fun q => ModuleCat.of k (Q.GinzburgGeneratorPrefix k u v r q c))
    (fun q => ModuleCat.ofHom (Q.ginzburgGeneratorPrefixDifferential k φ u v r q c))
    (fun q => by
      apply ModuleCat.hom_ext
      exact Q.ginzburgGeneratorPrefixDifferential_square k φ u v r q c)

end ASGinzburg.CutQuiver
