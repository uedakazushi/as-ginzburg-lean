import ASGinzburg.PathCyclicDerivativeSupport

/-! Genuine path-valued cyclic derivatives of the actual closed-path
potential space, obtained through the proved injective word embedding. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathWordMap_range (u v : Q.Vertex) :
    LinearMap.range (Q.pathWordMap k u v)=Q.pathWordSpace k u v := by
  rw [pathWordMap,LinearMap.range_eq_map,
    ←(Finsupp.supported_univ : Finsupp.supported k k (Set.univ : Set (Q.Path u v))=⊤),
    Finsupp.lmapDomain_supported]
  change Finsupp.supported k k (Path.toList '' Set.univ)=Finsupp.supported k k _
  congr 1
  ext w
  simp

noncomputable def pathWordEquiv (u v : Q.Vertex) :
    Q.PathComponent k u v ≃ₗ[k] Q.pathWordSpace k u v :=
  (LinearEquiv.ofInjective (Q.pathWordMap k u v) (Q.pathWordMap_injective k u v)).trans
    (LinearEquiv.ofEq _ _ (Q.pathWordMap_range k u v))

theorem pathWordEquiv_coe (u v : Q.Vertex) (f : Q.PathComponent k u v) :
    (Q.pathWordEquiv k u v f).val=Q.pathWordMap k u v f := rfl

noncomputable def pathCyclicDerivative (a : Q.Arrow) :
    Q.Potential k →ₗ[k] Q.PathComponent k (Q.target a) (Q.source a) :=
  (Q.pathWordEquiv k (Q.target a) (Q.source a)).symm.toLinearMap.comp
    ((((cyclicDerivative a).comp (Q.potentialSpace k).subtype)).codRestrict
      (Q.pathWordSpace k (Q.target a) (Q.source a))
      (fun φ => Q.cyclicDerivative_potential_mem k a φ))

theorem pathWordMap_pathCyclicDerivative (a : Q.Arrow) (φ : Q.Potential k) :
    Q.pathWordMap k (Q.target a) (Q.source a) (Q.pathCyclicDerivative k a φ)=
      cyclicDerivative a φ.val := by
  rw [←Q.pathWordEquiv_coe]
  change ((Q.pathWordEquiv k (Q.target a) (Q.source a))
    ((Q.pathWordEquiv k (Q.target a) (Q.source a)).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ASGinzburg.CutQuiver
