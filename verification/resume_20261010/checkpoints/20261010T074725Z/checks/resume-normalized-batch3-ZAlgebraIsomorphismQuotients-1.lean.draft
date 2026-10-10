import ASGinzburg.ZAlgebraIsomorphisms

/-! Vertex-fixed isomorphisms that carry genuine two-sided component
ideals onto one another induce genuine isomorphisms of their quotients. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
universe u v w
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k} {A : ZAlgebra.{u,w} k}
  (F : Isomorphism B A) (I : B.LinearIdeal) (J : A.LinearIdeal)
  (hI : ∀ i, I.hom i i=⊥) (hJ : ∀ i, J.hom i i=⊥)
  (hF : ∀ i j, (I.hom i j).map (F.map i j).toLinearMap=J.hom i j)

noncomputable def idealQuotientIsomorphism : Isomorphism (I.quotient hI) (J.quotient hJ) where
  map i j := Submodule.Quotient.equiv _ _ (F.map i j) (hF i j)
  map_id := by
    intro i
    change Submodule.Quotient.mk (F.map i i (B.id i)) = Submodule.Quotient.mk (A.id i)
    exact congrArg Submodule.Quotient.mk (F.map_id i)
  map_comp := by
    intro i j l f g
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (I.hom j l).mkQ_surjective g
    change Submodule.Quotient.mk (F.map i l (B.comp g f)) =
      Submodule.Quotient.mk (A.comp (F.map j l g) (F.map i j f))
    exact congrArg Submodule.Quotient.mk (F.map_comp f g)

theorem idealQuotientIsomorphism_apply_mk (i j : ℤ) (f : B.Hom i j) :
    (F.idealQuotientIsomorphism I J hI hJ hF).map i j (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (F.map i j f) := rfl

end ASGinzburg.ZAlgebra.Isomorphism
