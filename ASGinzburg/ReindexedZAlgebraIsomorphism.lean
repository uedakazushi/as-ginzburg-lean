import ASGinzburg.ZAlgebraIsomorphisms

/-! Compatible actual component equivalences indexed through a surjective
height map yield a genuine integer-indexed Z-algebra isomorphism. -/
namespace ASGinzburg.ZAlgebra
universe u v w x
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (B : ZAlgebra.{u,w} k)

noncomputable def Isomorphism.ofSurjectiveReindex {X : Type x}
    (f : X → ℤ) (hf : Function.Surjective f)
    (E : ∀ x y, A.Hom (f x) (f y) ≃ₗ[k] B.Hom (f x) (f y))
    (hid : ∀ x, E x x (A.id (f x)) = B.id (f x))
    (hcomp : ∀ x y z, ∀ (a : A.Hom (f x) (f y)) (b : A.Hom (f y) (f z)),
      E x z (A.comp b a) = B.comp (E y z b) (E x y a)) : Isomorphism A B := by
  classical
  let s : ℤ → X := fun i => Classical.choose (hf i)
  have hs (i : ℤ) : f (s i) = i := Classical.choose_spec (hf i)
  let F (i j : ℤ) : A.Hom i j ≃ₗ[k] B.Hom i j :=
    (A.homTransport i j (f (s i)) (f (s j)) (hs i).symm (hs j).symm).trans
      ((E (s i) (s j)).trans
        (B.homTransport (f (s i)) (f (s j)) i j (hs i) (hs j)))
  refine { map := F, map_id := ?_, map_comp := ?_ }
  · intro i
    dsimp [F]
    rw [A.homTransport_id, hid, B.homTransport_id]
  · intro i j l a b
    dsimp [F]
    rw [A.homTransport_comp, hcomp, B.homTransport_comp]

end ASGinzburg.ZAlgebra
