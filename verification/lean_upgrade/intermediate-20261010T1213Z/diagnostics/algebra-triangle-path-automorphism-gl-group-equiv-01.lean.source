import ASGinzburg.TriangleGLPathAutomorphism
import ASGinzburg.FiniteComponentAutomorphismProducts

/-! The actual vertex- and cut-preserving automorphism group of the
triangle path algebra is the product of its three arrow-space general
linear groups. Injectivity follows from actual path induction. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem trianglePathAutomorphism_path_image_eq
    (E F : triangle333.VertexCutPathAutomorphism k)
    (h : ∀ a : triangle333.Arrow,
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
          (triangle333.source a) (triangle333.target a)
          (triangle333.pathIdentityArrowReplacement k a) =
        CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F
          (triangle333.source a) (triangle333.target a)
          (triangle333.pathIdentityArrowReplacement k a))
    {i j : triangle333.Vertex} (p : triangle333.Path i j) :
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j
        (Finsupp.single p 1) =
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F i j
        (Finsupp.single p 1) := by
  induction p with
  | nil =>
    exact ((triangle333.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_id
      E.val (CutQuiver.VertexCutPathAutomorphism.fixes_vertex triangle333 k E) i).trans
      ((triangle333.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_id
        F.val (CutQuiver.VertexCutPathAutomorphism.fixes_vertex triangle333 k F) i).symm
  | @snoc j p a ha ih =>
    subst j
    have hp : triangle333.pathComp k (triangle333.pathIdentityArrowReplacement k a)
        (Finsupp.single p 1) = Finsupp.single (CutQuiver.Path.snoc p a rfl) 1 := by
      simp [CutQuiver.pathIdentityArrowReplacement, CutQuiver.pathComp_single,
        CutQuiver.Path.comp]
    rw [← hp]
    have hE := (triangle333.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp
      E.val (CutQuiver.VertexCutPathAutomorphism.fixes_vertex triangle333 k E)
      (Finsupp.single p 1) (triangle333.pathIdentityArrowReplacement k a)
    have hF := (triangle333.pathComponentAlgebra k).totalAlgEquivComponentLinearEquiv_comp
      F.val (CutQuiver.VertexCutPathAutomorphism.fixes_vertex triangle333 k F)
      (Finsupp.single p 1) (triangle333.pathIdentityArrowReplacement k a)
    change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E _ _
        (triangle333.pathComp k (triangle333.pathIdentityArrowReplacement k a)
          (Finsupp.single p 1)) = _ at hE
    change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F _ _
        (triangle333.pathComp k (triangle333.pathIdentityArrowReplacement k a)
          (Finsupp.single p 1)) = _ at hF
    rw [hE, hF]
    change triangle333.pathComp k
        (CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E _ _
          (triangle333.pathIdentityArrowReplacement k a))
        (CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E _ _
          (Finsupp.single p 1)) = _
    rw [h a, ih]
    rfl

theorem trianglePathAutomorphism_component_image_eq
    (E F : triangle333.VertexCutPathAutomorphism k)
    (h : ∀ a : triangle333.Arrow,
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
          (triangle333.source a) (triangle333.target a)
          (triangle333.pathIdentityArrowReplacement k a) =
        CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F
          (triangle333.source a) (triangle333.target a)
          (triangle333.pathIdentityArrowReplacement k a))
    (i j : triangle333.Vertex) (f : triangle333.PathComponent k i j) :
    CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E i j f =
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F i j f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add, ihf, ihg]
  | single p c =>
    simpa only [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] using
      congrArg (fun f => c • f) (trianglePathAutomorphism_path_image_eq k E F h p)

theorem trianglePathAutomorphism_eq_of_arrow_images
    (E F : triangle333.VertexCutPathAutomorphism k)
    (h : ∀ a : triangle333.Arrow,
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
          (triangle333.source a) (triangle333.target a)
          (triangle333.pathIdentityArrowReplacement k a) =
        CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F
          (triangle333.source a) (triangle333.target a)
          (triangle333.pathIdentityArrowReplacement k a)) : E = F := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  funext i j
  rw [← CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv_projection triangle333 k E,
    ← CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv_projection triangle333 k F]
  exact trianglePathAutomorphism_component_image_eq k E F h i j (x i j)

theorem trianglePathAutomorphismGLTriple_injective :
    Function.Injective (trianglePathAutomorphismGLTriple k) := by
  intro E F h
  have hc : ∀ (s : Fin 3) (b : ArrowSpace333 k),
      CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
          s (triangleEdgeTarget s) (triangleEdgeArrowEquiv k s b).val =
        CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F
          s (triangleEdgeTarget s) (triangleEdgeArrowEquiv k s b).val := by
    intro s b
    fin_cases s
    · change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
          0 1 (triangleXArrowEquiv k b).val =
        CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F
          0 1 (triangleXArrowEquiv k b).val
      rw [← trianglePathAutomorphismGLTriple_X_coordinates,
        ← trianglePathAutomorphismGLTriple_X_coordinates, h]
    · change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
          1 2 (triangleYArrowEquiv k b).val =
        CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F
          1 2 (triangleYArrowEquiv k b).val
      rw [← trianglePathAutomorphismGLTriple_Y_coordinates,
        ← trianglePathAutomorphismGLTriple_Y_coordinates, h]
    · change CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k E
          2 0 (triangleZArrowEquiv k b).val =
        CutQuiver.VertexCutPathAutomorphism.componentLinearEquiv triangle333 k F
          2 0 (triangleZArrowEquiv k b).val
      rw [← trianglePathAutomorphismGLTriple_Z_coordinates,
        ← trianglePathAutomorphismGLTriple_Z_coordinates, h]
  apply trianglePathAutomorphism_eq_of_arrow_images k E F
  intro a
  rw [triangleIdentityArrow_coordinates]
  exact hc (triangle333.source a) (Pi.single (triangleGLArrowIndex a) 1)

theorem triangleGLPathAutomorphism_restriction
    (E : triangle333.VertexCutPathAutomorphism k) :
    triangleGLPathAutomorphism k (trianglePathAutomorphismGLTriple k E) = E :=
  trianglePathAutomorphismGLTriple_injective k
    (trianglePathAutomorphismGLTriple_extension k (trianglePathAutomorphismGLTriple k E))

noncomputable def trianglePathAutomorphismGLEquiv :
    triangle333.VertexCutPathAutomorphism k ≃* TriangleGL333 k where
  toFun := trianglePathAutomorphismGLTriple k
  invFun := triangleGLPathAutomorphism k
  left_inv := triangleGLPathAutomorphism_restriction k
  right_inv := trianglePathAutomorphismGLTriple_extension k
  map_mul' := trianglePathAutomorphismGLTriple_mul k

@[simp] theorem trianglePathAutomorphismGLEquiv_apply
    (E : triangle333.VertexCutPathAutomorphism k) :
    trianglePathAutomorphismGLEquiv k E = trianglePathAutomorphismGLTriple k E := rfl

@[simp] theorem trianglePathAutomorphismGLEquiv_symm_apply (g : TriangleGL333 k) :
    (trianglePathAutomorphismGLEquiv k).symm g = triangleGLPathAutomorphism k g := rfl

end ASGinzburg
