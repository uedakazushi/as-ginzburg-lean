import work.ASGinzburgDraft.GinzburgOriginalArrowSubstitution
import work.ASGinzburgDraft.GinzburgArrowSubstitutionGrading
import work.ASGinzburgDraft.TriangleGinzburgGLGenerators

/-! Genuine triangle GL replacements act by the original and
contragredient arrow matrices and have actual inverse path substitutions. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleGinzburgGLSubstitution_original (g : TriangleGL333 k)
    (i j : triangle333.Vertex) (f : triangle333.PathComponent k i j) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        i j (triangle333.originalGinzburgLinearMap k i j f) =
      triangle333.originalGinzburgLinearMap k i j
        (triangle333.pathArrowSubstitutionComponent k (triangleGLArrowReplacement k g) i j f) :=
  triangle333.ginzburgArrowSubstitutionComponent_original k
    (triangleGinzburgGLArrowReplacement k g) (triangleGLArrowReplacement k g)
    (fun _ => rfl) i j f

theorem triangleGinzburgGLSubstitution_originalCoordinates (g : TriangleGL333 k)
    (s : Fin 3) (b : ArrowSpace333 k) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        s (triangleEdgeTarget s) (triangleGinzburgOriginalCoordinates k s b) =
      triangleGinzburgOriginalCoordinates k s (triangleGLArrowMatrix k g s b) := by
  change triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
      s (triangleEdgeTarget s)
      (triangle333.originalGinzburgLinearMap k _ _ (triangleEdgeArrowEquiv k s b).val) =
    triangle333.originalGinzburgLinearMap k _ _
      (triangleEdgeArrowEquiv k s (triangleGLArrowMatrix k g s b)).val
  rw [triangleGinzburgGLSubstitution_original,triangleGLSubstitution_coordinates]

theorem triangleGinzburgGLSubstitution_dualCoordinates (g : TriangleGL333 k)
    (s : Fin 3) (b : ArrowSpace333 k) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        (triangleEdgeTarget s) s (triangleGinzburgDualCoordinates k s b) =
      triangleGinzburgDualCoordinates k s
        (triangleArrowContragredient k (triangleGLArrowMatrix k g s) b) := by
  have hSingle : ∀ i : Fin 3,
      triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
          (triangleEdgeTarget s) s (triangleGinzburgDualCoordinates k s (Pi.single i 1)) =
        triangleGinzburgDualCoordinates k s
          (triangleArrowContragredient k (triangleGLArrowMatrix k g s) (Pi.single i 1)) := by
    intro i
    rw [triangleGinzburgDualCoordinates_single]
    have hArrow := triangle333.ginzburgArrowSubstitutionComponent_arrow k
      (triangleGinzburgGLArrowReplacement k g) (.dual (triangleEdgeArrow s i))
    fin_cases s <;> fin_cases i <;>
      simpa [triangleEdgeDualGinzburgPath,triangleGinzburgGLArrowReplacement,
        triangleGLArrowMatrix,triangleGLArrowIndex,triangleEdgeArrow,triangleEdgeTarget,
        triangle333,CutQuiver.GinzburgPath.transport,CutQuiver.dualGinzburgArrowPath,
        CutQuiver.ginzburgArrowPath,CutQuiver.GinzburgArrow.source,CutQuiver.GinzburgArrow.target]
        using hArrow
  have hBasis : ∀ i : Fin 3,
      ((triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        (triangleEdgeTarget s) s).comp (triangleGinzburgDualCoordinates k s))
          (Pi.basisFun k (Fin 3) i) =
        ((triangleGinzburgDualCoordinates k s).comp
          (triangleArrowContragredient k (triangleGLArrowMatrix k g s)).toLinearMap)
          (Pi.basisFun k (Fin 3) i) := by
    intro i
    simpa only [Pi.basisFun_apply,LinearMap.comp_apply,LinearEquiv.coe_coe] using hSingle i
  let result := (Pi.basisFun k (Fin 3)).ext hBasis
  exact LinearMap.congr_fun result b

theorem triangleGinzburgIdentityArrow_dualCoordinates (a : triangle333.Arrow) :
    triangle333.ginzburgIdentityArrowReplacement k (.dual a) =
      triangleGinzburgDualCoordinates k (triangle333.source a)
        (Pi.single (triangleGLArrowIndex a) 1) := by
  rw [triangleGinzburgDualCoordinates_single]
  fin_cases a <;> rfl

theorem triangleGinzburgGLArrowReplacement_inverse (g : TriangleGL333 k)
    (a : triangle333.GinzburgArrow) :
    triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        (a.source triangle333) (a.target triangle333)
        (triangleGinzburgGLArrowReplacement k (g⁻¹) a) =
      triangle333.ginzburgIdentityArrowReplacement k a := by
  cases a with
  | original a =>
    change triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        (triangle333.source a) (triangle333.target a)
        (triangle333.originalGinzburgLinearMap k _ _ (triangleGLArrowReplacement k (g⁻¹) a)) = _
    rw [triangleGinzburgGLSubstitution_original,triangleGLArrowReplacement_inverse]
    simp [CutQuiver.pathIdentityArrowReplacement,CutQuiver.ginzburgIdentityArrowReplacement,
      CutQuiver.ginzburgArrowPath,CutQuiver.Path.originalGinzburg]
  | dual a =>
    change triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        (triangleEdgeTarget (triangle333.source a)) (triangle333.source a)
        (triangleGinzburgDualCoordinates k (triangle333.source a)
          (triangleArrowContragredient k (triangleGLArrowMatrix k (g⁻¹) (triangle333.source a))
            (Pi.single (triangleGLArrowIndex a) 1))) = _
    rw [triangleGinzburgGLSubstitution_dualCoordinates,triangleGLArrowMatrix_inv,
      triangleArrowContragredient_symm,LinearEquiv.apply_symm_apply]
    exact (triangleGinzburgIdentityArrow_dualCoordinates k a).symm
  | loop v =>
    change triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
      v v (Finsupp.single (triangle333.ginzburgArrowPath (.loop v)) 1) = _
    rw [CutQuiver.ginzburgArrowSubstitutionComponent_arrow]
    rfl

noncomputable def triangleGinzburgGLComponentEquiv (g : TriangleGL333 k)
    (i j : triangle333.Vertex) :
    triangle333.GinzburgPathComponent k i j ≃ₗ[k] triangle333.GinzburgPathComponent k i j :=
  triangle333.ginzburgArrowSubstitutionComponentEquiv k
    (triangleGinzburgGLArrowReplacement k g) (triangleGinzburgGLArrowReplacement k (g⁻¹))
    (triangleGinzburgGLArrowReplacement_inverse k g)
    (by intro a; simpa only [inv_inv] using triangleGinzburgGLArrowReplacement_inverse k (g⁻¹) a)
    i j

@[simp] theorem triangleGinzburgGLComponentEquiv_apply (g : TriangleGL333 k)
    (i j : triangle333.Vertex) (f : triangle333.GinzburgPathComponent k i j) :
    triangleGinzburgGLComponentEquiv k g i j f =
      triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g) i j f := rfl

@[simp] theorem triangleGinzburgGLComponentEquiv_symm_apply (g : TriangleGL333 k)
    (i j : triangle333.Vertex) (f : triangle333.GinzburgPathComponent k i j) :
    (triangleGinzburgGLComponentEquiv k g i j).symm f =
      triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k (g⁻¹))
        i j f := rfl

noncomputable def triangleGinzburgGLCohomologicalEquiv (g : TriangleGL333 k)
    (i j : triangle333.Vertex) (q : ℤ) :
    triangle333.ginzburgCohomologicalComponent k i j q ≃ₗ[k]
      triangle333.ginzburgCohomologicalComponent k i j q :=
  triangle333.ginzburgArrowSubstitutionCohomologicalEquiv k
    (triangleGinzburgGLArrowReplacement k g) (triangleGinzburgGLArrowReplacement k (g⁻¹))
    (triangleGinzburgGLArrowReplacement_inverse k g)
    (by intro a; simpa only [inv_inv] using triangleGinzburgGLArrowReplacement_inverse k (g⁻¹) a)
    (triangleGinzburgGLArrowReplacement_mem_cohomological k g)
    (triangleGinzburgGLArrowReplacement_mem_cohomological k (g⁻¹)) i j q

@[simp] theorem triangleGinzburgGLCohomologicalEquiv_coe (g : TriangleGL333 k)
    (i j : triangle333.Vertex) (q : ℤ) (f : triangle333.ginzburgCohomologicalComponent k i j q) :
    (triangleGinzburgGLCohomologicalEquiv k g i j q f).val =
      triangle333.ginzburgArrowSubstitutionComponent k (triangleGinzburgGLArrowReplacement k g)
        i j f.val := rfl

end ASGinzburg
