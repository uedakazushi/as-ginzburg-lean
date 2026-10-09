import Mathlib.CategoryTheory.Iso

/-! Transport of an actual commuting square through its four object
isomorphisms. Used to assemble genuine homology maps into module maps. -/
namespace ASGinzburg
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

theorem isoTransport_naturality {Sx Sy Tx Ty Mx My Nx Ny : C}
    (eSx : Sx ≅ Mx) (eSy : Sy ≅ My) (eTx : Tx ≅ Nx) (eTy : Ty ≅ Ny)
    (fx : Sx ⟶ Tx) (fy : Sy ⟶ Ty)
    (hs : Sy ⟶ Sx) (ht : Ty ⟶ Tx) (m : My ⟶ Mx) (n : Ny ⟶ Nx)
    (hS : eSy.hom ≫ m=hs ≫ eSx.hom)
    (hT : eTy.hom ≫ n=ht ≫ eTx.hom)
    (hf : fy ≫ ht=hs ≫ fx) :
    m ≫ eSx.inv ≫ fx ≫ eTx.hom=eSy.inv ≫ fy ≫ eTy.hom ≫ n := by
  apply (cancel_epi eSy.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc eSy.hom m,hS,Category.assoc,Iso.hom_inv_id_assoc]
  rw [hT,← Category.assoc,← hf,Category.assoc]

end ASGinzburg
