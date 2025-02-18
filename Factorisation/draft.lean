import Mathlib.CategoryTheory.Category.Factorisation
import Mathlib.CategoryTheory.Comma.Over

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y : C}

variable (f : X ⟶ Y)

-- variable (samplefact : Factorisation f)

-- def factmapped : Under X := Under.mk (samplefact.ι)

def fInOver : Over Y := Over.mk f

def fInUnder : Under X := Under.mk f

variable (f1 f2 : Factorisation f)
variable (f12 : f1 ⟶ f2)

def midf := Factorisation.Hom f1 f2

def init1 : Under.mk f1.ι ⟶ (fInUnder f) := Under.homMk f1.π
abbrev ff1 := Over.mk (Under.homMk f1.π : Under.mk f1.ι ⟶ Under.mk f)
abbrev ff2 := Over.mk (Under.homMk f2.π : Under.mk f2.ι ⟶ Under.mk f)
example := (ff1 f f1).left
example := (ff1 f f1).left.hom
example := (ff1 f f1).left.right
example := (ff2 f f2).left.hom
example := (ff2 f f2).hom.left
example := (ff2 f f2).left
def innerf1to2 : (ff1 f f1).left ⟶ (ff2 f f2).left := Under.homMk f12.h (f12.ι_h)

-- def f1to2 : (ff1 f f1) ⟶ (ff2 f f2) :=
--   Over.homMk (Under.homMk f12.h (f12.ι_h)) (by sorry)

def from_fact : Factorisation f ⥤ Over (Under.mk f) where
  obj α := Over.mk (Under.homMk α.π : Under.mk α.ι ⟶ Under.mk f)
  map κ := Over.homMk (Under.homMk κ.h κ.ι_h) (Under.UnderMorphism.ext (by simp))

example {β : Over (Under.mk f)} : β.left.right ⟶ Y := β.hom.right

variable (u1 u2 : Over (Under.mk f))
variable (u12 : u1 ⟶ u2)
example := u1.left
-- example : (Factorisation)
abbrev obj_to_fact (α : Over (Under.mk f)) : Factorisation f := { mid := α.left.right, ι := α.left.hom, π := α.hom.right }
example := u12.left.right
-- example : obj_to_fact f u1 ⟶ obj_to_fact f u2 := u12.left

def make_under_map (α : Over (Under.mk f)) (β : Over (Under.mk f)) (κ : α ⟶ β) :
    κ.left.right ≫ β.hom.right = α.hom.right := by
  rw [← Under.comp_right, Over.w]

def to_fact : Over (Under.mk f) ⥤ Factorisation f where
  obj α           := { mid := α.left.right, ι := α.left.hom, π := α.hom.right }
  map {α₁} {α₂} κ := {
    h := κ.left.right, ι_h := Under.w κ.left, h_π := by (rw [← Under.comp_right, Over.w])
  }

  -- ≅ : hom x to y, inv y to x, hom_inv_id: hom ≫ inv = 𝟙 X, inv_hom_id : inv ≫ hom = 𝟙 Y

-- the left square commute: Fact f ≌ (x / C) / f
def factEqUnderOfOver : Factorisation f ≌ Over (Under.mk f) where
  functor := from_fact f
  inverse := to_fact f
  unitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 g -- ⋙
    inv := 𝟙 g
  } )
  counitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 (to_fact f ⋙ from_fact f).obj g
    inv := 𝟙 (to_fact f ⋙ from_fact f).obj g
  })

-- def factToUnderOfOver : Factorisation f ⥤ Under (Over.mk f) where
--   obj := sorry
--   map := sorry

-- def underOfOverToFact : Under (Over.mk f) ⥤ Factorisation f where
--   obj := sorry
--   map := sorry

-- -- the right square commute: Fact f ≌ f / (C / y)
-- def factEqOverOfUnder : Factorisation f ≌ Under (Over.mk f) where
--   functor := factToUnderOfOver f
--   inverse := underOfOverToFact f
--   unitIso := sorry
--   counitIso := sorry

end CategoryTheory
