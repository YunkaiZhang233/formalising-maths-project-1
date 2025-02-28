import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Tactic

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

@[ext]
structure Factorisation {X Y : C} (f : X ⟶ Y) where
  mid : C
  ι : X ⟶ mid
  π : mid ⟶ Y
  ι_π : ι ≫ π = f := by aesop_cat

attribute [simp] Factorisation.ι_π

-- to show: Fact f actually forms a category

namespace Factorisation

variable {X Y : C} {f : X ⟶ Y}

@[ext]
protected structure Hom (g₁ g₂ : Factorisation f) : Type (max u v) where
  h : g₁.mid ⟶ g₂.mid
  ι_h : g₁.ι ≫ h = g₂.ι := by aesop_cat
  h_π : h ≫ g₂.π = g₁.π := by aesop_cat

attribute [simp] Factorisation.Hom.ι_h Factorisation.Hom.h_π

@[simp]
protected def Hom.id (g : Factorisation f) : Factorisation.Hom g g where
  h := 𝟙 g.mid

@[simp]
def Hom.comp {g₁ g₂ g₃ : Factorisation f}
    (t₁ : Factorisation.Hom g₁ g₂) (t₂ : Factorisation.Hom g₂ g₃) : Factorisation.Hom g₁ g₃ where
  h := t₁.h ≫ t₂.h
  ι_h := by rw [← Category.assoc, t₁.ι_h, t₂.ι_h]
  h_π := by rw [Category.assoc, t₂.h_π, t₁.h_π]

-- to show: factorisation of a morphism form a category
instance : Category (Factorisation f) where
  Hom s t := Factorisation.Hom s t
  id x := Factorisation.Hom.id x
  comp g h := Factorisation.Hom.comp g h

namespace IteratedSlices

variable (f : X ⟶ Y)

namespace OverOfUnder

def fromFact : Factorisation f ⥤ Over (Under.mk f) where
  obj α := Over.mk (Under.homMk α.π : Under.mk α.ι ⟶ Under.mk f)
  map κ := Over.homMk (Under.homMk κ.h κ.ι_h) (Under.UnderMorphism.ext (by simp))

def toFact : Over (Under.mk f) ⥤ Factorisation f where
  obj α := {
    mid := α.left.right,
    ι := α.left.hom,
    π := α.hom.right
  }
  map κ := {
    h := κ.left.right,
    ι_h := Under.w κ.left,
    h_π := by (rw [← Under.comp_right, Over.w])
  }

def factEqOverOfUnder : Factorisation f ≌ Over (Under.mk f) where
  functor := fromFact f
  inverse := toFact f
  unitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 g
    inv := 𝟙 g
  })
  counitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 (toFact f ⋙ fromFact f).obj g
    inv := 𝟙 (toFact f ⋙ fromFact f).obj g
  })

end OverOfUnder

namespace UnderOfOver

def fromFact : Factorisation f ⥤ Under (Over.mk f) where
  obj α := Under.mk (Over.homMk α.ι : Over.mk f ⟶ Over.mk α.π)
  map κ := Under.homMk (Over.homMk κ.h κ.h_π) (Over.OverMorphism.ext (by simp))

def toFact : Under (Over.mk f) ⥤ Factorisation f where
  obj α := { mid := α.right.left, ι := α.hom.left, π := α.right.hom}
  map κ := {h := κ.right.left, ι_h := by (rw [← Over.comp_left, Under.w]), h_π := Over.w κ.right}

def factEqUnderOfOver : Factorisation f ≌ Under (Over.mk f) where
  functor := fromFact f
  inverse := toFact f
  unitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 g
    inv := 𝟙 g
  })
  counitIso := NatIso.ofComponents (fun g => {
    hom := 𝟙 (toFact f ⋙ fromFact f).obj g
    inv := 𝟙 (toFact f ⋙ fromFact f).obj g
  })

end UnderOfOver

end IteratedSlices

end Factorisation


end CategoryTheory
