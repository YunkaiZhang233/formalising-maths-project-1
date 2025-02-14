import Mathlib.CategoryTheory.Category.Factorisation
import Mathlib.CategoryTheory.Comma.Over

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y : C}

variable (f : X ⟶ Y)

def factToOverOfUnder : Factorisation f ⥤ Over (Under.mk f) where
  obj := sorry
  map := sorry

def overOfUnderToFact : Over (Under.mk f) ⥤ Factorisation f where
  obj := sorry
  map := sorry

-- the left square commute: Fact f ≌ (x / C) / f
def factEqUnderOfOver : Factorisation f ≌ Over (Under.mk f) where
  functor := factToOverOfUnder f
  inverse := overOfUnderToFact f
  unitIso := sorry
  counitIso := sorry

def factToUnderOfOver : Factorisation f ⥤ Under (Over.mk f) where
  obj := sorry
  map := sorry

def underOfOverToFact : Under (Over.mk f) ⥤ Factorisation f where
  obj := sorry
  map := sorry

-- the right square commute: Fact f ≌ f / (C / y)
def factEqOverOfUnder : Factorisation f ≌ Under (Over.mk f) where
  functor := factToUnderOfOver f
  inverse := underOfOverToFact f
  unitIso := sorry
  counitIso := sorry

end CategoryTheory
