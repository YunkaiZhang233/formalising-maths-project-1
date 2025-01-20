import Mathlib.Tactic

set_option autoImplicit false

-- namespace Initial
open CategoryTheory

universe u'
universe v'
variable {C : Type u'} [Category.{v'} C]

class InitialObject (X : C) : Prop where
  unique_morphism : ∀ (Y : C), ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g

-- end Initial


universe u
universe v

variable {C : Type u} [Category.{v} C]

structure FAlgebra (F : C ⥤ C) where
  /-- carrier -/
  carrier : C
  /-- the arrow -/
  mor : F.obj carrier ⟶ carrier
