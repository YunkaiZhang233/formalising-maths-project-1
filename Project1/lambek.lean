import Mathlib.Tactic

set_option autoImplicit false

-- section Initial
-- open CategoryTheory

-- universe u'
-- universe v'
-- variable {C : Type u'} [Category.{v'} C]

-- class InitialObject (X : C) : Prop where
--   unique_morphism : ∀ (Y : C), ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g

-- end Initial


namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

structure FAlgebra (F : C ⥤ C) where
  /-- carrier -/
  carrier : C
  /-- the arrow -/
  mor : F.obj carrier ⟶ carrier

namespace FAlgebra

local notation:80 g " ⊚ " f:80 => f ≫ g    -- type as \oo


variable {F : C ⥤ C} -- (A : FAlgebra F){B C : FAlgebra F}

/-- Define that all F-Algebra form a category.
This include components:
* homomorphisms: `h : (A, α) ⟶ (B, β)` is essentially an arrow `h : A ⟶ B`
  such that `h ∘ α = β ∘ F (h)`
* identities: identity arrows

```
         F h
   F A -----> F B
    |         |
  α |         | β
    V         V
    A  -----> B
        h
```
-/

structure AlgebraHom (A B : FAlgebra F) where
  -- mathching carrier
  h : A.carrier ⟶ B.carrier
  --
  condition : h ⊚ A.mor = B.mor ⊚ (F.map h)

variable (A : FAlgebra F){A' B' C': FAlgebra F}


namespace AlgebraHom

def id : AlgebraHom A A where
  h := 𝟙 _
  condition := by
    aesop

def comp (m1: AlgebraHom A' B') (m2: AlgebraHom B' C') : AlgebraHom A' C' where
  h := m2.h ⊚ m1.h
  condition := by
    simp [Functor.map_comp]
    rw [← m2.condition]
    simp [← Category.assoc]
    rw [m1.condition]

end AlgebraHom

instance (F : C ⥤ C) : CategoryStruct (FAlgebra F) where
  Hom := AlgebraHom
  id := AlgebraHom.id -- (X : FAlgebra F) → X ⟶ X
  comp := AlgebraHom.comp -- {X Y Z : FAlgebra F} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
--

-- theorem hom_isIso ()

/--
Given any endofunctor F : C → C on an arbitrary category C,
if i : F(I) → I is an initial F-algebra,
then i is an isomorphism.

isomorphism:IsIso

CategoryTheory.IsIso

given: F : C ==> C
given: i : IsInitial I in (Category of F-Algebra)
to show: IsIso i in (Category of F-Algebra)

-/

def placeholder : Prop := sorry

end FAlgebra

end CategoryTheory
