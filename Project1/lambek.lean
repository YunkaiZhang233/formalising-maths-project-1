import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

set_option autoImplicit false

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

@[ext]
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

def equiv_hom (m1: AlgebraHom A' B') (m2: AlgebraHom A' B') : Prop
  := (m1.h = m2.h) → m1 = m2

end AlgebraHom

instance (F : C ⥤ C) : CategoryStruct (FAlgebra F) where
  Hom := AlgebraHom
  id := AlgebraHom.id -- (X : FAlgebra F) → X ⟶ X
  comp := @AlgebraHom.comp _ _ _ -- {X Y Z : FAlgebra F} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
--

@[ext]
lemma ext {A B : FAlgebra F} {f g : A ⟶ B} (w : f.h = g.h) : f = g :=
  AlgebraHom.ext w

theorem comp_distr {f : B' ⟶ C'}{g : A' ⟶ B'} : (f ⊚ g).h = f.h ⊚ g.h := by
  rfl

theorem id_distr {A : FAlgebra F}: (𝟙 _ : A ⟶ A).h = 𝟙 A.carrier := by
  rfl


instance (F : C ⥤ C) : Category (FAlgebra F) := {
  --  ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  id_comp := by
    intros X Y f
    ext
    rw [comp_distr, id_distr, Category.id_comp]
  -- ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  comp_id := by
    intros X Y f
    ext
    rw [comp_distr, id_distr, Category.comp_id]
  -- Composition in a category is associative.
  assoc := by
    intros W X Y Z f g h
    ext
    simp [comp_distr]
}


namespace Initial
  -- initial algebra
  variable {I} (hInit : @Limits.IsInitial (FAlgebra F) _ I)

  def i_to_fi :=
    (hInit.to ⟨F.obj I.carrier, F.map I.mor⟩)


  def i_to_i_alg_hom : I ⟶ I where
    h := (i_to_fi hInit).h ≫ I.mor
    condition:= by
      rw [← Category.assoc, F.map_comp, i_to_fi, ← AlgebraHom.condition]

  lemma is_inv_1 : I.mor ⊚ (i_to_fi hInit).h = 𝟙 I.carrier := by
    have h1 : i_to_i_alg_hom hInit = 𝟙 I :=
      Limits.IsInitial.hom_ext hInit _ (𝟙 I)
    have h2 : (i_to_i_alg_hom hInit).h = 𝟙 I.carrier :=
      congr_arg AlgebraHom.h h1
    rw [← h2]
    unfold i_to_i_alg_hom
    simp

  lemma is_inv_2 : (i_to_fi hInit).h ⊚ I.mor = 𝟙 _ := by
    unfold i_to_fi
    rw [(hInit.to ⟨F.obj I.carrier, F.map I.mor⟩).condition, ← F.map_id, ← F.map_comp]
    congr
    apply is_inv_1 hInit

  theorem lambek (hInitial : Limits.IsInitial I) : IsIso I.mor := {
    /- define the inverse:
    out : ∃ inv : Y ⟶ X, (f ≫ inv = 𝟙 X) ∧ (inv ≫ f = 𝟙 Y)
    for the existence of the inverse morphism
    -/
    out := ⟨ (i_to_fi hInitial).h, is_inv_2 hInitial , is_inv_1 hInitial ⟩
  }

end Initial


end FAlgebra

end CategoryTheory
