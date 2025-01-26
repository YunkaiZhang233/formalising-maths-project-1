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

-- Composition of homomorphisms between algebras
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


/- We need to show that
  All F-Algebras form a category
-/
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


/-
  The idea of the proof:

  ```
         F f           F (i)
   F I -----> F (F I) -------> F (I)
    |         |                 |
  i |         | F(i)            | i
    V         V                 V
    I  -----> F I ------------> I
        f             i
```
Given `I` is the initial object in the category of algebras on endofunctors:

`f` is the unique arrow from Algebra of (F I --i--> I)
to Algebra of (F (F I) --F (i)--> F I)

so `i ⊚ f` constitutes an arrow from I to I.

However, by I being the initial object, there is one unique arrow from I to I,
which is the identity arrow. Therefore, `i ⊚ f = id_I`

With this in mind, as the left swuare commutes: we have

```
f ⊚ i = F (i) ⊚ F (f)
      = F (i ⊚ f)
      = F (id_I)
      = id_(F (I))
```

-/
namespace Initial
  -- initial algebra
  variable {I} (hInit : @Limits.IsInitial (FAlgebra F) _ I)

  def i_to_fi :=
    (hInit.to ⟨F.obj I.carrier, F.map I.mor⟩)


  /-
    Construct the homomorphism from Algebra (I, i) to (I, i),
    which is formed by composing the homomorphism from (I, i) to (F(I), F(i))
    and the homomorphism from (F(I), F(i)) to (I, i)
  -/
  def i_to_i_alg_hom : I ⟶ I where
    h := (i_to_fi hInit).h ≫ I.mor
    condition:= by
      rw [← Category.assoc, F.map_comp, i_to_fi, ← AlgebraHom.condition]

  /- i ⊚ f = id_I -/
  lemma is_inv_1 : I.mor ⊚ (i_to_fi hInit).h = 𝟙 I.carrier := by
    have h1 : i_to_i_alg_hom hInit = 𝟙 I :=
      Limits.IsInitial.hom_ext hInit _ (𝟙 I)
    have h2 : (i_to_i_alg_hom hInit).h = 𝟙 I.carrier :=
      congr_arg AlgebraHom.h h1
    rw [← h2]
    unfold i_to_i_alg_hom
    simp

  /- f ⊚ I = id_F(I) -/
  lemma is_inv_2 : (i_to_fi hInit).h ⊚ I.mor = 𝟙 (F.obj I.carrier) := by
    unfold i_to_fi
    rw [(hInit.to ⟨F.obj I.carrier, F.map I.mor⟩).condition, ← F.map_id, ← F.map_comp]
    congr
    apply is_inv_1 hInit

  /-
    Lambek's Lemma:
    if Algebra I : F (i) --i--> I is an initial F-algebra,
    Then i is an isomorphism, with F (I) ≅ I
  -/
  theorem lambek (hInitial : Limits.IsInitial I) : IsIso I.mor := {
    out := ⟨ (i_to_fi hInitial).h, is_inv_2 hInitial , is_inv_1 hInitial ⟩
  }

end Initial


end FAlgebra

end CategoryTheory
