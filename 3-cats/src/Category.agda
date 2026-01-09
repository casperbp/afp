{-# OPTIONS --type-in-type #-}

module Category where

open import Relation.Binary.PropositionalEquality

record Cat : Set where
  field
    Obj : Set
    Hom : Obj → Obj → Set

    id   : ∀ {A} → Hom A A
    _⊚_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    id-left-law  : ∀ {A B} {f : Hom A B} → id ⊚ f ≡ f
    id-right-law : ∀ {A B} {f : Hom A B} → f ⊚ id ≡ f
    comp-law     : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D}
                 → (h ⊚ g) ⊚ f ≡ h ⊚ (g ⊚ f)


record IsInitial (C : Cat) (z : Cat.Obj C) : Set where
  open Cat C
  field
    !    : ∀ {A : Obj} → Hom z A
    uniq : ∀ {A : Obj} (f : Hom z A) → f ≡ !

record IsTerminal (C : Cat) (i : Cat.Obj C) : Set where
  open Cat C
  field
    !    : ∀ {A : Obj} → Hom A i
    uniq : ∀ {A : Obj} (f : Hom A i) → f ≡ !


