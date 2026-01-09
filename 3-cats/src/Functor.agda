{-# OPTIONS --type-in-type #-}

module Functor where

open import Category
open Cat
open import Relation.Binary.PropositionalEquality

record FUNCTOR (C₁ C₂ : Cat) : Set where
  field
    act : C₁ .Obj → C₂ .Obj
    fmap : ∀ {X Y}
         → C₁ .Hom X Y
         → C₂ .Hom (act X) (act Y)

    id-law
      : ∀ {X} → fmap (C₁ .id {X}) ≡ C₂ .id {act X}
    homomorphism-law
      : ∀ {X Y Z} {f : C₁ .Hom X Y} {g : C₁ .Hom Y Z}
      → fmap (C₁ ._⊚_ g f) ≡ C₂ ._⊚_ (fmap g) (fmap f)

EndoFunctor : Cat → Set
EndoFunctor C = FUNCTOR C C
