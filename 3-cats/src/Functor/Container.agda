{-# OPTIONS --type-in-type #-}

module Functor.Container where

open import Function
open import Data.Product
open import Category
open import Functor
open import SET
open import Relation.Binary.PropositionalEquality

record Container : Set where
  field
    Shape : Set
    Position : Shape → Set

open Container

⟦_⟧ : Container → Set → Set
⟦ c ⟧ X = Σ (Shape c) (λ sh → Position c sh → X)

open FUNCTOR
open Cat

SETFunctor : Container → EndoFunctor SET
SETFunctor c .act = ⟦ c ⟧
SETFunctor c .fmap f (sh , ps) = sh , f ∘ ps
SETFunctor c .id-law = ext (λ x → refl)
SETFunctor c .homomorphism-law = ext λ x → refl
