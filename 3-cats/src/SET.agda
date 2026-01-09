{-# OPTIONS --type-in-type #-}

module SET where

open import Level
open import Function as F
open import Category
open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional

SET : Cat
SET .Cat.Obj = Set
SET .Cat.Hom A B = A → B
SET .Cat.id = F.id
SET .Cat._⊚_ g f = g ∘ f
SET .Cat.id-left-law = refl
SET .Cat.id-right-law = refl
SET .Cat.comp-law = refl

data ⊥ : Set where
data ⊤ : Set where tt : ⊤

postulate ext : Extensionality zero zero

top : IsInitial SET ⊥
top .IsInitial.! ()
top .IsInitial.uniq f = ext (λ ())

top-≡ : (t₁ t₂ : ⊤) → t₁ ≡ t₂
top-≡ tt tt = refl

bot : IsTerminal SET ⊤
bot .IsTerminal.! _ = tt
bot .IsTerminal.uniq f = ext (λ x → top-≡ _ _)
