module SET.Sum where

open import Category
open import SET
open import Sum
open import Data.Sum
open import Data.Sum.Properties
open import Relation.Binary.PropositionalEquality

open Cat
open IsSum

sum : ∀ {A B : Set} → IsSum SET A B (A ⊎ B)
sum .ι₁ = inj₁
sum .ι₂ = inj₂
sum ._∇_ = [_,_]
sum .inj-left = refl
sum .inj-right = refl
sum .inj-unique h = ext (λ where
  (inj₁ x) → refl
  (inj₂ y) → refl)
