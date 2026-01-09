module SET.Product where

open import Category
open import SET
open import Product
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality

open Cat
open IsProduct

product : ∀ {A B : Set} → IsProduct SET A B (A × B)
product .π₁ = proj₁
product .π₂ = proj₂
product .⟨_,_⟩ f g x = f x , g x
product .proj-left = refl
product .proj-right = refl
product .prod-unique h = refl
