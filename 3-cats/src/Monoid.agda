{-# OPTIONS --type-in-type #-}

module Monoid where

open import Function
open import Category
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Binary.Pointwise as PW
open import Data.List.Relation.Binary.Prefix.Heterogeneous
open import Data.List.Relation.Binary.Prefix.Homogeneous.Properties as L
open import Data.Product
open import Relation.Binary.PropositionalEquality as E
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsDecPartialOrder)

open ≡-Reasoning

prefix-refl : ∀ {a} {A : Set a} (xs : List A) → Prefix _≡_ xs xs
prefix-refl xs =
  (L.isPreorder E.isPreorder) .IsPreorder.reflexive (PW.refl E.refl)

prefix-trans : ∀ {a} {A : Set a} {xs ys zs : List A}
              → Prefix _≡_ xs ys → Prefix _≡_ ys zs → Prefix _≡_ xs zs
prefix-trans =
  (L.isPreorder E.isPreorder) .IsPreorder.trans

prefix-proof-irrelevant :
  ∀ {A : Set} {xs ys : List A}
  → (p q : Prefix _≡_ xs ys) → p ≡ q
prefix-proof-irrelevant [] [] = E.refl
prefix-proof-irrelevant (E.refl ∷ p) (E.refl ∷ q) = cong (_ ∷_) (prefix-proof-irrelevant p q)

LIST : Set → Cat
LIST A .Cat.Obj = List A
LIST A .Cat.Hom = Prefix _≡_
LIST A .Cat.id = prefix-refl _
LIST A .Cat._⊚_ = flip prefix-trans
LIST A .Cat.id-left-law {f = f} = prefix-proof-irrelevant (prefix-trans f (prefix-refl _)) f
LIST A .Cat.id-right-law {xs} {f = f} = prefix-proof-irrelevant (prefix-trans (prefix-refl xs) f) f
LIST A .Cat.comp-law {f = f} {g} {h} = prefix-proof-irrelevant
  (prefix-trans f (prefix-trans g h))
  (prefix-trans (prefix-trans f g) h)


