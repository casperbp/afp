{-# OPTIONS --type-in-type #-}

module SET.Functor.Fix-Second-Attempt where

open import Function

open import Functor.Container -- !

open import Category
open import SET
open import Functor
open import Functor.Algebra

open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

open import Data.Sum renaming ([_,_] to _∇_)
open import Data.Product

open import Function.Bundles

open FUNCTOR

data μ (c : Container) : Set where
  ⟨_⟩ : CFunctor c .act (μ c) → μ c

open Alg

μAlg : (c : Container) → Alg SET (CFunctor c)
μAlg c .carrier = μ c
μAlg c .alg     = ⟨_⟩

fold : ∀ {c : Container} (A : Alg SET (CFunctor c)) → μ c → A .carrier
fold {c} A ⟨ sh , ps ⟩ = A .alg (sh , (fold A ∘ ps))

open AlgHom

foldHom : ∀ {c : Container} (A : Alg SET (CFunctor c)) → AlgHom (μAlg c) A
foldHom A .𝓯 = fold A
foldHom {c} A .comm = refl

fold-unique-pointwise
  : {c : Container} {A : Alg SET (CFunctor c)}
    (h : AlgHom (μAlg c) A)
  → ∀ x → h .𝓯 x ≡ fold A x
fold-unique-pointwise {c} {A} h (⟨ sh , ps ⟩) =
  -- use the homomorphism law h.comm at (sh , ps)
  -- h.𝓯 (⟨ sh , ps ⟩)
  --   ≡ A.alg (sh , h.𝓯 ∘ ps)
  -- then rewrite recursively inside the function argument
  let
    -- from comm, instantiated on (sh , ps):
    step₀ : h .𝓯 (⟨ sh , ps ⟩) ≡ A .alg (sh , (h .𝓯 ∘ ps))
    step₀ = cong (λ f → f (sh , ps)) (h .comm)

    -- pointwise rewrite h.𝓯 ∘ ps to fold A ∘ ps
    step₁ : (h .𝓯 ∘ ps) ≡ (fold A ∘ ps)
    step₁ = ext (λ p → fold-unique-pointwise h (ps p))
  in
    begin
      h .𝓯 (⟨ sh , ps ⟩)
    ≡⟨ step₀ ⟩
      A .alg (sh , (h .𝓯 ∘ ps))
    ≡⟨ cong (A .alg ∘ (λ g → sh , g)) step₁ ⟩
      A .alg (sh , (fold A ∘ ps))
    ∎

fold-initial
  : {c : Container} (A : Alg SET (CFunctor c))
  → (h : AlgHom (μAlg c) A)
  → h ≡ foldHom A
fold-initial {c} A h =
  AlgHom-≡ h (foldHom A) (ext (fold-unique-pointwise h))

open IsInitial

μAlg-initial : ∀ (c : Container) → IsInitial (FAlgCat SET (CFunctor c)) (μAlg c)
μAlg-initial c .! {A} = foldHom A
μAlg-initial c .uniq {A} = fold-initial A

