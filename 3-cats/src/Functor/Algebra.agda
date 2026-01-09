module Functor.Algebra where

open import Category
open import Functor
open import Relation.Binary.PropositionalEquality

open import Axiom.UniquenessOfIdentityProofs

postulate uip : ∀ {A : Set} → UIP A

open ≡-Reasoning

record Alg (C : Cat) (F : EndoFunctor C) : Set where
  private module C = Cat C
          module F = FUNCTOR F
  field
    carrier : C.Obj
    alg     : C.Hom (F.act carrier) carrier


record AlgHom {C : Cat} {F : EndoFunctor C}
              (A B : Alg C F) : Set where
  constructor AH
  private module A = Alg A
          module B = Alg B
          module C = Cat C
          module F = FUNCTOR F

  field
    𝓯 : C.Hom A.carrier B.carrier
    comm : (𝓯 C.⊚ A.alg) ≡ (B.alg C.⊚ F.fmap 𝓯)

open Alg
open AlgHom
open Cat
open FUNCTOR

AlgHom-id : ∀ {C F} {A : Alg C F} → AlgHom A A
AlgHom-id {C = C} .𝓯 = C .id
AlgHom-id {C = C} {F} {A} .comm = begin
    C.id C.⊚ A .alg
  ≡⟨ C.id-left-law ⟩
    A .alg
  ≡⟨ sym C.id-right-law ⟩
    A .alg C.⊚ C.id
  ≡⟨ cong (_ C.⊚_) (sym (F .id-law)) ⟩
    A .alg C.⊚ (F .fmap C.id)
  ∎
  where module C = Cat C

AlgHom-comp : ∀ {C F} {A B C : Alg C F}
            → AlgHom B C → AlgHom A B → AlgHom A C
AlgHom-comp {C} h₂ h₁ .𝓯 = h₂ .𝓯 C.⊚ h₁ .𝓯
  where module C = Cat C
AlgHom-comp {C} {F} {A} {B} {D} h₂ h₁ .comm = begin
    (h₂ .𝓯 C.⊚ h₁ .𝓯) C.⊚ A .alg
  ≡⟨ C.comp-law ⟩
    h₂ .𝓯 C.⊚ (h₁ .𝓯 C.⊚ A .alg)
  ≡⟨ cong (h₂ .𝓯 C.⊚_) (h₁ .comm) ⟩
    h₂ .𝓯 C.⊚ (B .alg C.⊚ F .fmap (h₁ .𝓯))
  ≡⟨ sym C.comp-law ⟩
    (h₂ .𝓯 C.⊚ B .alg) C.⊚ F .fmap (h₁ .𝓯)
  ≡⟨ cong (C._⊚ _) (h₂ .comm) ⟩
    (D .alg C.⊚ F .fmap (h₂ .𝓯)) C.⊚ F .fmap (h₁ .𝓯)
  ≡⟨ C.comp-law ⟩
   D .alg C.⊚ (F .fmap (h₂ .𝓯) C.⊚ F .fmap (h₁ .𝓯))
  ≡⟨ cong (D .alg C.⊚_) (sym (F .homomorphism-law)) ⟩
    (D .alg C.⊚ F .fmap (h₂ .𝓯 C.⊚ h₁ .𝓯))
  ∎
  where module C = Cat C

AlgHom-≡
  : ∀ {C : Cat} {F : EndoFunctor C} {A B : Alg C F}
    (h k : AlgHom A B)
  → h .𝓯 ≡ k .𝓯
  → h ≡ k
AlgHom-≡ (AH 𝓯₁ comm₁) (AH 𝓯₂ comm₂) refl = cong (AH 𝓯₁) (uip comm₁ comm₂)

FAlgCat : (C : Cat) (F : EndoFunctor C) → Cat
FAlgCat C F .Obj = Alg C F
FAlgCat C F .Hom = AlgHom
FAlgCat C F .id = AlgHom-id
FAlgCat C F ._⊚_ = AlgHom-comp
FAlgCat C F .id-left-law {f = f} = AlgHom-≡ _ f (C .id-left-law)
FAlgCat C F .id-right-law {f = f} = AlgHom-≡ _ f (C .id-right-law)
FAlgCat C F .comp-law {f = f} = AlgHom-≡ _ _ (C .comp-law)

