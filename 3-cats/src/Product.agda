module Product where

open import Category
open import Relation.Binary.PropositionalEquality

open Cat

record IsProduct (C : Cat)
                 (A B P : C .Obj) : Set where
  private module C = Cat C                 
  field
    π₁ : C.Hom P A
    π₂ : C.Hom P B

    ⟨_,_⟩ : ∀ {X} → C.Hom X A → C.Hom X B → C.Hom X P

    proj-left : ∀ {X} {f : C.Hom X A} {g : C.Hom X B}
              → π₁ C.⊚ ⟨ f , g ⟩ ≡ f

    proj-right : ∀ {X} {f : C.Hom X A} {g : C.Hom X B}
               → π₂ C.⊚ ⟨ f , g ⟩ ≡ g

    prod-unique : ∀ {X} (h : C.Hom X P)
                → h ≡ ⟨ π₁ C.⊚ h , π₂ C.⊚ h ⟩
     
