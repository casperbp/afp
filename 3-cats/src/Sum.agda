module Sum where

open import Category
open import Relation.Binary.PropositionalEquality

open Cat

record IsSum (C : Cat)
             (A B S : C .Obj) : Set where
  private module C = Cat C                 
  field
    -- injections
    ι₁ : C.Hom A S
    ι₂ : C.Hom B S

    -- copairing / case analysis
    _∇_ : ∀ {X} → C.Hom A X → C.Hom B X → C.Hom S X

    -- β-laws (computational behavior)
    inj-left : ∀ {X} {f : C.Hom A X} {g : C.Hom B X}
             → (f ∇ g) C.⊚ ι₁ ≡ f

    inj-right :
      ∀ {X} {f : C.Hom A X} {g : C.Hom B X}
      → (f ∇ g) C.⊚ ι₂ ≡ g


    inj-unique :
      ∀ {X} (h : C.Hom S X)
      → h ≡ (h C.⊚ ι₁) ∇ (h C.⊚ ι₂)
