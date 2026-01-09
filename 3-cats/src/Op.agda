module Op where

open import Category
open import Relation.Binary.PropositionalEquality

open Cat

Op : Cat → Cat
Op C .Obj = C .Obj
Op C .Hom A B = C .Hom B A
Op C .id = C .id
Op C ._⊚_ g f = f C.⊚ g
  where open module C = Cat C
Op C .id-left-law = C .id-right-law
Op C .id-right-law = C .id-left-law
Op C .comp-law = sym (C .comp-law)

