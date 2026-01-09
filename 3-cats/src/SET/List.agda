module SET.List where

open import Functor
open import SET
open import Data.List
open import Data.List.Properties

open FUNCTOR

List-Functor : FUNCTOR SET SET
List-Functor .act = List
List-Functor .fmap = map
List-Functor .id-law = ext map-id
List-Functor .homomorphism-law = ext map-∘

