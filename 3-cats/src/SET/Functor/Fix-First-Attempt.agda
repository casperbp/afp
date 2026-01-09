{-# OPTIONS --type-in-type #-}

module SET.Functor.Fix-First-Attempt where

open import Function

open import Category
open import SET
open import Functor
open import Functor.Algebra

open import Relation.Binary.PropositionalEquality

open import Data.Sum renaming ([_,_] to _∇_)
open import Data.Product

open import Function.Bundles

open FUNCTOR

{-# NO_POSITIVITY_CHECK #-}
data μ (F : EndoFunctor SET) : Set where
  ⟨_⟩ : F .act (μ F) → μ F

open Alg

{-# TERMINATING #-}
fold : ∀ {F : EndoFunctor SET} (A : Alg SET F) → μ F → A .carrier
fold {F} A ⟨ x ⟩ = A .alg (F .fmap (fold A) x)



{-

We need positivity checking for Agda to be consistent.

Here is a proof that non-strict positivity breaks for impredicative types.
That is, it is exploiting the (unsafe) --type-in-type flag.

-}

Bad : EndoFunctor SET
Bad .act X = (X → Set) → Set
Bad .fmap f g b = g (b ∘ f)
Bad .id-law = ext (λ x → ext (λ x₁ → refl))
Bad .homomorphism-law = ext (λ x → refl)

-- A diagonal (Coquand–Paulin / Cantor/Russell style), ported to μ Bad
------------------------------------------------------------------------

-- Inspired by https://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/

A : Set
A = μ Bad

-- i : X → (X → Set), x ↦ (λ y → x ≡ y)
i : {X : Set} → X → (X → Set)
i x y = x ≡ y

-- injectivity of i (needs extensionality to interpret equality of predicates)
i-injective : {X : Set} {x x' : X} → i x ≡ i x' → x ≡ x'
i-injective {X} {x} {x'} eq =
  -- Apply both sides to x, so we get (x ≡ x) ≡ (x' ≡ x),
  -- then transport refl : x ≡ x across that equality to obtain x' ≡ x,
  -- then symmetry to get x ≡ x'.
  let
    -- specialize predicate equality at x
    hx : i x x ≡ i x' x
    hx = cong (λ p → p x) eq

    -- hx has type (x ≡ x) ≡ (x' ≡ x)
    -- rewrite refl along hx to get a proof of x' ≡ x
    px' : x' ≡ x
    px' = subst id hx refl
  in sym px'

-- f : (A → Set) → A, P ↦ ⟨ i P ⟩
f : (A → Set) → A
f P = ⟨ i P ⟩

⟨⟩-injective : ∀ {F : EndoFunctor SET} (x y : F .act (μ F)) → ⟨_⟩ {F = F} x ≡ ⟨ y ⟩ → x ≡ y
⟨⟩-injective _ _ refl = refl

f-injective : {P Q : A → Set} → f P ≡ f Q → P ≡ Q
f-injective {P} {Q} eq = i-injective (⟨⟩-injective _ _ eq)

-- P0 x := ∃ P, f P ≡ x ∧ ¬ (P x)
P0 : A → Set
P0 x = Σ (A → Set) (λ P → (f P ≡ x) × (P x → ⊥))

x0 : A
x0 = f P0

-- The key diagonal equivalence: P0 x0 ↔ ¬ P0 x0
record _iff_ (P Q : Set) : Set where
  constructor intro
  field
    to   : P → Q
    from : Q → P
open _iff_

bad : P0 x0 iff (P0 x0 → ⊥)
bad = intro forward backward
  where
    forward : P0 x0 → (P0 x0 → ⊥)
    forward (P , (fx0 , notPx0)) px0 =
      -- From fx0 : f P ≡ x0, and x0 = f P0 by definition,
      -- conclude P ≡ P0, then contradict notPx0 using px0.
      let
        Peq : P ≡ P0
        Peq = f-injective fx0

        -- transport px0 : P0 x0 to P x0 using Peq, then contradict
        px0' : P x0
        px0' = subst (λ P → P x0) (sym Peq) px0
      in notPx0 px0'

    backward : (P0 x0 → ⊥) → P0 x0
    backward notPx0 =
      -- witness P0 itself, with f P0 ≡ x0 and ¬(P0 x0) as the negated membership
      (P0 , (refl , notPx0))

contra-from-iff-not : ∀ {P : Set} → (P iff (P → ⊥)) → ⊥
contra-from-iff-not {P} i =
  let
    notP : P → ⊥
    notP p = (to i p) p      -- uses P → ¬P to refute p

    p : P
    p = from i notP          -- uses ¬P → P to obtain P
  in
    notP p

contradiction : ⊥
contradiction = contra-from-iff-not bad


{-

Some exploration ...

-}

-- data Bool : Set where true false : Bool

-- not : Bool → Bool
-- not true = false ; not false = true

-- Power : EndoFunctor SET
-- Power .act X = X → Set
-- Power .fmap {X} {Y} f P y = Σ X (λ x → f x ≡ y × P x)
-- Power .id-law = ext (λ P → ext (λ x → {!!}))
-- Power .homomorphism-law = ext (λ P → ext (λ z → {!!}))

-- Surj : {A B : Set} → (A → B) → Set
-- Surj {A} {B} f = (b : B) → Σ A (λ a → f a ≡ b)

-- -- Cantor: no surjection A → (A → 𝟚)
-- no-surj-to-preds : {A : Set} → (Σ (A → (A → Bool)) (λ e → Surj e)) → ⊥
-- no-surj-to-preds {A} (e , surj) =
--   contra
--   where
--     d : A → Bool
--     d a = not (e a a)

--     a₀ : A
--     a₀ = proj₁ (surj d)

--     eq : e a₀ ≡ d
--     eq = proj₂ (surj d)

--     eq-at : e a₀ a₀ ≡ d a₀
--     eq-at = cong (λ p → p a₀) eq

--     -- d a₀ = not (e a₀ a₀), so eq-at says x ≡ not x, impossible
--     contra : ⊥
--     contra with e a₀ a₀ | eq-at
--     ... | true | ()
--     ... | false | ()


-- F₂ : Set
-- F₂ = (A → Bool) → Bool

-- postulate
--   out    : A → F₂
--   select : F₂ → (A → Bool)

--   -- This says: every predicate p is represented by some a via select(out a)
--   select-surj : Surj (λ a → select (out a))

-- Bad′ : EndoFunctor SET
-- Bad′ .act X = (X → Bool) → Bool
-- Bad′ .fmap f g h = g (h ∘ f)
-- Bad′ .id-law = refl
-- Bad′ .homomorphism-law = refl

-- select′ : ((μ Bad′ → Bool) → Bool) → (μ Bad′ → Bool)
-- select′ f = {!!}

-- boom : ⊥
-- boom = no-surj-to-preds ((λ a → select (out a)) , select-surj)

-- -- Bad′ : EndoFunctor SET
-- -- Bad′ .act X = (X → ⊤) → X
-- -- Bad′ .fmap f g h = f (g (λ x → h (f x)))
-- -- Bad′ .id-law = refl
-- -- Bad′ .homomorphism-law = refl

-- -- x : μ Bad′
-- -- x = {!!}


-- -- -- b : ⊥
-- -- -- b = let r = fold {F = Bad′} (record { carrier = ⊥ ; alg = λ k → k ⊥ (inj₁ id) }) ⟨ (λ where
-- -- --   R (inj₁ x) → x {!!}
-- -- --   R (inj₂ y) → y) ⟩ in {!!}

-- -- b′ : μ Bad′ → ⊥
-- -- b′ = fold {Bad′} (record { carrier = ⊥
-- --                          ; alg = λ k → k (λ ()) })


-- -- -- bbb : μ Bad′
-- -- -- bbb = ⟨ (λ where
-- -- --   R (inj₁ x) → x {!!}
-- -- --   R (inj₂ y) → y) ⟩
