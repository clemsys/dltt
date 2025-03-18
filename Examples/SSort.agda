{-# OPTIONS --cubical --no-termination-check #-}
module Examples.SSort where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Sum
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary

open import Core
open import Functions
open import Examples.List
open import Examples.Maybe
open import Examples.ListPartial
open import Examples.Order

open LinearTypes


private
  variable
    ℓ : Level

module _ {A : Type ℓ} where
-- insSnd : (x : A) (ys : A × List A) → η ys ⊗ η x ⊩ A × List A
  insSnd : A ⊸﹠ A × List A ⊸ A × List A
  insSnd x (y , ys) = ． (y , x ∷ ys) by prod where prod : η (y , ys) ⊗ η x ⧟ η (y , x ∷ ys)
                                                   prod = wk, ∘ id (η y) ⊗ᶠ wk∷ ∘ id (η y) ⊗ᶠ swap (η ys) (η x) ∘ assoc (η y) (η ys) (η x) ∘ cn, ⊗ᶠ id (η x)


module _ {A : Type ℓ} (_<_ : Rel A A _) (_≟_ : (x y : A) → Ord.compare _<_ x y) where
  open Ord.Total _<_ _≟_

-- getMin : (xs : A × List A) → η xs ⊩ A × List A
  getMin : A × List A ⊸ A × List A
  getMin (x , []) = ． (x , [])
  getMin (x , y ∷ xs) with y ≤? x
  ... | inl y≤x = insSnd x ＠ getMin (y , xs) by id (η x) ⊗ᶠ (wk, ∘ cn∷) ∘ cn,
  ... | inr x<y = insSnd y ＠ getMin (x , xs)
    by prod
    where prod = id (η y) ⊗ᶠ wk, ∘ assoc (η y) (η x) (η xs) ∘ swap (η x) (η y) ⊗ᶠ id (η xs) ∘ id (η x) ⊗ᶠ cn∷ ∘ cn,


  -- getMin : (x : A) (xs : List A) → η xs ⊗ η x ⊩ (A × List A)
  -- getMin x [] = ． (x , []) by {!!}
  -- getMin x (y ∷ xs) with y ≤? x
  -- ... | inl p = (λ (z , zs) →  ． (z , x ∷ xs) by {!!}) ＠ (getMin y xs) by id (η x) ⊗ᶠ swap (η y) (η xs) ∘ swap (η y ⊗ η xs) (η x) ∘ cn∷ ⊗ᶠ (id (η x))
  -- ... | inr p = {!!}


  ssort : List A ⊸ List A
  ssort = unfold₁ go where
    go : List A ⊸ Maybe (A × List A)
    go [] = nothing○ by cn[]
    go (x ∷ ys) = just○ ＠ getMin (x , ys) by wk, ∘ cn∷




open NatOrder

test : List ℕ
test = ssort _<_ _≟_ (6 ∷ 1 ∷ 23 ∷ 2 ∷ 4 ∷ 12 ∷ 100 ∷ 16 ∷ 31 ∷ []) .fst


  -- go : List A ⊸ Maybe (A × List A)
  -- go [] = nothing○ by cn[]
  -- go (x ∷ ys) = just○ ＠ getMin (x , ys) by wk, ∘ cn∷

  -- ssortSorted : (xs : List A) → Sorted (fst (ssort xs))
  -- ssortSorted xs with fst (ssort xs)
  -- ... | [] = []
  -- ... | x ∷ xs = {!!}



-- TODO show it's sorted


