{-# OPTIONS --cubical --safe #-}
module Examples.ISort where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary

open import Core
open import Functions
open import Examples.List
open import Examples.Order

open LinearTypes

-- private
--   variable
--     ℓ : Level


module _ {ℓ : Level} {A : Type ℓ} (_<_ : Rel A A _) (_≟_ : (x y : A) → Ord.compare _<_ x y) where
  open Ord.Total _<_ _≟_

-- insert : (x : A) → (ys : List A) → η ys ⊗ η x ⊩ List A
  insert :  A ⊸﹠ List A ⊸ List A
  insert x [] = ． (x ∷ []) by wk∷ ∘ swap (η []) (η x)
  insert x (y ∷ ys) with x ≤? y
  ... | inl p = ． (x ∷ y ∷ ys) by wk∷ ∘ swap (η (y ∷ ys)) (η x)
  ... | inr p = ． y ∷◎ insert x ys by cn∷ ⊗ᶠ id (η x)

-- ... | inr p = y ∷○_ ＠ insert x ys by cn∷ ⊗ᶠ id (η x)

-- isort : (xs : List A) → η xs ⊩ List A
  isort : List A ⊸ List A
  isort = foldr₁ insert []○


open NatOrder

test : List ℕ
test = isort _<_ _≟_ (6 ∷ 1 ∷ 23 ∷ 2 ∷ 4 ∷ 12 ∷ 100 ∷ 16 ∷ 31 ∷ []) .fst





