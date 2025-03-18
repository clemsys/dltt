{-# OPTIONS --cubical -WnoUnsupportedIndexedMatch #-}
module Examples.Vector where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec hiding (zipWith)

open import Core
open import Functions

open LinearTypes



private
  variable
    ℓ : Level

module _ {A : Type ℓ} where
  []○ : ◇ ⊩ Vec A 0
  []○ = ． [] by wk[]'

module _ {A : Type ℓ} {n : ℕ} where
  _∷○_ : (x : A) → (xs : Vec A n) → η xs ⊗ η x ⊩ Vec A (suc n)
  _∷○_ x xs = ． (x ∷ xs) by wk∷' ∘ swap (η xs) (η x)

module _ {A : Type ℓ} {n : ℕ} {Δ₀ Δ₁ : Supply ℓ} where
  _∷◎_ : Δ₀ ⊩ A → Δ₁ ⊩ Vec A n → Δ₀ ⊗ Δ₁ ⊩ Vec A (suc n)
  _∷◎_ = ○→◎ _∷○_



module _ {A B : Type ℓ} where
  zip : (n : ℕ) → Vec A n ⊸﹠ Vec B n ⊸ Vec (A × B) n
  zip (zero) [] [] = []○ by cn[]' ⊗ᶠ cn[]'
  zip (suc n) (x ∷ xs) (y ∷ ys) = (． x ,◎ ． y) ∷◎ zip n xs ys
    by prod
    where
    prod : η (y ∷ ys) ⊗ η (x ∷ xs) ⧟ (η x ⊗ η y) ⊗ η ys ⊗ η xs
    prod =  assoc (η x ⊗ η y) (η ys) (η xs)
            ∘ (assoc' (η x) (η y) (η ys) ∘ swap (η y ⊗ η ys) (η x)) ⊗ᶠ (id (η xs))
            ∘ assoc' (η y ⊗ η ys) (η x) (η xs)
            ∘ cn∷' ⊗ᶠ cn∷'






