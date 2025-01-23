{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum renaming (elim to elim⊎)

open import Computing
open import Deriv


private
  variable
    ℓ : Level

elim⊕ : {A B : Type ℓ} {C : (A ⊎ B) → Type ℓ}
  → ((x : A) → η x ⊩₁ C (inl x))
  → ((y : B) → η y ⊩₁ C (inr y))
  → ((z : A ⊎ B) → η z ⊩₁ C z)
elim⊕ f g  = elim⊎ (λ a → ap ιinl (f a)) λ b → ap ιinr (g b)


