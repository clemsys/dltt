{-# OPTIONS --cubical --safe #-}

module Sigma where

open import Cubical.Foundations.Prelude

open import Computing
open import Deriv


elimΣ : ∀{ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : Σ A B → Type (ℓ-suc ℓ)}
  → ((x : A) → (y : B x) → C (x , y))
  → (z : Σ A B) → C z
elimΣ f (x , y) = f x y


insΣ : ∀{ℓ}{A : Type ℓ} {B : A → Type ℓ} {x : A} {y : B x}
  → η x ⊗ η y ⊩₁ Σ A B
insΣ = _ , ω,

elimΣL : ∀{ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : Σ A B → Type ℓ}
  → ((x : A) → (y : B x) → η x ⊗ η y ⊩₁ C (x , y))
  → (z : Σ A B) → η z ⊩₁ C z
elimΣL f z = ap ι, (elimΣ f z)

