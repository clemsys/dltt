{-# OPTIONS --safe #-}
module Lemmas where

open import Prelude
open import Base


private
  variable
    ℓ : Level

unitl : ∀ (Δ : Supply ℓ) → ◇ ⊗ Δ ▷ Δ
unitl Δ = unitr Δ ∘ swap ◇ Δ

unitl' : ∀ (Δ : Supply ℓ) → Δ ▷ ◇ ⊗ Δ
unitl' Δ = swap Δ ◇ ∘ unitr' Δ

assoc' : ∀ (Δ₀ Δ₁ Δ₂ : Supply ℓ) → (Δ₀ ⊗ Δ₁) ⊗ Δ₂ ▷ Δ₀ ⊗ (Δ₁ ⊗ Δ₂)
assoc' x y z = swap (y ⊗ z) x
  ∘ assoc y z x
  ∘ id y ⊗ᶠ swap x z
  ∘ swap (x ⊗ z) y
  ∘ swap z x ⊗ᶠ id y
  ∘ assoc z x y
  ∘ swap (x ⊗ y) z



module _ {Δ₀ Δ₁ : Supply ℓ} where
  wk : Δ₀ ▷ Δ₁ → ! Δ₀ ▷ Δ₁
  wk δ = use ∘ !ᶠ δ




