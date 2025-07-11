{-# OPTIONS --safe #-}
module NatMul where

open import Prelude
open import Base
open import Lemmas
open import Data.Nat public hiding (_^_ ; _≟_ ; _<_)

private
  variable
    ℓ : Level


_^_ : Supply ℓ → ℕ → Supply ℓ
Δ ^ zero = ◇
Δ ^ (suc m) = Δ ⊗ (Δ ^ m)

infixr 50 _^_

▷^ : ∀{ℓ}{Δ₀ Δ₁ : Supply ℓ} → (m : ℕ) → Δ₀ ▷ Δ₁ → (Δ₀ ^ m) ▷ (Δ₁ ^ m)
▷^ zero δ = id ◇
▷^ (suc m) δ = δ ⊗ᶠ (▷^ m δ)

module _ (X Y : Supply ℓ) where
  lemma2 : (m : ℕ) → X ^ m ⊗ Y ^ m ▷ (X ⊗ Y) ^ m
  lemma2 zero = unitl _
  lemma2 (suc m) = id (X ⊗ Y) ⊗ᶠ lemma2 m ∘ (assoc' _ _ _ ∘ (assoc _ _ _ ∘ id X ⊗ᶠ swap _ _ ∘ assoc' _ _ _ ) ⊗ᶠ id (Y ^ m)  ∘ assoc _ _ _)

module _ (X : Supply ℓ) where
  lemma3 : (m n : ℕ) → X ^ (m + n) ▷ X ^ n ⊗ X ^ m
  lemma3 zero n = unitr' _
  lemma3 (suc m) n = assoc' (X ^ n) X (X ^ m) ∘ swap _ _ ⊗ᶠ id (X ^ m)  ∘ assoc X _ _ ∘ id X ⊗ᶠ lemma3 m n

module _ (X Y : Supply ℓ) where
  lemma1 : (m n : ℕ) → Y ^ (m * n) ▷ (Y ^ n) ^ m
  lemma1 zero n = id _
  lemma1 (suc m) n = swap _ _ ∘ lemma1 m n ⊗ᶠ id (Y ^ n) ∘ lemma3 Y n (m * n) 


module _ {Δ₀ Δ₁ : Supply ℓ} where
  ⊗^-distr : (m n : ℕ) → Δ₀ ^ m ⊗ Δ₁ ^ (m * n) ▷ (Δ₀ ⊗ Δ₁ ^ n) ^ m
  ⊗^-distr m n = lemma2 Δ₀ (Δ₁ ^ n) m ∘ id (Δ₀ ^ m) ⊗ᶠ lemma1 Δ₀ Δ₁ m n


