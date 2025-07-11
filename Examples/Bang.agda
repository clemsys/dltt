{-# OPTIONS --safe #-}

module Examples.Bang where

open import Prelude
open import Base
open import Lemmas
open import NatFunctions
open import BangFunctions
open import Poly


private
  variable
    ℓ : Level
    A : Type ℓ


copyJ : (x : A) → ! (ι x) ⊩ A × A ．
copyJ x = (x , x) ⁱ by lax, ∘ (use ∘ dupl)


drop : (x : A) → ! (ι x) ⊩ ⊤ ．
drop x = tt* ⁱ by laxtt ∘ erase

copy : ◇ ⊩ !⟨ A ． ⟩ ⊸ A × A ．
copy = 𝛌 x !↦ copyJ x
  by unitr (! (ι x)) ∘ (unitr' (! (ι x)) ∘ unitl (! (ι x)))


copytwice : ◇ ⊩ !⟨ A ． ⟩ ⊸ (A × A) × (A × A) ．
copytwice = 𝛌 x ．!↦  copy !﹫． (copy !﹫ x ⁱ)
  by unitl' (! (◇ ⊗ ! (ι x))) ∘ !ᶠ (unitl' (! (ι x))) ∘ mult ∘ unitl (! (ι x))


just𝕗 : ◇ ⊩ ⟨ A ． ⟩ ⊸ Maybe A ．
just𝕗 = 𝛌 x ．↦ (just x) ⁱ by laxinl ∘ id (ι x) ∘ unitr (ι x) ∘
                               (id (ι x) ⊗ᶠ id ◇ ∘ unitl (ι x ⊗ ◇))

module _ {A B : Type ℓ} where
  mapMaybe : ◇ ⊩ !⟨ ⟨ A ． ⟩ ⊸ B ． ⟩ ⊸ ⟨ Maybe A ． ⟩ ⊸ Maybe B ．
  mapMaybe = 𝛌 f !↦𝕗 𝛌 x ↦ case x of
    (λ x → (◇ ⊗ ! ((⟨ A ． ⟩ ⊸ B ．) .snd (f .term))) ⊗ ι x ^ 1 ⊩ Maybe B ．) type λ where
      (just x) → just𝕗 ﹫． (f ᵀγ ﹫． x ⁱ)
        by id ◇ ⊗ᶠ
            (assoc (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]))) (ι x ⊗ ◇) ◇
             ∘
             id (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]))) ⊗ᶠ
             (assoc (ι x) ◇ ◇ ∘ id (ι x) ⊗ᶠ id ◇ ⊗ᶠ id ◇))
            ∘
            (unitl'
             (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) ⊗ ι x ⊗ ◇ ⊗ ◇)
             ∘
             id (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]))) ⊗ᶠ
             id (ι x) ⊗ᶠ (unitl' ◇ ∘ id ◇))
            ∘
            (id (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]))) ⊗ᶠ
             id (ι x) ⊗ᶠ id ◇
             ∘ unitl (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) ⊗ ι x ⊗ ◇)
             ∘
             (id ◇ ⊗ᶠ
              id (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]))) ⊗ᶠ
              id (ι x) ⊗ᶠ id ◇
              ∘
              assoc' ◇ (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])))
              (ι x ⊗ ◇))
             ∘
             (id ◇ ⊗ᶠ id (! (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])))) ⊗ᶠ
             (id (ι x) ∘ oplinl) ⊗ᶠ id ◇)
      nothing → nothing ⁱ
              by laxinr ∘ laxtt ∘ id ◇ ∘
                (id ◇ ∘ (id ◇ ∘ unitl ◇ ∘ unitl (◇ ⊗ ◇) ∘ unitl (◇ ⊗ ◇ ⊗ ◇)) ∘
                (id ◇ ⊗ᶠ id ◇ ⊗ᶠ id ◇ ⊗ᶠ id ◇ ∘ assoc' ◇ ◇ (◇ ⊗ ◇))
                ∘ (id ◇ ⊗ᶠ id ◇) ⊗ᶠ (opltt ∘ oplinr) ⊗ᶠ id ◇) ∘ (id ◇ ⊗ᶠ erase) ⊗ᶠ id (ι nothing ⊗ ◇)




