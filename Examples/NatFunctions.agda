{-# OPTIONS --safe #-}

module Examples.NatFunctions where

open import Prelude
open import Base
open import Lemmas
open import NatFunctions
open import Poly


private
  variable
    ℓ : Level



module _ {A : Type ℓ} {B : A → Type ℓ} where
  pair : ◇ ⊩ ⟨ x ∶ A ． ⟩ ⊸ ⟨ y ∶ B x ． ⟩ ⊸ Σ A B ．
  pair = 𝛌 x ↦ 𝛌 y ．↦ (x , y) ⁱ by lax, ∘ id (ι x) ⊗ᶠ id (ι y) ∘ id (ι x) ⊗ᶠ unitr (ι y) ∘
                                     (id (ι x) ⊗ᶠ (id (ι y) ⊗ᶠ id ◇ ∘ unitl (ι y ⊗ ◇)) ∘
                                      unitl (ι x ⊗ ◇ ⊗ ι y ⊗ ◇)
                                      ∘
                                      (id ◇ ⊗ᶠ
                                       (id (ι x) ⊗ᶠ id ◇ ⊗ᶠ id (ι y) ⊗ᶠ id ◇ ∘ assoc' (ι x) ◇ (ι y ⊗ ◇))
                                       ∘ assoc' ◇ (ι x ⊗ ◇) (ι y ⊗ ◇)))


module _ {A : Type ℓ} where
  copyJ : (x : A) → ι x ^ 2 ⊩ A × A ．
  copyJ x = (x , x) ⁱ
    by lax, ∘ id (ι x) ⊗ᶠ id (ι x) ∘ id (ι x) ⊗ᶠ unitr (ι x) ∘ id (ι x) ⊗ᶠ id (ι x) ⊗ᶠ id ◇


module _ {A : Type ℓ} where
  copy : ◇ ⊩ ⟨ A ． ⟩^ 2 ⊸ A × A ．
  copy = 𝛌 x ↦ (x , x) ⁱ
    by lax, ∘ id (ι x) ⊗ᶠ id (ι x) ∘ id (ι x) ⊗ᶠ unitr (ι x) ∘
        (id (ι x) ⊗ᶠ id (ι x) ⊗ᶠ id ◇ ∘ unitl (ι x ⊗ ι x ⊗ ◇))

module _ {A B : Type ℓ} where
  intersperse : ◇ ⊩ ⟨ x ∶ A ． ⟩^ 2 ⊸ ⟨ y ∶ B ． ⟩ ⊸ A × B × A ．
  intersperse = 𝛌 x ↦ 𝛌 y ↦ (x , y , x) ⁱ by lax, ∘ id (ι x) ⊗ᶠ (lax, ∘ id (ι y) ⊗ᶠ id (ι x)) ∘
                                              (id (ι x) ⊗ᶠ id (ι y) ⊗ᶠ unitr (ι x) ∘
                                               (id (ι x) ⊗ᶠ
                                                (assoc' (ι y) (ι x) ◇ ∘ swap (ι x) (ι y) ⊗ᶠ id ◇ ∘
                                                 assoc (ι x) (ι y) ◇)
                                                ∘ id (ι x ⊗ ι x ⊗ ι y ⊗ ◇)))
                                              ∘
                                              (id (ι x ⊗ ι x ⊗ ι y ⊗ ◇) ∘
                                               (id (ι x) ⊗ᶠ id (ι x) ⊗ᶠ (id (ι y) ⊗ᶠ id ◇ ∘ unitl (ι y ⊗ ◇)) ∘
                                                unitl (ι x ⊗ ι x ⊗ ◇ ⊗ ι y ⊗ ◇))
                                               ∘
                                               (id ◇ ⊗ᶠ
                                                (id (ι x) ⊗ᶠ
                                                 (id (ι x) ⊗ᶠ id ◇ ⊗ᶠ id (ι y) ⊗ᶠ id ◇ ∘ assoc' (ι x) ◇ (ι y ⊗ ◇))
                                                 ∘ assoc' (ι x) (ι x ⊗ ◇) (ι y ⊗ ◇))
                                                ∘ assoc' ◇ (ι x ⊗ ι x ⊗ ◇) (ι y ⊗ ◇)))

module _ {A  : Type ℓ} where

  copytwice : ◇ ⊩ ⟨ x ∶ A ． ⟩^ 4 ⊸ (A × A) × (A × A) ．
  copytwice = 𝛌 x ↦ copy ≺ 2 ﹫． (copy ≺ 2 ﹫ x ⁱ)
    by id ◇ ⊗ᶠ
        (assoc ◇ (ι x ⊗ ι x ⊗ ◇) ((◇ ⊗ ι x ⊗ ι x ⊗ ◇) ⊗ ◇) ∘
         id ◇ ⊗ᶠ
         (assoc (ι x) (ι x ⊗ ◇) ((◇ ⊗ ι x ⊗ ι x ⊗ ◇) ⊗ ◇) ∘
          id (ι x) ⊗ᶠ
          (assoc (ι x) ◇ ((◇ ⊗ ι x ⊗ ι x ⊗ ◇) ⊗ ◇) ∘
           id (ι x) ⊗ᶠ
           id ◇ ⊗ᶠ
           (assoc ◇ (ι x ⊗ ι x ⊗ ◇) ◇ ∘
            id ◇ ⊗ᶠ
            (assoc (ι x) (ι x ⊗ ◇) ◇ ∘
             id (ι x) ⊗ᶠ (assoc (ι x) ◇ ◇ ∘ id (ι x) ⊗ᶠ id ◇ ⊗ᶠ id ◇))))))
        ∘
        (unitl' (◇ ⊗ ι x ⊗ ι x ⊗ ◇ ⊗ ◇ ⊗ ι x ⊗ ι x ⊗ ◇ ⊗ ◇) ∘
         (unitl' (ι x ⊗ ι x ⊗ ◇ ⊗ ◇ ⊗ ι x ⊗ ι x ⊗ ◇ ⊗ ◇) ∘
          id (ι x) ⊗ᶠ
          id (ι x) ⊗ᶠ
          (unitl' (◇ ⊗ ι x ⊗ ι x ⊗ ◇ ⊗ ◇) ∘
           (unitl' (ι x ⊗ ι x ⊗ ◇ ⊗ ◇) ∘
            id (ι x) ⊗ᶠ id (ι x) ⊗ᶠ (unitl' ◇ ∘ id ◇)))))
        ∘
        (id (ι x) ⊗ᶠ id (ι x) ⊗ᶠ id (ι x) ⊗ᶠ id (ι x) ⊗ᶠ id ◇ ∘
         unitl (ι x ⊗ ι x ⊗ ι x ⊗ ι x ⊗ ◇))


module _ {A : Type ℓ} {B : A → Type ℓ} {C : (x : A) → B x → Type ℓ} where
  compose : ◇ ⊩ ⟨ g ∶ ⟨ x ∶ A ． ⟩^ 0 ⊸ ⟨ y ∶ B x ． ⟩ ⊸ C x y ． ⟩ ⊸ ⟨ f ∶ ⟨ x ∶ A ． ⟩ ⊸ B x ． ⟩
    ⊸ ⟨ x ∶ A ． ⟩ ⊸ C x (f x) ．
  compose = 𝛌 g ↦𝕗 𝛌 f ↦𝕗 𝛌 x ．↦  (g ᵀ ≺ 0 ﹫ x ⁱ) ﹫． (f ᵀ ﹫． x ⁱ)
    by assoc
        (Λ A
         (λ x₁ →
            [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ]))
        ◇ ((Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]) ⊗ ι x ⊗ ◇) ⊗ ◇)
        ∘
        id
        (Λ A
         (λ x₁ →
            [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ]))
        ⊗ᶠ
        id ◇ ⊗ᶠ
        (assoc (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) (ι x ⊗ ◇) ◇ ∘
         id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) ⊗ᶠ
         (assoc (ι x) ◇ ◇ ∘ id (ι x) ⊗ᶠ id ◇ ⊗ᶠ id ◇))
        ∘
        id
        (Λ A
         (λ x₁ →
            [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ]))
        ⊗ᶠ
        (unitl' (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]) ⊗ ι x ⊗ ◇ ⊗ ◇)
         ∘
         id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) ⊗ᶠ
         id (ι x) ⊗ᶠ (unitl' ◇ ∘ id ◇))
        ∘
        (id
         (Λ A
          (λ x₁ →
             [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ]))
         ⊗ᶠ
         (id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) ⊗ᶠ
          (id (ι x) ⊗ᶠ id ◇ ∘ unitl (ι x ⊗ ◇))
          ∘ unitl (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]) ⊗ ◇ ⊗ ι x ⊗ ◇))
         ∘
         unitl
         (Λ A
          (λ x₁ → [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ])
          ⊗ ◇ ⊗ Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]) ⊗ ◇ ⊗ ι x ⊗ ◇)
         ∘
         (id ◇ ⊗ᶠ
          (id
           (Λ A
            (λ x₁ →
               [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ]))
           ⊗ᶠ
           id ◇ ⊗ᶠ
           (id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) ⊗ᶠ
            id ◇ ⊗ᶠ id (ι x) ⊗ᶠ id ◇
            ∘ assoc' (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ])) ◇ (ι x ⊗ ◇))
           ∘
           assoc'
           (Λ A
            (λ x₁ →
               [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ]))
           ◇ ((Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]) ⊗ ◇) ⊗ ι x ⊗ ◇))
          ∘
          assoc' ◇
          (Λ A
           (λ x₁ → [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ])
           ⊗ ◇)
          ((Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]) ⊗ ◇) ⊗ ι x ⊗ ◇)
          ∘
          assoc'
          (◇ ⊗
           Λ A
           (λ x₁ → [ ◇ , Λ (B x₁) (λ x₂ → [ ι x₂ ⊗ ◇ , ι (g .term x₁ x₂) ]) ])
           ⊗ ◇)
          (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (f .term x₁) ]) ⊗ ◇) (ι x ⊗ ◇)))


module _ {A : Type ℓ} {B : A → Type ℓ} {C : (x : A) → B x → Type ℓ} {m n : ℕ} where
  compose' : ◇ ⊩ ⟨ g ∶ ⟨ x ∶ A ． ⟩^ 0 ⊸ ⟨ y ∶ B x ． ⟩^ m ⊸ C x y ． ⟩ ⊸
    ⟨ f ∶ ⟨ x ∶ A ． ⟩^ n ⊸ B x ． ⟩^ m ⊸ ⟨ x ∶ A ． ⟩^ (m * n) ⊸ C x (f x) ．
  compose' = 𝛌 g ↦𝕗 𝛌 f ↦𝕗 𝛌 x ．↦ (g ᵀ ≺ 0 ﹫ x ⁱ) ≺ m ﹫． (f ᵀ ≺ n ﹫ x ⁱ)
    by unitl _ ⊗ᶠ (⊗^-distr m n) ∘ assoc' _ _ _



module _ {A : Type ℓ} where
  ifthenelse : ◇ ⊩ ⟨ b ∶ Bool ． ⟩^ 0 ⊸ ⟨ A ． ⟩^ ∣ b ∣  ⊸ ⟨ A ． ⟩^ ∣ ¬ b ∣ ⊸ A ．
  ifthenelse = 𝛌 b ．↦ case b of
    (λ b → ◇ ⊗ ◇ ⊩ ⟨ A ． ⟩^ ∣ b ∣  ⊸ ⟨ A ． ⟩^ ∣ ¬ b ∣ ⊸ A ．) type λ where
      true → 𝛌 x ．↦ 𝛌 _ ．↦ x ⁱ
        by unitr (ι x) ∘
            (id (ι x) ⊗ᶠ (id ◇ ∘ unitl ◇) ∘ unitl (ι x ⊗ ◇ ⊗ ◇) ∘
             unitl (◇ ⊗ ι x ⊗ ◇ ⊗ ◇)
             ∘
             (id ◇ ⊗ᶠ id ◇ ⊗ᶠ (id (ι x) ⊗ᶠ id ◇ ⊗ᶠ id ◇ ∘ assoc' (ι x) ◇ ◇) ∘
              assoc' ◇ ◇ ((ι x ⊗ ◇) ⊗ ◇)
              ∘ assoc' (◇ ⊗ ◇) (ι x ⊗ ◇) ◇))
      false → 𝛌 _ ．↦ 𝛌 y ．↦ y ⁱ
        by unitr (ι y) ∘
            (id (ι y) ⊗ᶠ id ◇ ∘ unitl (ι y ⊗ ◇) ∘ unitl (◇ ⊗ ι y ⊗ ◇) ∘
             unitl (◇ ⊗ ◇ ⊗ ι y ⊗ ◇)
             ∘
             (id ◇ ⊗ᶠ id ◇ ⊗ᶠ id ◇ ⊗ᶠ id (ι y) ⊗ᶠ id ◇ ∘
              assoc' ◇ ◇ (◇ ⊗ ι y ⊗ ◇)
              ∘ assoc' (◇ ⊗ ◇) ◇ (ι y ⊗ ◇)))





module _ {A : LType ℓ} where
  ite' : ◇ ⊩ ⟨ b ∶ Bool ． ⟩^ 0 ⊸ ⟨ A ⟩^ ∣ b ∣  ⊸ ⟨ A ⟩^ ∣ ¬ b ∣ ⊸ A
  ite' = 𝛌 b ．↦ case b of
    (λ b → ◇ ⊗ ◇ ⊩ ⟨ A ⟩^ ∣ b ∣  ⊸ ⟨ A ⟩^ ∣ ¬ b ∣ ⊸ A) type λ where
      true → 𝛌 x ↦𝕗 𝛌 _ ．↦ x ᵀ by unitr (A .snd (x .term)) ∘
                                    (id (A .snd (x .term)) ⊗ᶠ (id ◇ ∘ unitl ◇) ∘
                                     unitl (A .snd (x .term) ⊗ ◇ ⊗ ◇)
                                     ∘ unitl (◇ ⊗ A .snd (x .term) ⊗ ◇ ⊗ ◇)
                                     ∘
                                     (id ◇ ⊗ᶠ
                                      id ◇ ⊗ᶠ
                                      (id (A .snd (x .term)) ⊗ᶠ id ◇ ⊗ᶠ id ◇ ∘
                                       assoc' (A .snd (x .term)) ◇ ◇)
                                      ∘ assoc' ◇ ◇ ((A .snd (x .term) ⊗ ◇) ⊗ ◇)
                                      ∘ assoc' (◇ ⊗ ◇) (A .snd (x .term) ⊗ ◇) ◇))
      false → 𝛌 _ ．↦ 𝛌 y ↦𝕗 y ᵀ by unitr (A .snd (y .term)) ∘
                                     (id (A .snd (y .term)) ⊗ᶠ id ◇ ∘ unitl (A .snd (y .term) ⊗ ◇) ∘
                                      unitl (◇ ⊗ A .snd (y .term) ⊗ ◇)
                                      ∘ unitl (◇ ⊗ ◇ ⊗ A .snd (y .term) ⊗ ◇)
                                      ∘
                                      (id ◇ ⊗ᶠ id ◇ ⊗ᶠ id ◇ ⊗ᶠ id (A .snd (y .term)) ⊗ᶠ id ◇ ∘
                                       assoc' ◇ ◇ (◇ ⊗ A .snd (y .term) ⊗ ◇)
                                       ∘ assoc' (◇ ⊗ ◇) ◇ (A .snd (y .term) ⊗ ◇)))


module Ignore {A B : Type ℓ} where
  foldMaybe : ◇ ⊩ ⟨ z ∶ Maybe A ． ⟩ ⊸ ⟨ j ∶ ⟨ A ． ⟩ ⊸ B ． ⟩^ ∣ isJust z ∣ ⊸ ⟨ n ∶ B ． ⟩^ ∣ isNothing z ∣ ⊸ B ．
  foldMaybe = 𝛌 z ．↦ case z of
    (λ z → ◇ ⊗ ι z ^ 1 ⊩ ⟨ ⟨ A ． ⟩ ⊸ B ． ⟩^ ∣ isJust z ∣ ⊸ ⟨ B ． ⟩^ ∣ isNothing z ∣ ⊸ B ．) type λ where
      (just x) → 𝛌 j ↦𝕗 𝛌 _ ．↦ j ᵀ ﹫． x ⁱ by assoc' (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) (ι x) ◇ ∘
                                                 swap (ι x) (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ id ◇
                                                 ∘ assoc (ι x) (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ◇
                                                 ∘ id (ι x ⊗ Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇)
                                                 ∘
                                                 (id (ι x ⊗ Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ∘
                                                  (id (ι x) ⊗ᶠ
                                                   (id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ
                                                    (id ◇ ∘ unitl ◇)
                                                    ∘ unitl (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇ ⊗ ◇))
                                                   ∘
                                                   unitl
                                                   (ι x ⊗ ◇ ⊗ Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇ ⊗ ◇))
                                                  ∘
                                                  (id ◇ ⊗ᶠ
                                                   (id (ι x) ⊗ᶠ
                                                    id ◇ ⊗ᶠ
                                                    (id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ id ◇ ⊗ᶠ id ◇ ∘
                                                     assoc' (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ◇ ◇)
                                                    ∘
                                                    assoc' (ι x) ◇
                                                    ((Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ⊗ ◇))
                                                   ∘
                                                   assoc' ◇ (ι x ⊗ ◇)
                                                   ((Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ⊗ ◇)
                                                   ∘
                                                   assoc' (◇ ⊗ ι x ⊗ ◇)
                                                   (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ◇)
                                                  ∘
                                                  ((id ◇ ⊗ᶠ (id (ι x) ∘ oplinl) ⊗ᶠ id ◇) ⊗ᶠ
                                                   id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ id ◇)
                                                  ⊗ᶠ id ◇)
      nothing → 𝛌 _ ．↦ 𝛌 n ．↦ n ⁱ by unitr (ι n) ∘
                                        (id (ι n) ⊗ᶠ id ◇ ∘ unitl (ι n ⊗ ◇) ∘ unitl (◇ ⊗ ι n ⊗ ◇) ∘
                                         unitl (◇ ⊗ ◇ ⊗ ι n ⊗ ◇)
                                         ∘ unitl (◇ ⊗ ◇ ⊗ ◇ ⊗ ι n ⊗ ◇)
                                         ∘
                                         (id ◇ ⊗ᶠ
                                          (id ◇ ⊗ᶠ id ◇ ⊗ᶠ id ◇ ⊗ᶠ id (ι n) ⊗ᶠ id ◇ ∘
                                           assoc' ◇ ◇ (◇ ⊗ ι n ⊗ ◇))
                                          ∘ assoc' ◇ (◇ ⊗ ◇) (◇ ⊗ ι n ⊗ ◇)
                                          ∘ assoc' (◇ ⊗ ◇ ⊗ ◇) ◇ (ι n ⊗ ◇))
                                         ∘ ((id ◇ ⊗ᶠ (opltt ∘ oplinr) ⊗ᶠ id ◇) ⊗ᶠ id ◇) ⊗ᶠ id (ι n) ⊗ᶠ id ◇)



module _ {A B : Type ℓ} where
  foldMaybe : ◇ ⊩ ⟨ z ∶ Maybe A ． ⟩ ⊸ ⟨ ⟨ A ． ⟩ ⊸ B ． ⟩^ ∣ isJust z ∣ ⊸ ⟨ B ． ⟩^ ∣ isNothing z ∣ ⊸ B ．
  foldMaybe = 𝛌 z ．↦ case z of
    (λ z → ◇ ⊗ ι z ^ 1 ⊩ ⟨ ⟨ A ． ⟩ ⊸ B ． ⟩^ ∣ isJust z ∣ ⊸ ⟨ B ． ⟩^ ∣ isNothing z ∣ ⊸ B ．) type λ where
      (just x) → 𝛌 j ↦𝕗 𝛌 _ ．↦ j ᵀ ﹫． x ⁱ
        by assoc' (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) (ι x) ◇ ∘
            swap (ι x) (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ id ◇
            ∘ assoc (ι x) (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ◇
            ∘ id (ι x ⊗ Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇)
            ∘
            (id (ι x ⊗ Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ∘
             (id (ι x) ⊗ᶠ
              (id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ
               (id ◇ ∘ unitl ◇)
               ∘ unitl (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇ ⊗ ◇))
              ∘
              unitl
              (ι x ⊗ ◇ ⊗ Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇ ⊗ ◇))
             ∘
             (id ◇ ⊗ᶠ
              (id (ι x) ⊗ᶠ
               id ◇ ⊗ᶠ
               (id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ id ◇ ⊗ᶠ id ◇ ∘
                assoc' (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ◇ ◇)
               ∘
               assoc' (ι x) ◇
               ((Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ⊗ ◇))
              ∘
              assoc' ◇ (ι x ⊗ ◇)
              ((Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ⊗ ◇)
              ∘
              assoc' (◇ ⊗ ι x ⊗ ◇)
              (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ]) ⊗ ◇) ◇)
             ∘
             ((id ◇ ⊗ᶠ (id (ι x) ∘ oplinl) ⊗ᶠ id ◇) ⊗ᶠ
              id (Λ A (λ x₁ → [ ι x₁ ⊗ ◇ , ι (j .term x₁) ])) ⊗ᶠ id ◇)
             ⊗ᶠ id ◇)
      nothing → 𝛌 _ ．↦ 𝛌 n ．↦ n ⁱ
        by unitr (ι n) ∘
            (id (ι n) ⊗ᶠ id ◇ ∘ unitl (ι n ⊗ ◇) ∘ unitl (◇ ⊗ ι n ⊗ ◇) ∘
             unitl (◇ ⊗ ◇ ⊗ ι n ⊗ ◇)
             ∘ unitl (◇ ⊗ ◇ ⊗ ◇ ⊗ ι n ⊗ ◇)
             ∘
             (id ◇ ⊗ᶠ
              (id ◇ ⊗ᶠ id ◇ ⊗ᶠ id ◇ ⊗ᶠ id (ι n) ⊗ᶠ id ◇ ∘
               assoc' ◇ ◇ (◇ ⊗ ι n ⊗ ◇))
              ∘ assoc' ◇ (◇ ⊗ ◇) (◇ ⊗ ι n ⊗ ◇)
              ∘ assoc' (◇ ⊗ ◇ ⊗ ◇) ◇ (ι n ⊗ ◇))
             ∘ ((id ◇ ⊗ᶠ (opltt ∘ oplinr) ⊗ᶠ id ◇) ⊗ᶠ id ◇) ⊗ᶠ id (ι n) ⊗ᶠ id ◇)



