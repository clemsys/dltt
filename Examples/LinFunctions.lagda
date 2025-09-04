\begin{code}[hide]
{-# OPTIONS --safe #-}

module Examples.LinFunctions where

open import Prelude
open import Base hiding (curry ; uncurry)
open import Lemmas
open import LinFunctions
open import Poly


private
  variable
    ℓ : Level

module _ {A : Type ℓ} {B : A → Type ℓ} where
  pair : ◇ ⊩ ⟨ x ∶ A ． ⟩ ⊸ ⟨ y ∶ B x ． ⟩ ⊸ Σ A B ．
  pair = 𝛌 x ↦ 𝛌 y ．↦  (x , y) ⁱ
    by lax, ∘ id (ι x) ⊗ᶠ id (ι y) ∘ id (ι x) ⊗ᶠ unitr (ι y) ∘
      (id (ι x) ⊗ᶠ unitr' (ι y) ∘ unitl (ι x ⊗ ι y) ∘
      (id ◇ ⊗ᶠ id (ι x) ⊗ᶠ id (ι y) ∘ assoc' ◇ (ι x) (ι y)))


module _ {A B : Type ℓ} where
\end{code}
\newcommand{\agdaDLTTswitch}{%
\begin{code}
  switch : ◇ ⊩ ⟨ A × B ． ⟩ ⊸ B × A ．
  switch = 𝛌 (x , y) ↦ pair ﹫ y ⁱ ﹫． x ⁱ
\end{code}}
\begin{code}[hide]
      by assoc _ _ _ ∘ id ◇ ⊗ᶠ swap (ι x) (ι y) ∘ id ◇ ⊗ᶠ opl,


module _ {A B : Type ℓ} where
  idf : ◇ ⊩ ⟨ x ∶ A ． ⟩ ⊸ A ．
  idf = 𝛌 x ．↦ x ⁱ by unitr (ι x) ∘ (unitr' (ι x) ∘ unitl (ι x))


module _ {A B : Type ℓ} where
  mp : ◇ ⊩ ⟨ ⟨ A ． ⟩ ⊸ B ． ⟩ ⊸ ⟨ A ． ⟩ ⊸ B ．
  mp = 𝛌 f ↦𝕗 𝛌 x ↦ f ᵀ ﹫． x ⁱ by id (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ unitr (ι x) ∘
                                     (id (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ unitr' (ι x) ∘
                                      unitl (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ]) ⊗ ι x)
                                      ∘
                                      (id ◇ ⊗ᶠ id (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ id (ι x) ∘
                                       assoc' ◇ (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) (ι x)))


module _ {A B C : Type ℓ} where
  compose : ◇ ⊩ ⟨ ⟨ B ． ⟩ ⊸ C ． ⟩ ⊸ ⟨ ⟨ A ． ⟩ ⊸ B ． ⟩ ⊸ ⟨ A ． ⟩ ⊸ C ．
  compose = 𝛌 g ↦𝕗 𝛌 f ↦𝕗 𝛌 x ．↦ g ᵀ ﹫． (f ᵀ ﹫ x ⁱ) by id (Λ B (λ x₁ → [ ι x₁ , ι (g .term x₁) ])) ⊗ᶠ
                                                            id (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ unitr (ι x)
                                                            ∘
                                                            (id (Λ B (λ x₁ → [ ι x₁ , ι (g .term x₁) ])) ⊗ᶠ
                                                             id (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ unitr' (ι x)
                                                             ∘
                                                             unitl
                                                             (Λ B (λ x₁ → [ ι x₁ , ι (g .term x₁) ]) ⊗
                                                              Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ]) ⊗ ι x)
                                                             ∘
                                                             (id ◇ ⊗ᶠ
                                                              id (Λ B (λ x₁ → [ ι x₁ , ι (g .term x₁) ])) ⊗ᶠ
                                                              id (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ id (ι x)
                                                              ∘
                                                              assoc' ◇ (Λ B (λ x₁ → [ ι x₁ , ι (g .term x₁) ]))
                                                              (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ]) ⊗ ι x)
                                                              ∘
                                                              assoc' (◇ ⊗ Λ B (λ x₁ → [ ι x₁ , ι (g .term x₁) ]))
                                                              (Λ A (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) (ι x)))


module _ {A : Type ℓ} {B : A → Type ℓ} {C : (x : A) → B x → Type ℓ} where
  curry :  ◇ ⊩ ⟨ ⟨ (x , y) ∶ Σ A B ． ⟩ ⊸ C x y ． ⟩ ⊸ ⟨ x ∶ A ． ⟩ ⊸ ⟨ y ∶ B x ． ⟩ ⊸ C x y ．
  curry = 𝛌 f ↦𝕗 𝛌 x ↦ 𝛌 y ．↦ f ᵀ ﹫． (pair ﹫ x ⁱ ﹫． y ⁱ)
   by id (Λ (Σ A B) (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ
       (assoc ◇ (ι x) (ι y) ∘ id ◇ ⊗ᶠ id (ι x) ⊗ᶠ id (ι y))
       ∘
       id (Λ (Σ A B) (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ
       (unitl' (ι x ⊗ ι y) ∘ id (ι x) ⊗ᶠ unitr (ι y))
       ∘
       (id (Λ (Σ A B) (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ
        id (ι x) ⊗ᶠ unitr' (ι y)
        ∘ unitl (Λ (Σ A B) (λ x₁ → [ ι x₁ , ι (f .term x₁) ]) ⊗ ι x ⊗ ι y)
        ∘
        (id ◇ ⊗ᶠ
         id (Λ (Σ A B) (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) ⊗ᶠ
         id (ι x) ⊗ᶠ id (ι y)
         ∘
         assoc' ◇ (Λ (Σ A B) (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) (ι x ⊗ ι y)
         ∘
         assoc' (◇ ⊗ Λ (Σ A B) (λ x₁ → [ ι x₁ , ι (f .term x₁) ])) (ι x)
         (ι y)))

module _ {A : Type ℓ} {B : A → Type ℓ} {C : (x : A) → B x → Type ℓ} where
  uncurry :  ◇ ⊩  ⟨ ⟨ x ∶ A ． ⟩ ⊸ ⟨ y ∶ B x ． ⟩ ⊸ C x y ． ⟩ ⊸ ⟨ (x , y) ∶ Σ A B ． ⟩ ⊸ C x y ．
  uncurry = 𝛌 f ↦𝕗 𝛌 (x , y) ．↦ f ᵀ ﹫ x ⁱ ﹫． y ⁱ
   by assoc
               (Λ A
                (λ x₁ → [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ]))
               (ι x) (ι y)
               ∘
               id
               (Λ A
                (λ x₁ → [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ]))
               ⊗ᶠ id (ι x) ⊗ᶠ id (ι y)
               ∘
               id
               (Λ A
                (λ x₁ → [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ]))
               ⊗ᶠ id (ι x) ⊗ᶠ unitr (ι y)
               ∘
               (id
                (Λ A
                 (λ x₁ → [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ]))
                ⊗ᶠ id (ι x) ⊗ᶠ unitr' (ι y)
                ∘
                unitl
                (Λ A
                 (λ x₁ → [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ])
                 ⊗ ι x ⊗ ι y)
                ∘
                (id ◇ ⊗ᶠ
                 id
                 (Λ A
                  (λ x₁ → [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ]))
                 ⊗ᶠ id (ι x) ⊗ᶠ id (ι y)
                 ∘
                 assoc' ◇
                 (Λ A
                  (λ x₁ → [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ]))
                 (ι x ⊗ ι y))
                ∘
                (id ◇ ⊗ᶠ
                 id
                 (Λ A
                  (λ x₁ →
                     [ ι x₁ , Λ (B x₁) (λ x₂ → [ ι x₂ , ι (f .term x₁ x₂) ]) ])))
                ⊗ᶠ (id (ι x) ⊗ᶠ id (ι y) ∘ opl,))

\end{code}
