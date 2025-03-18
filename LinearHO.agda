{-# OPTIONS --cubical --safe #-}

module LinearHO where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe
open import Cubical.Data.Sum

open import Cubical.Data.Nat public hiding (_^_)
open import Cubical.HITs.FiniteMultiset public hiding ([_]) renaming (FMSet to Bag ; [] to ◇ ; _∷_ to _⨾_ ; _++_ to _⊗_)

open import Base


infixl 0 _⧟_
infixl 10 [_,_]
infixl 11 _⊗ᶠ_
infixl 10 _∘_


abstract
  _⧟_ : ∀{ℓ} → Supply ℓ → Supply ℓ → Type (ℓ-suc ℓ)
  _⧟_ _ _ = Unit*

  id : ∀{ℓ}→ (Δ : Supply ℓ) → Δ ⧟ Δ
  id _ = tt*

  _∘_ : ∀ {ℓ} {Δ₀ Δ₁ Δ₂ : Supply ℓ}
    →  Δ₁ ⧟ Δ₂
    →  Δ₀ ⧟ Δ₁
    →  Δ₀ ⧟ Δ₂
  _∘_ _ _ = tt*

  [_,_] : ∀{ℓ} → Supply ℓ → Supply ℓ → Supply ℓ
  cur : ∀ {ℓ} {Δ₀ Δ₁ Δ₂ : Supply ℓ} →  (Δ₀ ⊗ Δ₁) ⧟ Δ₂ → Δ₀ ⧟ [ Δ₁ , Δ₂ ]
  unc : ∀ {ℓ} {Δ₀ Δ₁ Δ₂ : Supply ℓ} →  Δ₀ ⧟ [ Δ₁ , Δ₂ ] →  (Δ₀ ⊗ Δ₁) ⧟  Δ₂

  [_,_] _ _ = ◇
  cur _ = tt*
  unc _ = tt*

  _⊗ᶠ_ : ∀ {ℓ} {Δ₀ Δ₁ Δ₀' Δ₁' : Supply ℓ}
    → Δ₀ ⧟ Δ₁
    → Δ₀' ⧟ Δ₁'
    → Δ₀ ⊗ Δ₀' ⧟ Δ₁ ⊗ Δ₁'
  _⊗ᶠ_ _ _ = tt*

  ι, :  ∀{ℓ} {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
    → η {A = Σ A B} (a , b) ⧟ (η a ⊗ η b)
  ι, = tt*
  ω, :  ∀{ℓ} {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
    → (η a ⊗ η b) ⧟ η {A = Σ A B} (a , b)
  ω, = tt*


  ι[] : ∀{ℓ} {A : Type ℓ} → (η {A = List A} []) ⧟ ◇
  ι[] = tt*
  ω[] : ∀{ℓ}{A : Type ℓ} → ◇ ⧟ (η {A = List A} [])
  ω[] = tt*
  ι∷ : ∀{ℓ}{A : Type ℓ} {x : A} {xs : List A} → η (x ∷ xs) ⧟ η x ⊗ η xs
  ι∷ = tt*
  ω∷ : ∀{ℓ}{A : Type ℓ} {x : A} {xs : List A} → η x ⊗ η xs ⧟ η (x ∷ xs)
  ω∷ = tt*



  ωinl : ∀{ℓ}{A B : Type ℓ} {a : A} → η a ⧟ η {A = A ⊎ B} (inl a)
  ωinl = tt*
  ιinl : ∀{ℓ}{A B : Type ℓ} {a : A} → η {A = A ⊎ B} (inl a) ⧟ η a
  ιinl = tt*

  ωinr : ∀{ℓ}{A B : Type ℓ} {b : B} → η b ⧟ η {A = A ⊎ B} (inr b)
  ωinr = tt*
  ιinr : ∀{ℓ}{A B : Type ℓ} {b : B} → η {A = A ⊎ B} (inr b) ⧟ η b
  ιinr = tt*


  Λₒ : ∀{ℓ} → (A : Type ℓ) → (Δ : A → Supply ℓ) → Supply ℓ

  Λₒ A Δ = ◇

  module _ {ℓ} {A : Type ℓ} {Δ₀ : Supply ℓ} {Δ : A → Supply ℓ} where
    abstract
      λₒ : ((x : A) → Δ₀ ⧟ Δ x) → (Δ₀ ⧟ Λₒ A Δ)
      λₒ⁻¹ : (Δ₀ ⧟ Λₒ A Δ) → ((x : A) → Δ₀ ⧟ Δ x)



      λₒ _ = tt*
      λₒ⁻¹ _ _ = tt*



private
  variable
    ℓ : Level

Λₒ-syntax : (A : Type ℓ) → (A → Supply ℓ) → Supply (ℓ)
Λₒ-syntax = Λₒ

syntax Λₒ-syntax A (λ x → Δ) = Λₒ[ x ∈ A ] Δ

DSupply : (ℓ : Level) → Type (ℓ-suc ℓ)
DSupply ℓ = Σ[ A ∈ Type ℓ ] (A → Supply ℓ)




_⊩_ : Supply ℓ → DSupply ℓ → Type (ℓ-suc ℓ)
Δ ⊩ (A , Δ₁) = Σ[ a ∈ A ] (Δ ⧟ Δ₁ a)
infixl -100 _⊩_

_⊩₁_ : Supply ℓ → Type ℓ → Type (ℓ-suc ℓ)
Δ ⊩₁ A = Δ ⊩ (A , η)
infixl -100 _⊩₁_


ax : {(A , Δ) : DSupply ℓ} → (a : A) → Δ a ⊩ (A , Δ)
ax {_} {(A , Δ)} a = a , (id (Δ a))

ap : {Δ₀ Δ₁ : Supply ℓ} {A : DSupply ℓ}
  → (δ : Δ₁ ⧟ Δ₀)
  → Δ₀ ⊩ A
  → Δ₁ ⊩ A
ap δ₁ (a , δ₂) = a , δ₂ ∘ δ₁



