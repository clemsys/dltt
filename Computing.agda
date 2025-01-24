{-# OPTIONS --cubical --safe #-}

module Computing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Data.Nat public hiding (_^_)
open import Cubical.HITs.FiniteMultiset public renaming ([] to ◇ ; _∷_ to _⨾_ ; _++_ to _⊗_ ; [_] to ⟪_⟫)

infixl 0 _⊸_
infixl 10 [_,_]
infixl 11 _⊸⊗_
infixl 10 _⊸∘_

∙Type : (ℓ : Level) → Type (ℓ-suc ℓ)
∙Type ℓ = Σ[ A ∈ Type ℓ ] A

sply : (ℓ : Level) → Type (ℓ-suc ℓ)
sply ℓ = FMSet (∙Type ℓ)

η : ∀{ℓ} {A : Type ℓ} → A → sply ℓ
η a = ⟪ _ , a ⟫

abstract
  [_,_] : ∀{ℓ} → sply ℓ → sply ℓ → sply ℓ
  [_,_] _ _ = ◇

  _⊸_ : ∀{ℓ} → sply ℓ → sply ℓ → Type (ℓ-suc ℓ)
  _⊸_ _ _ = Unit*

  id : ∀{ℓ}→ (Δ : sply ℓ) → Δ ⊸ Δ
  id _ = tt*

  _⊸∘_ : ∀ {ℓ} {Δ₀ Δ₁ Δ₂ : sply ℓ}
    →  Δ₁ ⊸ Δ₂
    →  Δ₀ ⊸ Δ₁
    →  Δ₀ ⊸ Δ₂
  _⊸∘_ _ _ = tt*

  cur : ∀ {ℓ} {Δ₀ Δ₁ Δ₂ : sply ℓ} →  (Δ₀ ⊗ Δ₁) ⊸ Δ₂ → Δ₀ ⊸ [ Δ₁ , Δ₂ ]
  cur _ = tt*
  unc : ∀ {ℓ} {Δ₀ Δ₁ Δ₂ : sply ℓ} →  Δ₀ ⊸ [ Δ₁ , Δ₂ ] →  (Δ₀ ⊗ Δ₁) ⊸  Δ₂
  unc _ = tt*

  _⊸⊗_ : ∀ {ℓ} {Δ₀ Δ₁ Δ₀' Δ₁' : sply ℓ}
    → Δ₀ ⊸ Δ₁
    → Δ₀' ⊸ Δ₁'
    → Δ₀ ⊗ Δ₀' ⊸ Δ₁ ⊗ Δ₁'
  _⊸⊗_ _ _ = tt*

  ι, :  ∀{ℓ} {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
    → η {A = Σ A B} (a , b) ⊸ (η a ⊗ η b)
  ι, = tt*
  ω, :  ∀{ℓ} {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
    → (η a ⊗ η b) ⊸ η {A = Σ A B} (a , b)
  ω, = tt*


  ι[] : ∀{ℓ} {A : Type ℓ} → (η {A = List A} []) ⊸ ◇
  ι[] = tt*
  ω[] : ∀{ℓ}{A : Type ℓ} → ◇ ⊸ (η {A = List A} [])
  ω[] = tt*
  ι∷ : ∀{ℓ}{A : Type ℓ} {x : A} {xs : List A} → η (x ∷ xs) ⊸ η x ⊗ η xs
  ι∷ = tt*
  ω∷ : ∀{ℓ}{A : Type ℓ} {x : A} {xs : List A} → η x ⊗ η xs ⊸ η (x ∷ xs)
  ω∷ = tt*

  ωinl : ∀{ℓ}{A B : Type ℓ} {a : A} → η a ⊸ η {A = A ⊎ B} (inl a)
  ωinl = tt*
  ιinl : ∀{ℓ}{A B : Type ℓ} {a : A} → η {A = A ⊎ B} (inl a) ⊸ η a
  ιinl = tt*

  ωinr : ∀{ℓ}{A B : Type ℓ} {b : B} → η b ⊸ η {A = A ⊎ B} (inr b)
  ωinr = tt*
  ιinr : ∀{ℓ}{A B : Type ℓ} {b : B} → η {A = A ⊎ B} (inr b) ⊸ η b
  ιinr = tt*

  Λₒ : ∀{ℓ} → (A : Type ℓ) → (A → sply ℓ) → sply ℓ
  Λₒ A Δ = ◇

  λₒ : ∀{ℓ} {A : Type ℓ} {Δ₀ : sply ℓ} {Δ₁ : A → sply ℓ}
    → ((x : A) → ( Δ₀ ⊸  (Δ₁ x)))
    → ( Δ₀ ⊸  (Λₒ A Δ₁))
  λₒ _ = tt*

  λₒ⁻¹ : ∀{ℓ} → {A : Type ℓ} {Δ₀ : sply ℓ} {Δ₁ : A → sply ℓ}
    → ( Δ₀ ⊸  (Λₒ A Δ₁))
    → ((x : A) → ( Δ₀ ⊸  (Δ₁ x)))
  λₒ⁻¹ _ _ = tt*


-- several productions hold strictly in the finite multiset

swap : ∀{ℓ} → (x y : sply ℓ) → x ⊗ y ⊸ y ⊗ x
swap x y =  subst (_⊸ y ⊗ x) (sym (comm-++ x y)) (id (y ⊗ x))

assoc : ∀{ℓ} (Δ₀ Δ₁ Δ₂ : sply ℓ) → (Δ₀ ⊗ Δ₁) ⊗ Δ₂ ⊸ Δ₀ ⊗ Δ₁ ⊗ Δ₂
assoc x y z = subst ((x ⊗ y) ⊗ z ⊸_) (sym (assoc-++ x y z)) (id _)


unitl⊸ : ∀ {ℓ} → (Δ : sply ℓ) → (◇ ⊗ Δ) ⊸ Δ
unitl⊸ _ = id _
unitl⊸' : ∀ {ℓ} → (Δ : sply ℓ) → Δ ⊸ ◇ ⊗ Δ
unitl⊸' _ = id _
