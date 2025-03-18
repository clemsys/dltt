{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Base
module Core where




module Lemmas {ℓ : Level}
  (_⧟_ :  Supply ℓ → Supply ℓ → Type (ℓ-suc ℓ)) (let infixl 0 _⧟_; _⧟_ = _⧟_)
  (_∘_ : ∀ {Δ₀ Δ₁ Δ₂} → Δ₁ ⧟ Δ₂ → Δ₀ ⧟ Δ₁ → Δ₀ ⧟ Δ₂) (let infixl 10 _∘_; _∘_ = _∘_)
  (_⊗ᶠ_ :  ∀ {Δ₀ Δ₁ Δ₂ Δ₃} → Δ₀ ⧟ Δ₁ → Δ₂ ⧟ Δ₃ → Δ₀ ⊗ Δ₂ ⧟ Δ₁ ⊗ Δ₃) (let infixl 11 _⊗ᶠ_; _⊗ᶠ_ = _⊗ᶠ_)
  (id : (Δ : Supply ℓ) → Δ ⧟ Δ)
  where
-- private
--   variable
--     ℓ : Level


  ≡to⧟ : {Δ₀ Δ₁ : Supply ℓ} → (Δ₁ ≡ Δ₀) → Δ₀ ⧟ Δ₁
  ≡to⧟ {Δ₀ = Δ₀} {Δ₁} p = subst (_⧟ Δ₁) p (id Δ₁)

  swap : (Δ₀ Δ₁ : Supply ℓ) → (Δ₀ ⊗ Δ₁) ⧟ Δ₁ ⊗ Δ₀
  swap Δ₀ Δ₁ = ≡to⧟ (comm-++ Δ₁ Δ₀)

  unitr : (Δ : Supply ℓ) → Δ ⊗ ◇ ⧟ Δ
  unitr Δ = ≡to⧟ (sym (unitr-++ Δ))

  unitr' : (Δ : Supply ℓ) → Δ ⧟ Δ ⊗ ◇
  unitr' Δ = ≡to⧟ (unitr-++ Δ)

  assoc : (Δ₀ Δ₁ Δ₂ : Supply ℓ) → (Δ₀ ⊗ Δ₁) ⊗ Δ₂ ⧟ Δ₀ ⊗ Δ₁ ⊗ Δ₂
  assoc Δ₀ Δ₁ Δ₂ = ≡to⧟ (assoc-++ Δ₀ Δ₁ Δ₂)

  assoc' : (Δ₀ Δ₁ Δ₂ : Supply ℓ) → Δ₀ ⊗ Δ₁ ⊗ Δ₂ ⧟ (Δ₀ ⊗ Δ₁) ⊗ Δ₂
  assoc' Δ₀ Δ₁ Δ₂ = ≡to⧟ (sym (assoc-++ Δ₀ Δ₁ Δ₂))

  unitl : (Δ : Supply ℓ) → (◇ ⊗ Δ) ⧟ Δ
  unitl Δ = ≡to⧟ refl

  unitl' : (Δ : Supply ℓ) → Δ ⧟ (◇ ⊗ Δ)
  unitl' Δ = ≡to⧟ refl





  _^_ : Supply ℓ → ℕ → Supply ℓ
  Δ ^ zero = ◇
  Δ ^ (suc n) = Δ ⊗ (Δ ^ n)

  infixl 50 _^_

  ⧟^ : {Δ₀ Δ₁ : Supply ℓ} → (m : ℕ) → Δ₀ ⧟ Δ₁ → (Δ₀ ^ m) ⧟ (Δ₁ ^ m)
  ⧟^ zero δ = id (◇)
  ⧟^ (suc m) δ = δ ⊗ᶠ (⧟^ m δ)

  ◇^ : (m : ℕ) → _⧟_ (◇ ^ m) ◇
  ◇^ zero = id _
  ◇^ (suc m) = (id ◇) ⊗ᶠ (◇^ m)

  ◇^' : (m : ℕ) → _⧟_ ◇ (◇ ^ m)
  ◇^' zero = id ◇
  ◇^' (suc m) = ◇^' m



  ⊗^ :  {X Y : Supply ℓ} (m : ℕ) → (X ⊗ Y) ^ m ⧟ X ^ m ⊗ Y ^ m
  ⊗^ zero = unitl' ◇
  ⊗^ {X} {Y} (suc m) = assoc (X ⊗ X ^ m) Y (Y ^ m) ∘ (assoc' X (X ^ m) Y) ⊗ᶠ id (Y ^ m) ∘ id X ⊗ᶠ swap Y (X ^ m) ⊗ᶠ id (Y ^ m) ∘ (assoc X Y (X ^ m) ⊗ᶠ id (Y ^ m) ∘ assoc' (X ⊗ Y) (X ^ m) (Y ^ m) ∘ assoc' X Y (X ^ m ⊗ Y ^ m)) ∘ assoc X Y (X ^ m ⊗ Y ^ m) ∘ id (X ⊗ Y) ⊗ᶠ (⊗^ {X} {Y} m) 


  aaasoc : (X Y Z W : Supply ℓ) → X ⊗ Y ⊗ Z ⊗ W ⧟ (X ⊗ Y ⊗ Z) ⊗ W
  aaasoc X Y Z W = assoc X Y Z ⊗ᶠ id W ∘ assoc' (X ⊗ Y) Z W ∘ assoc' X Y (Z ⊗ W)

  ⊗^' :  {X Y : Supply ℓ} (m : ℕ) → X ^ m ⊗ Y ^ m ⧟ (X ⊗ Y) ^ m
  ⊗^' zero = id ◇
  ⊗^' {X} {Y} (suc m) = 
    (id (X ⊗ Y) ⊗ᶠ IH)
    ∘ assoc' X Y (X ^ m ⊗ Y ^ m)
    ∘ id X ⊗ᶠ assoc Y (X ^ m) (Y ^ m)
    ∘ assoc X (Y ⊗ X ^ m) (Y ^ m)
    ∘ id X ⊗ᶠ swap (X ^ m) Y ⊗ᶠ id (Y ^ m)
    ∘ aaasoc X (X ^ m) Y (Y ^ m)
    ∘ assoc X (X ^ m) (Y ⊗ Y ^ m)
    where IH = ⊗^' {X = X} {Y} m


  exp : (Δ₀ Δ₁ : Supply ℓ) (n : ℕ) → Δ₀ ^ n ⊗ Δ₁ ^ n ⧟ (Δ₀ ⊗ Δ₁) ^ n
  exp Δ₀ Δ₁ zero = id ◇
  exp X Y (suc n) =
    id (X ⊗ Y) ⊗ᶠ (exp X Y n)
    ∘ assoc' X Y (X ^ n ⊗ Y ^ n)
    ∘ id X ⊗ᶠ assoc Y (X ^ n) (Y ^ n)
    ∘ assoc X (Y ⊗ X ^ n) (Y ^ n)
    ∘ id X ⊗ᶠ swap (X ^ n) (Y) ⊗ᶠ id (Y ^ n)
    ∘ aaasoc X (X ^ n) Y (Y ^ n)
    ∘ assoc X (X ^ n) (Y ⊗ Y ^ n)


  expplus : (X : Supply ℓ) (m n : ℕ) → X ^ (m + n) ⧟ X ^ n ⊗ X ^ m
  expplus X zero n = unitr' (X ^ n)
  expplus X (suc m) n = assoc (X ^ n) X (X ^ m) ∘ swap X (X ^ n) ⊗ᶠ id (X ^ m) ∘ assoc' X _ _ ∘ id X ⊗ᶠ IH
    where
    IH = expplus X m n

  explaw : (X : Supply ℓ) (m n : ℕ) → X ^ (m · n) ⧟ X ^ m ^ n
  explaw X zero n = ◇^' n
  explaw X (suc m) n =  ⊗^' {X = X} {X ^ m} n ∘ swap (X ^ m ^ n) (X ^ n) ∘ IH ⊗ᶠ id ( X ^ n ) ∘ expplus X n (m · n)
    where IH = explaw X m n



module LinearTypes {ℓ : Level} where
  open import Base public
  open import Linear public
  open Lemmas {ℓ} _⧟_ _∘_ _⊗ᶠ_ id public

module LinearHOTypes {ℓ : Level} where
  open import Base public
  open import LinearHO public
  open Lemmas {ℓ} _⧟_ _∘_ _⊗ᶠ_ id public

