{-# OPTIONS --cubical --safe #-}
module Linear where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Vec
open import Cubical.Data.Unit
open import Cubical.Data.Maybe

open import Cubical.Data.Nat public hiding (_^_)
open import Cubical.HITs.FiniteMultiset public hiding ([_]) renaming (FMSet to Bag ; [] to ◇ ; _∷_ to _⨾_ ; _++_ to _⊗_)

open import Base


module _ {ℓ : Level}  where
  infixl 0 _⧟_
  infixl 11 _⊗ᶠ_
  infixl 10 _∘_

  data _⧟_ : Supply ℓ → Supply ℓ → Type (ℓ-suc ℓ) where
    id : ∀ Δ → Δ ⧟ Δ
    _∘_ : ∀ {Δ₀ Δ₁ Δ₂} → Δ₁ ⧟ Δ₂ → Δ₀ ⧟ Δ₁ → Δ₀ ⧟ Δ₂
    _⊗ᶠ_ : ∀ {Δ₀ Δ₁ Δ₂ Δ₃} → Δ₀ ⧟ Δ₁ → Δ₂ ⧟ Δ₃ → Δ₀ ⊗ Δ₂ ⧟ Δ₁ ⊗ Δ₃

    cn, :  {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
      → η {A = Σ A B} (a , b) ⧟ (η a ⊗ η b)
    wk, :  {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
      → (η a ⊗ η b) ⧟ η {A = Σ A B} (a , b)

    cn[] : {A : Type ℓ} → (η {A = List A} []) ⧟ ◇
    wk[] : {A : Type ℓ} → ◇ ⧟ (η {A = List A} [])
    cn∷ : {A : Type ℓ} {x : A} {xs : List A} → η (x ∷ xs) ⧟ η x ⊗ η xs
    wk∷ : {A : Type ℓ} {x : A} {xs : List A} → η x ⊗ η xs ⧟ η (x ∷ xs)

    cnnothing : {A : Type ℓ} → (η {A = Maybe A} nothing) ⧟ ◇
    wknothing : {A : Type ℓ} → ◇ ⧟ (η {A = Maybe A} nothing)
    cnjust : {A : Type ℓ} {x : A} → η (just x) ⧟ η x
    wkjust : {A : Type ℓ} {x : A} → η x ⧟ η (just x)

    cn[]' : {A : Type ℓ} → (η {A = Vec A zero} []) ⧟ ◇
    wk[]' : {A : Type ℓ} → ◇ ⧟ (η {A = Vec A zero} [])
    cn∷' : {n : ℕ} {A : Type ℓ} {x : A} {xs : Vec A n} → η (x ∷ xs) ⧟ η x ⊗ η xs
    wk∷' : {n : ℕ} {A : Type ℓ} {x : A} {xs : Vec A n} → η x ⊗ η xs ⧟ η (x ∷ xs)


private
  variable
    ℓ : Level






module _ where
  _⊩_ : Supply ℓ → Type ℓ → Type (ℓ-suc ℓ)
  Δ ⊩ A = Σ[ a ∈ A ] (Δ ⧟ η a)
  infixl -100 _⊩_


module _ {A : Type ℓ} where
  ． : (a : A) → η a ⊩ A
  ． a = a , id (η a)

module _ {Δ₀ Δ₁ : Supply ℓ} {A : Type ℓ} where
  _by_ : Δ₀ ⊩ A → (Δ₁ ⧟ Δ₀) → Δ₁ ⊩ A
  (a , δ₂) by  δ₁ = a , δ₂ ∘ δ₁

  infixl -1000 _by_


