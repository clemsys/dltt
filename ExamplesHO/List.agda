{-# OPTIONS --cubical --safe #-}
module ExamplesHO.List where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map ; foldr)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Core
open import FunctionsHO
open LinearHOTypes


private
  variable
    ℓ : Level


-- We can use pattern matching to eliminate lists
module _ {A : Type ℓ} where
  null : List A → Bool
  null [] = true
  null (_ ∷ _) = false

  -- there is a unique function with the below type signature
  shead : (a : A) → (xs : List A) → η xs ⊗ (if null xs then η a else ◇) ⊩₁ A × List A
  shead a [] = ap (swap (η []) (η a)) (ap ω, (ax (a , [])))
  shead a (x ∷ xs) = ap ι∷ (ap ω, (ax (x , xs)))


  rep : (x : A) → (m : ℕ) → η x ^ m ⊩₁ List A
  rep x zero = ap ω[] (ax [])
  rep x (suc m) = ap (unitr' _) (ΠApp {Δ₀ = η x} {Δ = η} 1 (ΠI {Δ = η} 1 (λ ys → ap ω∷ (ax (x ∷ ys)))) (rep x m))

-- we define a more general recursor for lists
module _ {ℓ}{A : Type ℓ} {C : Type ℓ} where
  recList : (m : ℕ) {Δ₀ Δ₁ : Supply ℓ}
    → (Δ₀ ⊩₁ C)
    → (Δ₁ ⊩ Π m A λ _ → (Π 1 C (λ _ → C , η)))
    → (xs : List A) → (η xs) ^ m ⊗ Δ₁ ^ (length xs) ⊗ Δ₀ ⊩₁ C
  recList m {Δ₀} J f [] = ap ( ((◇^ m) ∘ ⧟^ m ι[]) ⊗ᶠ (id Δ₀)) J
  recList m {Δ₀} {Δ₁} J f (x ∷ xs) = ap (prod₂ ∘ prod₁) (ΠApp 1 (ΠApp m f (ax x)) (recList m J f xs))
    where
    prod₁ :
      η (x ∷ xs) ^ m ⊗ (Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀ ⧟
      (η x ^ m ⊗ η xs ^ m) ⊗ (Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀
    prod₁ = ((⊗^ m) ∘ (⧟^ m (ι∷ {x = x} {xs = xs}))) ⊗ᶠ (id ((Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀))

    prod₂ : (η x ^ m ⊗ η xs ^ m) ⊗ (Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀ ⧟
      (Δ₁ ⊗ η x ^ m) ⊗ (η xs ^ m ⊗ Δ₁ ^ length xs ⊗ Δ₀) ⊗ ◇
    prod₂ = id (Δ₁ ⊗ η x ^ m) ⊗ᶠ unitr' _ ∘ assoc' Δ₁ (η x ^ m) (η xs ^ m ⊗ Δ₁ ^ length xs ⊗ Δ₀) ∘ id Δ₁ ⊗ᶠ assoc (η x ^ m) (η xs ^ m) (Δ₁ ^ length xs ⊗ Δ₀) ∘ assoc (Δ₁) (η x ^ m ⊗ η xs ^ m) (Δ₁ ^ length xs ⊗ Δ₀)  ∘ (swap (η x ^ m ⊗ η xs ^ m) Δ₁) ⊗ᶠ (id (Δ₁ ^ length xs ⊗ Δ₀)) ∘ assoc' (η x ^ m ⊗ η xs ^ m) Δ₁ (Δ₁ ^ length xs ⊗ Δ₀) ∘ (id (η x ^ m ⊗ η xs ^ m) ⊗ᶠ assoc Δ₁ (Δ₁ ^ length xs) Δ₀)


-- the list constructors as linear functions
module _ {A : Type ℓ} where
  nilᵒ : ◇ ⊩₁ List A
  nilᵒ = ap ω[] (ax [])

  consᵒ : ◇ ⊩ Π 1 A (λ _ → Π 1 (List A) (λ _ → List A , η))
  consᵒ = ΠI 1 (λ x → ΠI {Δ = η} 1 (λ xs → ap ω∷ (ax (x ∷ xs))))


-- a mapping function for lists which tracks the number of times the mapped function is used.
module _ {A B : Type ℓ} where
  map : (m : ℕ) ((f , δ) : Π' m A (λ _ → B , η) ) (xs : List A)
       → (η xs) ^ m ⊗ ． δ  ^ (length xs) ⊩₁ List B
  map m (f , δ) xs = ap prod₁ (recList m nilᵒ (ΠI m (λ x → ap (prod₂ x) (ΠApp {Δ = lf 1 η} 1 consᵒ (ΠApp m (ax f) (ax x))))) xs)
    where
    prod₁ = (assoc (η xs ^ m) _ _  ∘ unitr' (η xs ^ m ⊗ ． δ ^ length xs))
    prod₂ : (x : A) → ． δ ⊗ η x ^ m ⧟ ◇ ⊗ ( ． δ ⊗ η x ^ m) ^ 1
    prod₂ x = (unitr' ((lf m η f) ⊗ (η x ^ m)))


