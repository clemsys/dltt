{-# OPTIONS --cubical --safe #-}

module Deriv where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_^_)

-- This file type-checks with either the computing or the free implementation of the axioms included
-- (when using Free, we need to remove the --safe flag from this file since the free model requires postulates)
open import Computing
-- open import Free

private
  variable
    ℓ : Level

Λₒ-syntax : (A : Type ℓ) → (A → sply ℓ) → sply (ℓ)
Λₒ-syntax = Λₒ

syntax Λₒ-syntax A (λ x → Δ) = Λₒ[ x ∈ A ] Δ

dsply : (ℓ : Level) → Type (ℓ-suc ℓ)
dsply ℓ = Σ[ A ∈ Type ℓ ] (A → sply ℓ)


_^_ : sply ℓ → ℕ → sply ℓ
_^_ Δ zero = ◇
_^_ Δ (suc n) = Δ ⊗ (Δ ^ n)
infixl 50 _^_


⊸^ : ∀{ℓ}{Δ₀ Δ₁ : sply ℓ} → (m : ℕ) → Δ₀ ⊸ Δ₁ → (Δ₀ ^ m) ⊸ (Δ₁ ^ m)
⊸^ zero δ = id (◇)
⊸^ (suc m) δ = δ ⊸⊗ (⊸^ m δ)


_⊩_ : sply ℓ → dsply ℓ → Type (ℓ-suc ℓ)
Δ ⊩ (A , Δ₁) = Σ[ a ∈ A ] (Δ ⊸ Δ₁ a)
infixl -100 _⊩_

_⊩₁_ : sply ℓ → Type ℓ → Type (ℓ-suc ℓ)
Δ ⊩₁ A = Δ ⊩ (A , η)
infixl -100 _⊩₁_


ax : {(A , Δ) : dsply ℓ} → (a : A) → Δ a ⊩ (A , Δ)
ax {_} {(A , Δ)} a = a , (id (Δ a))

ap : {Δ₀ Δ₁ : sply ℓ} {A : dsply ℓ}
  → (δ : Δ₁ ⊸ Δ₀)
  → Δ₀ ⊩ A
  → Δ₁ ⊩ A
ap δ₁ (a , δ₂) = a , δ₂ ⊸∘ δ₁



Π : (m : ℕ) → (A : Type ℓ) (B : (x : A) → dsply ℓ) → dsply ℓ
Π m A BΔ = ((x : A) → fst (BΔ x)) , λ f → Λₒ[ x ∈ A ] [ (η x) ^ m , snd (BΔ x) (f x) ]


ΠI : {A : Type ℓ} {B : A → Type ℓ} {Δ₀ : sply ℓ} {Δ : {x : A} → B x → sply ℓ} (m : ℕ)
  → ((x : A) → Δ₀ ⊗ (η x) ^ m ⊩ (B x) , Δ)
  → Δ₀ ⊩ Π m A (λ x → (B x) , Δ)
ΠI {_} {A} m J = (λ x → fst (J x)) , λₒ (λ x → cur (snd (J x)))

ΠE : {A : Type ℓ} {B : A → Type ℓ} {Δ : sply ℓ} {Δ₁ : {x : A} → B x → sply ℓ} (m : ℕ)
  → Δ ⊩ Π m A (λ x → (B x) , Δ₁)
  → ((x : A) → Δ ⊗ (η x) ^ m ⊩ (B x) , Δ₁)
ΠE {_} {A} m (b , f) x = (b x) , (unc (λₒ⁻¹ f x))


ΠApp : {A : Type ℓ} {B : A → Type ℓ} {Δ₀ Δ₁ : sply ℓ} {Δ : {x : A} → B x → sply ℓ} (m : ℕ)
  → Δ₀ ⊩ Π m A (λ x → (B x) , Δ)
  → ((a , _) : Δ₁ ⊩₁ A)
  → (Δ₀ ⊗ Δ₁ ^ m ⊩ (B a) , Δ)
ΠApp {_} {A} {B} {Δ₀} m J (a , p) = ap (id Δ₀ ⊸⊗ ⊸^ m p) (ΠE m J a)






-- we introduce a singleton type for supplies to embed a supply as a type
record ⟨_⟩ (Δ : sply ℓ) : Type ℓ where
  elem = Δ
open ⟨_⟩ public
s : (Δ : sply ℓ) -> ⟨ Δ ⟩
s _ = _

． : ∀{Δ} → ⟨ Δ ⟩ → sply ℓ
． {_} {Δ} _ = Δ


-- we use the singleton type to include functions as resources in supplies
Π' : (m : ℕ) → (A : Type ℓ) (B : (x : A) → dsply ℓ) → Type ℓ
Π' m A BΔ = Σ[ f ∈ ((x : A) → fst (BΔ x)) ] ⟨ Λₒ[ x ∈ A ] [ (η x) ^ m , snd (BΔ x) (f x) ] ⟩


-- sometimes we need to guide the type-checker a bit, use the below shortcut
lf : {A : Type ℓ} {B : A → Type ℓ} → (m : ℕ) → (Δ₁ : {x : A} → B x → sply ℓ) → ((x : A) → B x) → sply ℓ
lf {_}  {A} m Δ₁ f =  Λₒ[ x ∈ A ] [ (η x) ^ m , Δ₁ (f x) ]
