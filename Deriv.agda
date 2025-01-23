{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Deriv where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_^_)

open import Computing
-- open import Model



dsply : (ℓ : Level) → Type (ℓ-suc ℓ)
dsply ℓ = Σ[ A ∈ Type ℓ ] (A → sply ℓ)

private
  variable
    ℓ : Level

-- TODO deriv assoc 
unitr⇒ : ∀ {ℓ} → (Δ : sply ℓ) → (Δ ⊗ ◇) ⇒ Δ
unitr⇒ Δ = unitl⇒ Δ ⇒∘ swap Δ ◇
unitr⇐ : ∀ {ℓ} → (Δ : sply ℓ) → Δ ⇒ Δ ⊗ ◇
unitr⇐ Δ = swap ◇ Δ ⇒∘ unitl⇐ Δ

Λₒ-syntax : (A : Type ℓ) → (A → sply ℓ) → sply (ℓ)
Λₒ-syntax = Λₒ

syntax Λₒ-syntax A (λ x → Δ) = Λₒ[ x ∈ A ] Δ




_^_ : sply ℓ → ℕ → sply ℓ
_^_ Δ zero = ◇
_^_ Δ (suc n) = Δ ⊗ (Δ ^ n)
infixl 50 _^_

-- _^_ : {A : Type} (x : A) → ℕ → sply
-- x ^ m = (η x) ^^ m

-- _^'_ : {Δ : sply} → ⟨ Δ ⟩ → ℕ → sply
-- _^'_ {Δ} _ m = Δ ^^ m
-- infixl 50 _^'_


⇒^ : ∀{ℓ}{Δ₀ Δ₁ : sply ℓ} → (m : ℕ) → Δ₀ ⇒ Δ₁ → (Δ₀ ^ m) ⇒ (Δ₁ ^ m)
⇒^ zero δ = id (◇)
⇒^ (suc m) δ = δ ⇒⊗ (⇒^ m δ)

◇^ : ∀{ℓ} → (m : ℕ) → _⇒_ {ℓ} (◇ ^ m) ◇
◇^ zero = id _
◇^ (suc m) = {!!} -- ◇^ m

⊗^ :  ∀{ℓ}{X Y : sply ℓ} (m : ℕ) → (X ⊗ Y) ^ m ⇒ X ^ m ⊗ Y ^ m
⊗^ zero = {!!} -- id ◇
⊗^ {X} {Y} (suc m) = {!⊗^ {X} {Y} m !}




_⊩_ : sply ℓ → dsply ℓ → Type (ℓ-suc ℓ)
Δ ⊩ (A , Δ₁) = Σ[ a ∈ A ] (Δ ⇒ Δ₁ a)
infixl -100 _⊩_

_⊩₁_ : sply ℓ → Type ℓ → Type (ℓ-suc ℓ)
Δ ⊩₁ A = Δ ⊩ (A , η)
infixl -100 _⊩₁_


ax : {(A , Δ) : dsply ℓ} → (a : A) → Δ a ⊩ (A , Δ)
ax {_} {(A , Δ)} a = a , (id (Δ a))

ap : {Δ₀ Δ₁ : sply ℓ} {A : dsply ℓ}
  → (δ : Δ₁ ⇒ Δ₀)
  → Δ₀ ⊩ A
  → Δ₁ ⊩ A
ap δ₁ (a , δ₂) = a , δ₂ ⇒∘ δ₁


lf : {A : Type ℓ} {B : A → Type ℓ} → (m : ℕ) → (Δ₁ : {x : A} → B x → sply ℓ) → ((x : A) → B x) → sply ℓ
lf {_}  {A} m Δ₁ f =  Λₒ[ x ∈ A ] [ (η x) ^ m , Δ₁ (f x) ]


-- Π' : (m : ℕ) → (A : Type) (B : A → Type) (Δ₁ : {x : A} → B x → sply) → dsply
-- Π' m A B Δ₁ = ((x : A) → B x) , lf m Δ₁

Π : (m : ℕ) → (A : Type ℓ) (B : (x : A) → dsply ℓ) → dsply ℓ
Π m A BΔ = ((x : A) → fst (BΔ x)) , λ f → Λₒ[ x ∈ A ] [ (η x) ^ m , snd (BΔ x) (f x) ]

-- lf m λ {x} → snd (BΔ x)


-- Π : (m : ℕ) → (A : Type) (B : A → Type) (Δ₁ : {x : A} → B x → sply) → Type
-- Π m A B Δ₁ = Σ[ f ∈ ((x : A) → B x) ] ⟨ lf m Δ₁ f ⟩




-- record ⟨_⟩ (A : Type) : Type where
--   constructor ′
--   field
--     {f} : A
--     Δ : A → sply

-- inj : ((A , Δ) : dsply) → ⟨ A ⟩
-- inj (A , Δ) = ′ Δ


-- record ⟨_⟩ {A : Type} (a : A) : Type where
--   elem = a
-- open ⟨_⟩ public
-- s : {A : Type} → (a : A) -> ⟨ a ⟩
-- s _ = _

-- ． : {A : Type} → (a : A) → ⟨ a ⟩ → A
-- ． {A} a _ = a

-- infixl -100 ′_
-- ′_ : dsply → Type
-- ′ (A , Δ) = ⟨ A , Δ ⟩



ΠI : {A : Type ℓ} {B : A → Type ℓ} {Δ₀ : sply ℓ} {Δ : {x : A} → B x → sply ℓ} (m : ℕ)
  → ((x : A) → Δ₀ ⊗ (η x) ^ m ⊩ (B x) , Δ)
  → Δ₀ ⊩ Π m A (λ x → (B x) , Δ)
ΠI {_} {A} m J = (λ x → fst (J x)) , λₒ (λ x → cur (snd (J x)))

ΠE' : {A : Type ℓ} {B : A → Type ℓ} {Δ : sply ℓ} {Δ₁ : {x : A} → B x → sply ℓ} (m : ℕ)
  → Δ ⊩ Π m A (λ x → (B x) , Δ₁)
  → ((x : A) → Δ ⊗ (η x) ^ m ⊩ (B x) , Δ₁)
ΠE' {_} {A} m (b , f) x = (b x) , (unc (λₒ⁻¹ f x))


ΠApp : {A : Type ℓ} {B : A → Type ℓ} {Δ₀ Δ₁ : sply ℓ} {Δ : {x : A} → B x → sply ℓ} (m : ℕ)
  → Δ₀ ⊩ Π m A (λ x → (B x) , Δ)
  → ((a , _) : Δ₁ ⊩₁ A)
  → (Δ₀ ⊗ Δ₁ ^ m ⊩ (B a) , Δ)
ΠApp {_} {A} {B} {Δ₀} m J (a , p) = ap (id Δ₀ ⇒⊗ ⇒^ m p) (ΠE' m J a)





record ⟨_⟩ (Δ : sply ℓ) : Type ℓ where
  elem = Δ
open ⟨_⟩ public
s : (Δ : sply ℓ) -> ⟨ Δ ⟩
s _ = _

． : ∀{Δ} → ⟨ Δ ⟩ → sply ℓ
． {_} {Δ} _ = Δ

Π' : (m : ℕ) → (A : Type ℓ) (B : (x : A) → dsply ℓ) → Type ℓ
Π' m A BΔ = Σ[ f ∈ ((x : A) → fst (BΔ x)) ] ⟨ Λₒ[ x ∈ A ] [ (η x) ^ m , snd (BΔ x) (f x) ] ⟩

