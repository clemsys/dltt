{-# OPTIONS --cubical --safe #-}

module FunctionsHO where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)

open import Core
open LinearHOTypes


private
  variable
    ℓ : Level




Π : ℕ → (A : Type ℓ) → (A → DSupply ℓ) → DSupply ℓ
Π m A BΔ .fst = (x : A) → fst (BΔ x)
Π m A BΔ .snd f = Λₒ[ x ∈ A ] [ (η x) ^ m , snd (BΔ x) (f x) ]



ΠI : {A : Type ℓ} {B : A → Type ℓ} {Δ₀ : Supply ℓ} {Δ : {x : A} → B x → Supply ℓ} (m : ℕ)
  → ((x : A) → Δ₀ ⊗ (η x) ^ m ⊩ (B x) , Δ)
  → Δ₀ ⊩ Π m A (λ x → (B x) , Δ)
ΠI {_} {A} m J = (λ x → fst (J x)) , λₒ (λ x → cur (snd (J x)))


ΠE : {A : Type ℓ} {B : A → Type ℓ} {Δ : Supply ℓ} {Δ₁ : {x : A} → B x → Supply ℓ} (m : ℕ)
  → Δ ⊩ Π m A (λ x → (B x) , Δ₁)
  → ((x : A) → Δ ⊗ (η x) ^ m ⊩ (B x) , Δ₁)
ΠE {_} {A} m (b , f) x = b x , unc (λₒ⁻¹ f x)

ΠApp : {A : Type ℓ} {B : A → Type ℓ} {Δ₀ Δ₁ : Supply ℓ} {Δ : {x : A} → B x → Supply ℓ} (m : ℕ)
  → Δ₀ ⊩ Π m A (λ x → (B x) , Δ)
  → ((a , _) : Δ₁ ⊩₁ A)
  → (Δ₀ ⊗ Δ₁ ^ m ⊩ (B a) , Δ)
ΠApp {_} {A} {B} {Δ₀} m J (a , p) = ap (id Δ₀ ⊗ᶠ ⧟^ m p) (ΠE m J a) -- TODO wout ΠE



module _ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : {x : A} → B x → Type ℓ} where
  compose : {Δ₀ Δ₁ : Supply ℓ} ( m n : ℕ ) →
    ({x : A} → Δ₁ ⊩ Π n (B x) (λ y → C y , η))
    → ((f , _) : Δ₀ ⊩ Π m A (λ x → B x , η))
    → Δ₁ ⊗ Δ₀ ^ n ⊩ Π (m · n) A (λ x → C (f x) , η)
  compose {Δ₀} {Δ₁} m n J J' = ΠI (m · n) (λ x → ap (prod₁ x) (ΠApp {Δ = η} n J (ΠApp {Δ = η} m J' (ax x))))
    where
    prod₁ : (x : A) → (Δ₁ ⊗ Δ₀ ^ n) ⊗ η x ^ (m · n) ⧟ Δ₁ ⊗ (Δ₀ ⊗ η x ^ m) ^ n
    prod₁ x = id Δ₁ ⊗ᶠ (exp Δ₀ (η x ^ m) n ∘ id (Δ₀ ^ n) ⊗ᶠ explaw (η x) m n) ∘ assoc Δ₁ (Δ₀ ^ n) (η x ^ (m · n))

copy : {A : Type} → ◇ ⊩ Π 2 A  (λ _ → A × A , η)
copy = ΠI {Δ = η} 2 λ x → ap ω, (ax (x , x))

copytwice : {A : Type} → ◇ ⊩ Π 4 A  (λ _ → (A × A) × (A × A) , η)
copytwice {A} = ap (unitr ◇) (compose 2 2 (copy {A = A × A}) copy)


module _ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : {x : A} → B x → Type ℓ} {Δ : Supply ℓ} where
  curryD :
    Δ ⊩ Π 1 (Σ A B) (λ (x , y) → C y , η)
    →  Δ ⊩ Π 1 A (λ x → Π 1 (B x) λ y → (C y) , η)
  curryD J = ΠI 1 (λ x → ΠI 1 (λ y → ap (id Δ ⊗ᶠ ω, ∘ assoc Δ _ _) (ΠApp {Δ = η} 1 J (ax (x , y)))))

  uncurryD :
    Δ ⊩ Π 1 A (λ x → Π 1 (B x) λ y → (C y) , η)
   → Δ ⊩ Π 1 (Σ A B) (λ (x , y) → C y , η)
  uncurryD J = ΠI 1 (λ (x , y) → ap (assoc' Δ _ _ ∘ id Δ ⊗ᶠ ι,) (ΠApp {Δ = η} 1 (ΠApp 1 J (ax x)) (ax y)))



-- we introduce a singleton type for supplies to embed a supply as a type
record ⟨_⟩ (Δ : Supply ℓ) : Type ℓ where
  elem = Δ
open ⟨_⟩ public
s : (Δ : Supply ℓ) -> ⟨ Δ ⟩
s _ = _

． : ∀{Δ} → ⟨ Δ ⟩ → Supply ℓ
． {_} {Δ} _ = Δ


-- we use the singleton type to include functions as resources in supplies
Π' : (m : ℕ) → (A : Type ℓ) (B : (x : A) → DSupply ℓ) → Type ℓ
Π' m A BΔ = Σ[ f ∈ ((x : A) → fst (BΔ x)) ] ⟨ Λₒ[ x ∈ A ] [ (η x) ^ m , snd (BΔ x) (f x) ] ⟩


-- sometimes we need to guide the type-checker a bit, use the below shortcut
lf : {A : Type ℓ} {B : A → Type ℓ} → (m : ℕ) → (Δ₁ : {x : A} → B x → Supply ℓ) → ((x : A) → B x) → Supply ℓ
lf {_}  {A} m Δ₁ f =  Λₒ[ x ∈ A ] [ (η x) ^ m , Δ₁ (f x) ]

