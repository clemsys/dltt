{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Prelude
open import Computing
open import Deriv


private
  variable
    ℓ : Level



lid : ∀{ℓ}{A : Type ℓ} → ◇ ⊩ Π 1 A λ _ → A , η
lid = ΠI {Δ = η} 1 (λ x → ax x)




basic : {A : Type} → (x : A) → Σ[ b ∈ A × A ] (η x ⊗ η x ⇒ η b)
basic x = (x , x) , ω, ⇒∘ id (η x ⊗ η x)

dupl : {A : Type} → (x : A) → η x ⊗ η x ⊩₁ A × A
dupl x = ap ω, (ax (x , x))

copy : {A : Type} → ◇ ⊩ Π 2 A  (λ _ → A × A , η)
copy = ΠI {Δ = η} 2 λ x → ap ω, (ax (x , x))


module _ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : {x : A} → B x → Type ℓ} where
  composemn : {Δ₀ Δ₁ : sply ℓ} {m n : ℕ} →
    ({x : A} → Δ₁ ⊩ Π n (B x) (λ y → C y , η))
    → ((f , _) : Δ₀ ⊩ Π m A (λ x → B x , η))
    → Δ₁ ⊗ Δ₀ ^ n ⊩ Π (m · n) A (λ x → C (f x) , η)
  composemn {Δ₀} {Δ₁} {m = m} {n = n} J J' = ΠI (m · n) (λ x → ap {!!} $ ΠApp {Δ = η} n J (ΠApp {Δ = η} m J' (ax x)))

copytwice : {A : Type} → ◇ ⊩ Π 4 A  (λ _ → (A × A) × (A × A) , η)
copytwice {A} = ap (unitr⇒ ◇) $ composemn {m = 2} {n = 2} (copy {A = A × A}) copy


module _ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : {x : A} → B x → Type ℓ} {Δ : sply ℓ} where
  curryD :
    Δ ⊩ Π 1 (Σ A B) (λ (x , y) → C y , η)
    →  Δ ⊩ Π 1 A (λ x → Π 1 (B x) λ y → (C y) , η)
  curryD J = ΠI 1 (λ x → ΠI 1 (λ y → ap ((id Δ ⇒⊗ ω,) ⇒∘ assoc Δ _ _) $ ΠApp {Δ = η} 1 J (ax (x , y))))

  uncurryD :
    Δ ⊩ Π 1 A (λ x → Π 1 (B x) λ y → (C y) , η)
   → Δ ⊩ Π 1 (Σ A B) (λ (x , y) → C y , η)
  uncurryD J = ΠI 1 (λ (x , y) → ap ((assoc' Δ _ _) ⇒∘ (id Δ ⇒⊗ ι,)) (ΠApp {Δ = η} 1 (ΠApp 1 J (ax x)) (ax y)))
