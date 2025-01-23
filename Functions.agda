{-# OPTIONS --cubical --safe #-}

module Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Computing
open import Deriv


private
  variable
    ℓ : Level



lid : ∀{ℓ}{A : Type ℓ} → ◇ ⊩ Π 1 A λ _ → A , η
lid = ΠI {Δ = η} 1 (λ x → ax x)




basic : {A : Type} → (x : A) → Σ[ b ∈ A × A ] (η x ⊗ η x ⊸ η b)
basic x = (x , x) , ω, ⊸∘ id (η x ⊗ η x)

dupl : {A : Type} → (x : A) → η x ⊗ η x ⊩₁ A × A
dupl x = ap ω, (ax (x , x))

copy : {A : Type} → ◇ ⊩ Π 2 A  (λ _ → A × A , η)
copy = ΠI {Δ = η} 2 λ x → ap ω, (ax (x , x))


⊗^ :  ∀{ℓ}{X Y : sply ℓ} (m : ℕ) → (X ⊗ Y) ^ m ⊸ X ^ m ⊗ Y ^ m
⊗^ zero = unitl⊸' ◇
⊗^ {ℓ} {X} {Y} (suc m) =  assoc (X ⊗ X ^ m) Y (Y ^ m) ⊸∘ (assoc' X (X ^ m) Y) ⊸⊗ id (Y ^ m) ⊸∘ id X ⊸⊗ swap Y (X ^ m) ⊸⊗ id (Y ^ m) ⊸∘ (assoc X Y (X ^ m) ⊸⊗ id (Y ^ m) ⊸∘ assoc' (X ⊗ Y) (X ^ m) (Y ^ m) ⊸∘ assoc' X Y (X ^ m ⊗ Y ^ m)) ⊸∘ assoc X Y (X ^ m ⊗ Y ^ m) ⊸∘ id (X ⊗ Y) ⊸⊗ (⊗^ {ℓ} {X} {Y} m) 



aaasoc : (X Y Z W : sply ℓ) → X ⊗ Y ⊗ Z ⊗ W ⊸ (X ⊗ Y ⊗ Z) ⊗ W
aaasoc X Y Z W = assoc X Y Z ⊸⊗ id W ⊸∘ assoc' (X ⊗ Y) Z W ⊸∘ assoc' X Y (Z ⊗ W)

⊗^' :  ∀{ℓ}{X Y : sply ℓ} (m : ℕ) → X ^ m ⊗ Y ^ m ⊸ (X ⊗ Y) ^ m 
⊗^' zero = id ◇
⊗^' {ℓ} {X} {Y} (suc m) = (id (X ⊗ Y) ⊸⊗ IH) ⊸∘ assoc' X Y (X ^ m ⊗ Y ^ m) ⊸∘ id X ⊸⊗ assoc Y (X ^ m) (Y ^ m) ⊸∘ assoc X (Y ⊗ X ^ m) (Y ^ m) ⊸∘ id X ⊸⊗ swap (X ^ m) Y ⊸⊗ id (Y ^ m) ⊸∘ aaasoc X (X ^ m) Y (Y ^ m) ⊸∘ assoc X (X ^ m) (Y ⊗ Y ^ m)
  where IH = ⊗^' {X = X} {Y} m


exp : (Δ₀ Δ₁ : sply ℓ) (n : ℕ) → Δ₀ ^ n ⊗ Δ₁ ^ n ⊸ (Δ₀ ⊗ Δ₁) ^ n
exp Δ₀ Δ₁ zero = id ◇
exp X Y (suc n) =  id (X ⊗ Y) ⊸⊗ (exp X Y n) ⊸∘ assoc' X Y (X ^ n ⊗ Y ^ n) ⊸∘ id X ⊸⊗ assoc Y (X ^ n) (Y ^ n) ⊸∘ assoc X (Y ⊗ X ^ n) (Y ^ n) ⊸∘ id X ⊸⊗ swap (X ^ n) (Y) ⊸⊗ id (Y ^ n) ⊸∘ aaasoc X (X ^ n) Y (Y ^ n) ⊸∘ assoc X (X ^ n) (Y ⊗ Y ^ n)
-- exp Δ₀ Δ₁ n


expplus : (X : sply ℓ) (m n : ℕ) → X ^ (m + n) ⊸ X ^ n ⊗ X ^ m
expplus X zero n = unitr⊸' (X ^ n)
expplus X (suc m) n = assoc (X ^ n) X (X ^ m) ⊸∘ swap X (X ^ n) ⊸⊗ id (X ^ m) ⊸∘ assoc' X _ _ ⊸∘ id X ⊸⊗ IH
  where
  IH = expplus X m n

explaw : (X : sply ℓ) (m n : ℕ) → X ^ (m · n) ⊸ X ^ m ^ n
explaw X zero n = ◇^' n
explaw X (suc m) n =  ⊗^' {X = X} {X ^ m} n ⊸∘ swap (X ^ m ^ n) (X ^ n) ⊸∘ IH ⊸⊗ id ( X ^ n ) ⊸∘ expplus X n (m · n)
  where IH = explaw X m n

-- ⊗^ {X = X} {X ^ m} n


module _ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : {x : A} → B x → Type ℓ} where
  composemn : {Δ₀ Δ₁ : sply ℓ} {m n : ℕ} →
    ({x : A} → Δ₁ ⊩ Π n (B x) (λ y → C y , η))
    → ((f , _) : Δ₀ ⊩ Π m A (λ x → B x , η))
    → Δ₁ ⊗ Δ₀ ^ n ⊩ Π (m · n) A (λ x → C (f x) , η)
  composemn {Δ₀} {Δ₁} {m = m} {n = n} J J' = ΠI (m · n) (λ x → ap (id Δ₁ ⊸⊗ (exp Δ₀ (η x ^ m) n ⊸∘ id (Δ₀ ^ n) ⊸⊗ explaw (η x) m n) ⊸∘ assoc Δ₁ (Δ₀ ^ n) (η x ^ (m · n))) $ ΠApp {Δ = η} n J (ΠApp {Δ = η} m J' (ax x)))

--exp Δ₀ (η x ^ m) n

copytwice : {A : Type} → ◇ ⊩ Π 4 A  (λ _ → (A × A) × (A × A) , η)
copytwice {A} = ap (unitr⊸ ◇) $ composemn {m = 2} {n = 2} (copy {A = A × A}) copy


module _ {ℓ} {A : Type ℓ} {B : A → Type ℓ} {C : {x : A} → B x → Type ℓ} {Δ : sply ℓ} where
  curryD :
    Δ ⊩ Π 1 (Σ A B) (λ (x , y) → C y , η)
    →  Δ ⊩ Π 1 A (λ x → Π 1 (B x) λ y → (C y) , η)
  curryD J = ΠI 1 (λ x → ΠI 1 (λ y → ap ((id Δ ⊸⊗ ω,) ⊸∘ assoc Δ _ _) $ ΠApp {Δ = η} 1 J (ax (x , y))))

  uncurryD :
    Δ ⊩ Π 1 A (λ x → Π 1 (B x) λ y → (C y) , η)
   → Δ ⊩ Π 1 (Σ A B) (λ (x , y) → C y , η)
  uncurryD J = ΠI 1 (λ (x , y) → ap ((assoc' Δ _ _) ⊸∘ (id Δ ⊸⊗ ι,)) (ΠApp {Δ = η} 1 (ΠApp 1 J (ax x)) (ax y)))
