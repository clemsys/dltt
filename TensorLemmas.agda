{-# OPTIONS --cubical --safe #-}

module TensorLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_^_)

open import Computing
open import Deriv


-- this file contains entirely straightforward operations and lemmas about ⊗ in
-- the future, we want to implement an Agda tactic which constructs many of the
-- productions automatically---in particular assoc and unit can be easily
-- mechanised with a simple normaliser




unitr⊸ : ∀ {ℓ} → (Δ : sply ℓ) → (Δ ⊗ ◇) ⊸ Δ
unitr⊸ Δ = unitl⊸ Δ ⊸∘ swap Δ ◇
unitr⊸' : ∀ {ℓ} → (Δ : sply ℓ) → Δ ⊸ Δ ⊗ ◇
unitr⊸' Δ = swap ◇ Δ ⊸∘ unitl⊸' Δ

assoc' : ∀{ℓ} (Δ₀ Δ₁ Δ₂ : sply ℓ) → Δ₀ ⊗ Δ₁ ⊗ Δ₂ ⊸ (Δ₀ ⊗ Δ₁) ⊗ Δ₂
assoc' x y z = ( swap z (x ⊗ y) ⊸∘ assoc z x y ⊸∘ swap x z ⊸⊗ id y ⊸∘ swap y (x ⊗ z) ⊸∘ (id y ⊸⊗ swap z x)  ⊸∘ assoc y z x) ⊸∘ swap x (y ⊗ z)


◇^ : ∀{ℓ} → (m : ℕ) → _⊸_ {ℓ} (◇ ^ m) ◇
◇^ zero = id _
◇^ (suc m) =  unitl⊸ ◇ ⊸∘ (id ◇) ⊸⊗ (◇^ m)

◇^' : ∀{ℓ} → (m : ℕ) → _⊸_ {ℓ} ◇ (◇ ^ m)
◇^' zero = id ◇
◇^' (suc m) = ◇^' m


private
  variable
    ℓ : Level

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
