{-# OPTIONS --cubical --allow-unsolved-metas #-}

module List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.List hiding ([_]) renaming (elim to elimList)
open import Cubical.Data.Bool

open import Prelude
open import Computing
open import Deriv
open import Functions



module _ {A : Type} where
  null : List A → Bool
  null [] = true
  null (_ ∷ _) = false

  shead : (a : A) → (xs : List A) → η xs ⊗ (if null xs then η a else ◇) ⊩₁ A × List A
  shead a [] = ap (swap (η []) (η a)) (ap ω, (ax (a , [])))
  shead a (x ∷ xs) = ap ι∷ (ap ω, (ax (x , xs)))


module _ {ℓ}{A : Type ℓ} {C : Type ℓ} where
  recList : (m : ℕ)
    → {Δ₀ Δ₁ : sply ℓ}
    → (Δ₀ ⊩₁ C)
    → (Δ₁ ⊩ Π m A λ _ → (Π 1 C (λ _ → C , η)))
    → (xs : List A) → (η xs) ^ m ⊗ Δ₁ ^ (length xs) ⊗ Δ₀ ⊩₁ C
  recList m {Δ₀} J f [] = ap ( ((◇^ m) ⇒∘ ⇒^ m ι[]) ⇒⊗ (id Δ₀)) J
  recList m {Δ₀} {Δ₁} J f (x ∷ xs) = ap ( sndatt ⇒∘ fstatt) apprec
    where
    test : Δ₁ ⊗ η x ^ m ⊩ Π 1 C (λ _ → C , η)
    test = ΠApp m f (ax x) -- ΠE m f (ax x)

    apprec : (Δ₁ ⊗ η x ^ m) ⊗ (η xs ^ m ⊗ Δ₁ ^ length xs ⊗ Δ₀) ^ 1 ⊩₁ C
    apprec = ΠApp {Δ = η} 1 test (recList m {Δ₀ = Δ₀} J f xs)

    fstatt :
      η (x ∷ xs) ^ m ⊗ (Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀ ⇒
      (η x ^ m ⊗ η xs ^ m) ⊗ (Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀
        -- (Δ₁ ⊗ η x ^ m) ⊗ (η xs ^ m ⊗ Δ₁ ^ length xs ⊗ Δ₀) ^ 1
    fstatt = ((⊗^ m) ⇒∘ (⇒^ m (ι∷ {x = x} {xs = xs}))) ⇒⊗ (id ((Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀))

    sndatt : (η x ^ m ⊗ η xs ^ m) ⊗ (Δ₁ ⊗ Δ₁ ^ length xs) ⊗ Δ₀ ⇒
      (Δ₁ ⊗ η x ^ m) ⊗ (η xs ^ m ⊗ Δ₁ ^ length xs ⊗ Δ₀) ⊗ ◇
    sndatt = {!!} ⇒∘ (swap (η x ^ m ⊗ η xs ^ m) Δ₁) ⇒⊗ (id $ Δ₁ ^ length xs ⊗ Δ₀) ⇒∘ {!assoc!} ⇒∘ (id (η x ^ m ⊗ η xs ^ m) ⇒⊗ assoc Δ₁ (Δ₁ ^ length xs) Δ₀)


module _ {A : Type} where
  cons : ∀{Δ₀ Δ₁} → Δ₀ ⊩₁ A → Δ₁ ⊩₁ List A → Δ₀ ⊗ Δ₁ ⊩₁ List A
  cons (x , δ₀) (xs , δ₁) = x ∷ xs , ω∷ ⇒∘ (δ₀ ⇒⊗ δ₁)


  nilᵒ : ◇ ⊩₁ List A
  nilᵒ = ap ω[] (ax [])


  consᵒ : ◇ ⊩ Π 1 A (λ _ → Π 1 (List A) (λ _ → List A , η))
  consᵒ = ΠI 1 (λ x → ΠI {Δ = η} 1 (λ xs → ap ω∷ (ax (x ∷ xs))))


module _ {A B : Type} where
  map' : (m : ℕ) ((f , δ) : Π' m A (λ _ → B , η) ) (xs : List A) 
       → (η xs) ^ m ⊗ ． δ  ^ (length xs) ⊩₁ List B
  map' m (f , δ) xs = ap (assoc (η xs ^ m) _ _  ⇒∘ unitr⇐ (η xs ^ m ⊗ ． δ ^ length xs))
    (recList m {Δ₀ = ◇} {Δ₁ = ． δ} nilᵒ (ΠI m (λ x → ap (unitr⇐ ((lf m η f) ⊗ (η x ^ m)) ) (ΠApp {Δ = lf 1 η} 1 consᵒ (ΠApp m (ax f) (ax x))))) xs)
