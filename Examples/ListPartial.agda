{-# OPTIONS --cubical #-}
module Examples.ListPartial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map ; foldr)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Maybe


open import Core
open import Functions
open import Examples.List
open import Examples.Maybe

open LinearTypes


private
  variable
    ℓ : Level


module _ {A B : Type ℓ} where
  {-# NON_TERMINATING #-}
-- unfold₁ : ((x : B) → η x ⊩ Maybe (A × B)) → (x : B) → η x ⊩ List A
  unfold₁ : (B ⊸ Maybe (A × B)) → B ⊸ List A
  unfold₁ f x with f x
  ... | nothing , δ = []○ by cnnothing ∘ δ
  ... | (just (y , x')) , δ = ． y ∷◎ unfold₁ f x' by cn, ∘ cnjust ∘ δ
-- ... | (just (y , x')) , δ = y ∷○_ ＠ unfold₁ f x' by cn, ∘ cnjust ∘ δ


-- zipWith : ((z : A × B) → η z ⊩ C) → (zs : List (A × B)) → η zs ⊩ List C
module _ {A B C : Type ℓ} where
  zipWith : (A × B ⊸ C) → List (A × B) ⊸ List C
  zipWith f = unfold₁ go where
    go : List (A × B) ⊸ Maybe (C × List (A × B))
    go [] = nothing○ by cn[]
    go (z ∷ zs) = just○ ＠ (f z ,◎ ． zs) by cn∷

-- let (fz , δ) = f z in just○ ＠ (fz ,○ zs) by id (η zs) ⊗ᶠ δ ∘ swap (η z) (η zs) ∘ cn∷


module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  {-# TERMINATING #-}
  rounds : (B → Maybe ((Δ ⊩ A) × B)) → B → ℕ
  rounds f x with f x
  ... | nothing = zero
  ... | just (_ , x') = suc (rounds f x')

module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  {-# NON_TERMINATING #-}
  unfold₂ : (f : B → Maybe ((Δ ⊩ A) × B)) → (x : B) → Δ ^ rounds f x ⊩ List A
  unfold₂ f x with f x
  ... | nothing = []○
  ... | just ((y , δ) , x') = ． y ∷◎ unfold₂ f x' by δ ⊗ᶠ id (Δ ^ rounds f x')


module _ {A : Type} where
  replicate : (m : ℕ) → A -⟨ m ⟩⊸ List A
  replicate m x = unfold₂ go m by prod where
    go : ℕ → Maybe ((η x ⊩ A) × ℕ)
    go zero = nothing
    go (suc m) = just (． x , m)
    prod : η x ^ m ⧟ η x ^ rounds go m
    prod = subst (λ n → η x ^ m ⧟ η x ^ n) (mrounds≡m m) (id (η x ^ m))
      where
      mrounds≡m : (n : ℕ) → n ≡ rounds go n
      mrounds≡m zero = refl
      mrounds≡m (suc m) = cong suc (mrounds≡m m)


-- module _ {A B : Type ℓ} {Δ : Supply ℓ} where
-- unfold₃ : (f : B → Maybe ((Δ ⊩ A) × B)) (m : ℕ) → (x : B) → Δ ^ m ⊩ List A
-- unfold₃ f m x with f x
-- ... | nothing = {!!}
-- ... | just ((y , δ) , x') = y ∷○_ ＠ unfold₃ f (predℕ m) x' by {!!} -- δ ⊗ᶠ (id _)


-- TODO ALSO DO THIS?
-- {-# NON_TERMINATING #-}
-- ∞ : ℕ
-- ∞ = suc ∞


postulate
  ∞ : ℕ
  suc∞ : ∞ ≡ suc ∞

wk∞ : (Δ : Supply ℓ) → Δ ^ ∞ ⧟ Δ ^ (suc ∞)
wk∞  Δ = subst (λ a → Δ ^ a ⧟ Δ ^ suc ∞) (sym suc∞) (id (Δ ^ (suc ∞)))

module _ {A : Type ℓ} where
  {-# NON_TERMINATING #-}
  repeat : A -⟨ ∞ ⟩⊸ List A
  repeat x = ． x ∷◎ repeat x by wk∞ (η x)
-- repeat x = x ∷○_ ＠ repeat x by wk∞ (η x)


  {-# NON_TERMINATING #-}
  iterate : (A ⊸ A) → A -⟨ ∞ ⟩⊸ List A
  iterate f x = ． x ∷◎ iterate f ＠⟨ ∞ ⟩ (f x) by wk∞ (η x)


-- where --  prod where
-- -- iterate f x = x ∷○_ ＠ iterate f (f x .fst) by prod where
--   prod : η x ^ ∞ ⧟ η x ⊗ η (f x .fst) ^ ∞
--   prod = id (η x) ⊗ᶠ ⧟^ ∞ (f x .snd) ∘ wk∞ (η x)




