{-# OPTIONS --cubical --safe #-}
module Examples.List where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map ; foldr)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Maybe

open import Core
open import Functions
open LinearTypes



private
  variable
    ℓ : Level


module _ {A : Type ℓ} where

  null : List A → Bool
  null [] = true
  null (x ∷ xs) = false


-- TODO notation for 0-ary function
module _ {A : Type ℓ} where
  []○ : ◇ ⊩ List A
  []○ = ． [] by wk[]

-- _∷○_ : (x : A) → (xs : List A) → η xs ⊗ η x ⊩ List A
  _∷○_ : A ⊸﹠ List A ⊸ List A
  x ∷○ xs = ． (x ∷ xs) by wk∷ ∘ swap (η xs) (η x)

module _ {A : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _∷◎_ : Δ₀ ⊩ A → Δ₁ ⊩ List A → Δ₀ ⊗ Δ₁ ⊩ List A
  _∷◎_ = ○→◎ _∷○_



  infixr 5 _∷◎_




module Ignore {A : Type ℓ} where
  safeHead : (xs : List A) → (y : A) → (if null xs then η y else ◇) ⊗ η xs ⊩ A × List A
  safeHead [] y = ． (y , []) by wk,
  safeHead (x ∷ xs) y = ． (x , xs) by wk, ∘ cn∷


module _ {A : Type ℓ} where
  safeHead : (xs : List A) → (y : A) → (if null xs then η y else ◇) ⊗ η xs ⊩ A × List A
  safeHead [] y = ． (y , []) by wk,
  safeHead (x ∷ xs) y = ． (x , xs) by wk, ∘ cn∷



-- foldr₁ : ((x : A) → (b : B) → η b ⊗ η x ⊩ B) → (z : Δ ⊩ B) → (xs : List A) → Δ ⊗ η xs ⊩ B
module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  foldr₁ : (A ⊸﹠ B ⊸ B) → (Δ ⊩ B) → (xs : List A) → Δ ⊗ η xs ⊩ B
  foldr₁ f z [] = z by unitr Δ ∘ (id Δ) ⊗ᶠ cn[]
  foldr₁ f z (x ∷ xs) = f x ＠ foldr₁ f z xs by prod where prod : Δ ⊗ η (x ∷ xs) ⧟ η x ⊗ Δ ⊗ η xs
                                                          prod = assoc (η x) Δ (η xs)
                                                            ∘ swap Δ (η x) ⊗ᶠ (id (η xs))
                                                            ∘ assoc' Δ (η x) (η xs) ∘ (id Δ) ⊗ᶠ cn∷


module _ {A : Type ℓ} where
  append : List A ⊸﹠ List A ⊸ List A
  append xs ys = foldr₁ _∷○_ (． ys) xs


module _ {A : Type ℓ} where
  concat : List (List A) ⊸ List A
  concat = foldr₁ append []○



module _ {A B : Type ℓ} {Δ : Supply ℓ} where
  foldr₂ : ((x : A) → (b : B) → η b ⊗ η x ⊗ Δ ⊩ B) → ◇ ⊩ B → (xs : List A)
    → Δ ^ (length xs) ⊗ η xs ⊩ B
  foldr₂ f z [] = z by cn[]
  foldr₂ f z (x ∷ xs) = f x ＠ foldr₂ f z xs
    by prod where
    prod : (Δ ⊗ Δ ^ length xs) ⊗ η (x ∷ xs) ⧟ η x ⊗ Δ ⊗ Δ ^ length xs ⊗ η xs

    prod = id (η x) ⊗ᶠ assoc Δ (Δ ^ length xs) (η xs)
      ∘ swap (Δ ⊗ Δ ^ (length xs)) (η x) ⊗ᶠ id (η xs)
      ∘ assoc' (Δ ^ suc (length xs)) (η x) (η xs)
      ∘ id (Δ ^ (suc (length xs ))) ⊗ᶠ cn∷


module _ {A : Type ℓ} where
  intersperse : (x : A) (ys : List A) → η x ^ (length ys) ⊗ η ys ⊩ List A
  intersperse x = foldr₂ (λ y xys → ． x ∷◎ ． y ∷◎ ． xys by prod y xys) []○ where
    prod : (y : A) (xys : List A) → η xys ⊗ η y ⊗ η x ⧟ η x ⊗ η y ⊗ η xys
    prod y xys = assoc (η x) (η y) (η xys) ∘ swap (η xys) (η x ⊗ η y) ∘ (id (η xys) ⊗ᶠ swap (η y) (η x))

-- intersperse x = foldr₂ (λ y xys → x ∷○_ ＠ (y ∷○_ ＠ ． xys) by prod y xys) []○ where

  lt2 : List A → Bool
  lt2 [] = true
  lt2 (_ ∷ []) = true
  lt2 (_ ∷ _ ∷ _) = false

  lt2Lemma : (x : A) (xs : List A) → length xs ≡ (if lt2 (x ∷ xs) then zero else predℕ (length (x ∷ xs))) 
  lt2Lemma _ [] = refl
  lt2Lemma _ (_ ∷ _) = refl


  intersperse' : (x : A) (ys : List A) → η x ^ (if lt2 ys then zero else predℕ (length ys)) ⊗ η ys ⊩ List A
  intersperse' x [] = ． []
  intersperse' x (y ∷ []) = ． (y ∷ [])
  intersperse' x (y ∷ y' ∷ ys) = ． x ∷◎ ． y ∷◎ intersperse' x (y' ∷ ys)
    by id (η x) ⊗ᶠ prod
    where
    prod : η x ^ (length (ys)) ⊗ η (y ∷ y' ∷ ys) ⧟
        η y ⊗ η x ^ (if lt2 (y' ∷ ys) then zero else predℕ (length (y' ∷ ys))) ⊗ η (y' ∷ ys)
    prod = subst (λ a → η x ^ (length (ys)) ⊗ η (y ∷ y' ∷ ys) ⧟ η y ⊗ η x ^ a ⊗ η (y' ∷ ys))
           (lt2Lemma y' ys )
           (swap (η x ^ length ys) (η y) ⊗ᶠ id (η (y' ∷ ys)) ∘ assoc' (η x ^ length ys) (η y) (η (y' ∷ ys)) ∘ id (η x ^ length ys) ⊗ᶠ cn∷ )

    -- prod : η x ^ length ys ⊗ η (y ∷ ys) ⧟ η x ⊗ η y ⊗ η x ^ (if null ys then zero else predℕ (length ys)) ⊗ η ys
    -- prod = {!!}
    



-- module _ {A B : Type ℓ} {Δ : Supply ℓ} where
--   foldr₁' : (A ⊸﹠ B ⊸ B) → (z : Δ ⊩ B) → (xs : List A) → Δ ⊗ η xs ⊩ B
--   foldr₁' f z [] = z by ? where prod : Δ ⊗ η [] ⧟ Δ
--   prod = unitr Δ ∘ (id Δ) ⊗ᶠ cn[]
--   foldr₁' f z (x ∷ xs) = f x ＠ foldr₁ f z xs by ?

-- prod where prod : Δ ⊗ η (x ∷ xs) ⧟ η x ⊗ Δ ⊗ η xs
-- prod = assoc (η x) Δ (η xs)
-- ∘ swap Δ (η x) ⊗ᶠ (id (η xs))
-- ∘ assoc' Δ (η x) (η xs) ∘ (id Δ) ⊗ᶠ cn∷




module _ {A B : Type ℓ} (m : ℕ) where
  map :  A -⟨ m ⟩⊸ B → List A -⟨ m ⟩⊸ List B
  map f [] = []○ by ◇^ m ∘ ⧟^ m cn[]
  map f (x ∷ xs) = f x ∷◎ map f xs by ⊗^ m ∘ ⧟^ m cn∷
-- map f (x ∷ xs) = let (fx , δ) = f x in fx ∷○_ ＠ map f xs by δ ⊗ᶠ id (η xs ^ m) ∘ ⊗^ m ∘ ⧟^ m cn∷

  -- map :  (A - m ⊸ B) → List A - m ⊸ List B
  -- map f [] = []○ by p₁
  --   where
  --   p₁ = ◇^ m ∘ ⧟^ m cn[]
  -- map f (x ∷ xs) = f x .fst ∷○_ ＠ map f xs by p₂
  --   where
  --   p₂ = f x .snd ⊗ᶠ id (η xs ^ m) ∘ ⊗^ m ∘ ⧟^ m cn∷





-- module _ {A : Type} where
--   replicate : (m : ℕ) → (x : A) → η x ^ m ⊩ List A
--   replicate zero x = ． [] by wk[]
--   replicate (suc m) x = x ∷○_ ＠ replicate m x


