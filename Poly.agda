{-# OPTIONS --safe #-}
module Poly where

open import Prelude
open import Base

import Data.Unit.Base as ⊤
open import Data.Nat

private
  variable
    ℓ : Level

mapFold : ∀ {X : Type ℓ} (F G : Functor ℓ) → (⟦ G ⟧ X → X) → ⟦ F ⟧ (μ G) → ⟦ F ⟧ X
mapFold Id G ϕ (init x) = ϕ (mapFold G G ϕ x)
mapFold (Const A) G ϕ c = c
mapFold (F1 ＋' F2) G ϕ = (λ where (inl x) → inl (mapFold F1 G ϕ x)
                                  (inr y) → inr (mapFold F2 G ϕ y))
mapFold (F1 ×' F2) G ϕ (x , y) = mapFold F1 G ϕ x , mapFold F2 G ϕ y

fold : {F : Functor ℓ}{A : Type ℓ} → (⟦ F ⟧ A → A) → μ F → A
fold {_} {F} ϕ (init x) = ϕ (mapFold F F ϕ x)


module _ {ℓ : Level} where

  ⊤' : Functor ℓ
  ⊤' = Const ⊤

module _ {ℓ : Level} where

  Bool : Type ℓ
  Bool = ⊤ {ℓ} ＋ ⊤ {ℓ}


  pattern tt* = lift ⊤.tt
  pattern true = inl tt*
  pattern false = inr tt*


  ¬ : Bool → Bool
  ¬ false = true
  ¬ true = false

  ∣_∣ : Bool → ℕ
  ∣ false ∣ = 0
  ∣ true ∣ = 1



  Maybe : Type ℓ → Type ℓ
  -- Maybe A = μ (Const A ＋' ⊤')
  Maybe A = A ＋ (⊤ {ℓ})
  pattern just x = inl x
  pattern nothing = inr tt*


  ListF : Type ℓ → Functor ℓ
  ListF A = ⊤' ＋' (Const A ×' Id)

  List : Type ℓ → Type ℓ
  List A = μ (ListF A)

  pattern nil = init (inl tt*)
  pattern cons x xs  = init (inr (x , xs))

  foldr : {A B : Type ℓ} → (A → B → B) → B → List A → B
  foldr {A}{B} f z = fold (λ where (inl tt) → z
                                   (inr (a , b)) → f a b)



isJust : {A : Type ℓ} → Maybe A → Bool {ℓ}
isJust (just x) = true
isJust nothing = false

isNothing : {A : Type ℓ} → Maybe A → Bool
isNothing x = ¬ (isJust x)


module _  {ℓ' : Level} {A : Type ℓ} where
  if_then_else_ : Bool {ℓ'} → A → A → A
  if true then a else b = a
  if false then a else b = b


-- pattern true l = (tt* l)


-- test3 : Bool {ℓ-zero}
-- test3 = init (inl tt)

