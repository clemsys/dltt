{-# OPTIONS --safe #-}
module Prelude where

open import Agda.Primitive public
  using    ( Level
  ; SSet )
  renaming ( lzero to ℓ-zero
  ; lsuc  to ℓ-suc
  ; _⊔_   to ℓ-max
  ; Set   to Type
  ; Setω  to Typeω )
open import Data.Product public hiding (map ; swap ; curry ; uncurry) renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum public hiding (map ; map₁ ; map₂ ; assocʳ ; assocˡ ; [_,_] ; swap) renaming (_⊎_ to _＋_ ; inj₁ to inl; inj₂ to inr)
open import Level public

open import Data.Unit.Polymorphic public

case_of_type_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (B : A → Type ℓ') → ((x : A) → B x) → B x
case x of B type f = f x


-- Taken from 3.2 Universes https://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf

data Functor (ℓ : Level) : Type (ℓ-suc ℓ) where
  Id : Functor ℓ
  Const : Type ℓ → Functor ℓ
  _×'_ : Functor ℓ → Functor ℓ → Functor ℓ
  _＋'_ : Functor ℓ → Functor ℓ → Functor ℓ

module _ {ℓ : Level} where
  ⟦_⟧ : Functor ℓ → Type ℓ → Type ℓ
  ⟦ Id ⟧ X = X
  ⟦ Const A ⟧ X = A
  ⟦ A ×' B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦ A ＋' B ⟧ X = ⟦ A ⟧ X ＋ ⟦ B ⟧ X


  data μ (F : Functor ℓ) : Type ℓ where
    init : ⟦ F ⟧ (μ F) → μ F


