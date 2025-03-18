{-# OPTIONS --cubical --safe -WnoUnsupportedIndexedMatch #-}
module Examples.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Relation.Binary


module Ord {ℓ : Level} {A : Type ℓ} (_<_ : Rel A A ℓ) where
  data compare (x y : A) : Type ℓ where
    lt : x < y → compare x y
    eq : x ≡ y → compare x y
    gt : y < x → compare x y

  module Total (_≟_ : (x y : A) → compare x y) where

    _≤_ : Rel A A _
    x ≤ y = (x < y) ⊎ (x ≡ y)


    _≤?_ : (x y : A) → (x ≤ y) ⊎ (y < x)
    x ≤? y with x ≟ y
    ... | lt p = inl (inl p)
    ... | eq p = inl (inr (p))
    ... | gt p = inr p

    data Sorted : List A → Type ℓ where
      []  : Sorted []
      [-] : ∀ {x} → Sorted (x ∷ [])
      _∷_ : ∀ {x y xs} → x ≤ y → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)


    Sorted-tail : {x : A} {xs : List A} → Sorted (x ∷ xs) → Sorted xs
    Sorted-tail {_} {[]} [-] = []
    Sorted-tail {_} {_ ∷ _} (_ ∷ p) = p

    SList : Type ℓ
    SList = Σ (List A) Sorted




module NatOrder where
  open import Cubical.Data.Nat
  open import Cubical.Data.Nat.Order hiding (_≟_) public

  open Ord _<_
  Order-suc : {m n : ℕ} → compare m n → compare (suc m) (suc n)
  Order-suc (lt m<n) = lt (suc-≤-suc m<n)
  Order-suc (eq m=n) = eq (cong suc m=n)
  Order-suc (gt n<m) = gt (suc-≤-suc n<m)

  _≟_ : (x y : ℕ) → compare x y
  _≟_ zero zero = Ord.eq refl
  _≟_ zero (suc y) = Ord.lt (y , +-comm y 1)
  _≟_ (suc x) zero = Ord.gt ((x , +-comm x 1))
  _≟_ (suc x) (suc y) = Order-suc (x ≟ y)

-- module ListOrder  {ℓ : Level} {A : Type ℓ} (_<_ : Rel A A ℓ) (_≟_ : (x y : A) → Ord.compare _<_ x y) where

--   _<L_ : Rel (List A) (List A) ℓ
--   [] <L [] = ⊥*
--   [] <L (x ∷ ys) = Unit*
--   (x ∷ xs) <L [] = ⊥*
--   (x ∷ xs) <L (y ∷ ys) with x ≟ y
--   ... | Ord.lt x₁ = Unit*
--   ... | Ord.eq x₁ = xs <L ys
--   ... | Ord.gt x₁ = ⊥*

-- -- -- module ListOrder  {ℓ : Level} {A : Type ℓ} (_<_ : Rel A A ℓ) (_≟_ : (x y : A) → compare _<_ x y) where
--   open Ord _<L_

--   _≟L_ : (xs ys : List A) → compare xs ys
--   [] ≟L [] = eq refl
--   [] ≟L (x ∷ ys) = lt tt*
--   (x ∷ xs) ≟L [] = gt tt*
--   (x ∷ xs) ≟L (y ∷ ys) with x ≟ y
--   ... | lt x₁ = {!lt!}
--   ... | eq x₁ = {!xs <L ys!}
--   ... | gt x₁ = {!!}



-- \end{code}
