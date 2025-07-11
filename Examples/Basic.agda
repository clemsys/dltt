{-# OPTIONS --safe #-}

module Examples.Basic where

open import Prelude
open import Lemmas
open import Base
open import Poly

private
  variable
    ℓ : Level



module _ {A : Type ℓ} where
  idJ : (x : A) → ι x ⊩ A ．
  idJ x = x ⁱ


testev = fst (idJ 4)

module _ {A B : Type ℓ} where
  switchJ : (z : A × B) → ι z ⊩  B × A ．
  switchJ (x , y) = ((y , x) ⁱ)
      by lax, ∘ id (ι y) ⊗ᶠ id (ι x) ∘
          (id (ι y) ⊗ᶠ unitr (ι x) ∘
           (assoc' (ι y) (ι x) ◇ ∘ swap (ι x) (ι y) ⊗ᶠ id ◇ ∘
            assoc (ι x) (ι y) ◇
            ∘ id (ι x ⊗ ι y ⊗ ◇)))
          ∘
          (id (ι x ⊗ ι y ⊗ ◇) ∘ id (ι x) ⊗ᶠ unitr' (ι y) ∘
           (id (ι x) ⊗ᶠ id (ι y) ∘ opl,)) 

module _ {A B : Type ℓ} where
  foldMaybe-ish : (z : Maybe A) → ((x : A) → ι x ⊩ B ．) → (n : B)
    → ι z ⊗ (if isJust z then ◇ else ι n) ⊩ B ．
  foldMaybe-ish (just x) j n = j x
    by unitr (ι x) ∘ (id (ι x) ⊗ᶠ id ◇ ∘ (id (ι x) ∘ oplinl) ⊗ᶠ id ◇)
  foldMaybe-ish nothing j n = n ⁱ
    by unitr (ι n) ∘ (unitr' (ι n) ∘ unitl (ι n) ∘ (opltt ∘ oplinr) ⊗ᶠ id (ι n))


module _ {A B C : Type ℓ} where
  elim＋ : ((x : A) → ι x ⊩ C ．) → ((y : B) → ι y ⊩ C ．) → (z : A ＋ B) → ι z ⊩ C ．
  elim＋ f g (inl x) = f x by unitr (ι x) ∘ (unitr' (ι x) ∘ (id (ι x) ∘ oplinl))
  elim＋ f g (inr y) = g y by unitr (ι y) ∘ (unitr' (ι y) ∘ (id (ι y) ∘ oplinr))



