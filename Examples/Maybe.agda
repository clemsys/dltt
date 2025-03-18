{-# OPTIONS --cubical --safe #-}
module Examples.Maybe where

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
  nothing○ : ◇ ⊩ Maybe A
  nothing○ = ． nothing by wknothing

-- just○ : (x : A) → η x ⊩ Maybe A
  just○ : A ⊸ Maybe A
  just○ x = ． (just x) by wkjust

