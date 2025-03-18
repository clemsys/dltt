{-# OPTIONS --cubical --safe #-}
module Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_] ; map)
open import Cubical.Data.Vec
open import Cubical.Data.Unit
open import Cubical.Data.Maybe

open import Cubical.Data.Nat public hiding (_^_)
open import Cubical.HITs.FiniteMultiset public hiding ([_]) renaming ([] to ◇ ; _∷_ to _⨾_ ; _++_ to _⊗_)




Supply : (ℓ : Level) → Type (ℓ-suc ℓ)
Supply ℓ = FMSet (Σ[ A ∈ Type ℓ ] A)


module _ {ℓ : Level}  {A : Type ℓ} where
  η : A → Supply ℓ
  η a = (A , a) ⨾ ◇



