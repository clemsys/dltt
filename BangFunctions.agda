{-# OPTIONS --safe #-}
module BangFunctions where

open import Prelude
open import Base
open import Lemmas


module ignore {ℓ : Level} where
  !⟨_⟩⊸_ : (A : LType ℓ) → (A ⇒ LType) → LType ℓ
  !⟨ A , Θ₀ ⟩⊸ (B , Θ₁) = ((x : A) → B x) , λ f → Λ[ x ∶ A ] [ ! (Θ₀ x) , Θ₁ (f x) ]


module _ {ℓ : Level} where

  Π! : (A : LType ℓ) → (A ⇒ LType) → LType ℓ
  Π! (A , Θ₀) (B , Θ₁) = ((x : A) → B x) , λ f → Λ[ x ∶ A ] [ ! (Θ₀ x) , Θ₁ (f x) ]

  -- To be able to introduce nice syntax we need to make the dependency for
  -- whole codomain explicit
  Π!' : ((A , Θ₀) : LType ℓ) → (A → LType ℓ) → LType ℓ
  Π!' (A , Θ₀) BΘ₁ = Π! (A , Θ₀) ((λ x → BΘ₁ x .fst) , λ {x} → BΘ₁ x .snd)

  infixr -5 Π!'
  syntax Π!' A (λ x → B) = !⟨ x ∶ A ⟩ ⊸ B

private
  variable
    ℓ : Level


Π!nd : ((A , Θ₀) : LType ℓ) → LType ℓ → LType ℓ
Π!nd A B = !⟨ _ ∶ A ⟩ ⊸ B
infixr -5 Π!nd
syntax Π!nd A B = !⟨ A ⟩ ⊸ B



module _ {Δ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType} where
  Π!I : ((x : A) → Δ ⊗ ! (Θ₀ x) ⊩ B x , Θ₁) → Δ ⊩ !⟨ x ∶ A , Θ₀ ⟩ ⊸ B x , Θ₁

  Π!I fδ = (λ x → fst (fδ x)) , bind (λ x → curry (snd (fδ x)))

  infixr -5 Π!I
  syntax Π!I (λ x → J) = 𝛌 x !↦ J

module _ {Δ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType} where
  Π!Iβ : ((x : of (A , Θ₀)) → Δ ⊗ ! (Θ₀ (x .term)) ⊩ B (x .term) , Θ₁) → Δ ⊩ !⟨ x ∶ A , Θ₀ ⟩ ⊸ B x , Θ₁
  Π!Iβ fδ = (λ x → fδ (- x) .fst ) , bind (λ x → curry (fδ (- x) .snd))

  infixr -5 Π!Iβ
  syntax Π!Iβ (λ x → J) = 𝛌 x !↦𝕗 J


．Π!I : {Δ : Supply ℓ} {A : Set ℓ} {(B , Θ) : (A ．) ⇒ LType}
  → ((x : A) → (Δ ⊗ ! (ι x)) ⊩ B x , Θ)
  → Δ ⊩ !⟨ x ∶ A ． ⟩ ⊸ B x , Θ
．Π!I {ℓ} {Δ} {A} = Π!I {ℓ} {Δ} {A , ι}

infixr -5 ．Π!I
syntax ．Π!I (λ x → J) = 𝛌 x ．!↦ J

module _ {Δ₀ Δ₁ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType} where
  _!﹫_ : Δ₀ ⊩ !⟨ x ∶ A , Θ₀ ⟩ ⊸ B x , Θ₁ → ((a , _) : Δ₁ ⊩ A , Θ₀) → (Δ₀ ⊗ ! Δ₁ ⊩ B a , Θ₁)
  (f , δ₀) !﹫ (a , δ₁) = f a , uncurry (free δ₀ a) ∘ (id Δ₀ ⊗ᶠ !ᶠ δ₁)

  infixl 100 _!﹫_

_!﹫．_ : {Δ₀ Δ₁ : Supply ℓ} {(A , Θ₀) : LType ℓ} {B : A → Type ℓ}
  → Δ₀ ⊩ !⟨ x ∶ A , Θ₀ ⟩ ⊸ B x ．
  → ((a , _) : Δ₁ ⊩ A , Θ₀)
  → (Δ₀ ⊗ ! Δ₁ ⊩ B a ．)
_!﹫．_ {_} {Δ₀} (b , f) (a , δ) = b a , uncurry (free f a) ∘ id Δ₀ ⊗ᶠ !ᶠ δ

infixl 100 _!﹫．_

