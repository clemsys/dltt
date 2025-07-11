{-# OPTIONS --safe #-}
module NatFunctions where

open import Prelude
open import Base
open import Lemmas
open import NatMul public



module _ {ℓ : Level} where
  Π^ : (A : LType ℓ) → ℕ → (A ⇒ LType) → LType ℓ
  Π^ (A , Θ₀) m (B , Θ₁) = ((x : A) → B x) , λ f → Λ[ x ∶ A ] [ Θ₀ x ^ m , Θ₁ (f x) ]


  Π^' : ((A , Θ₀) : LType ℓ) → ℕ → (A → LType ℓ) → LType ℓ
  Π^' (A , Θ₀) m BΘ₁ = Π^ (A , Θ₀) m ((λ x → BΘ₁ x .fst) , λ {x} → BΘ₁ x .snd)

  infixr -5 Π^'
  syntax Π^' A m (λ x → B) = ⟨ x ∶ A ⟩^ m ⊸ B


private
  variable
    ℓ : Level


-- Non-dependent version
⟨_⟩^_⊸_ : ((A , Θ₀) : LType ℓ) → ℕ → LType ℓ → LType ℓ
⟨ A ⟩^ m ⊸ B = ⟨ _ ∶ A ⟩^ m ⊸ B
infixr -5 ⟨_⟩^_⊸_

-- Version with multiplicity 1
Π : (A : LType ℓ) → (A ⇒ LType) → LType ℓ
Π A = Π^ A 1

Π' : ((A , Θ₀) : LType ℓ) → (A → LType ℓ) → LType ℓ
Π' (A , Θ₀) BΘ₁ = Π (A , Θ₀) ((λ x → BΘ₁ x .fst) , λ {x} → BΘ₁ x .snd)

infixr -5 Π'
syntax Π' A (λ x → B) = ⟨ x ∶ A ⟩ ⊸ B

Πnd : ((A , Θ₀) : LType ℓ) → LType ℓ → LType ℓ
Πnd A B = ⟨ _ ∶ A ⟩ ⊸ B
infixr -5 Πnd
syntax Πnd A B = ⟨ A ⟩ ⊸ B


module _ {Δ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType} {m : ℕ} where
  Π^I : ((x : A) → Δ ⊗ Θ₀ x ^ m ⊩ B x , Θ₁) → Δ ⊩ ⟨ x ∶ A , Θ₀ ⟩^ m ⊸ B x , Θ₁
  Π^I fδ = (λ x → fst (fδ x)) , bind (λ x → curry (snd (fδ x)))

  infixr -5 Π^I
  syntax Π^I (λ x → b) = 𝛌 x ↦ b


module _ {Δ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType} {m : ℕ} where
  Π^Iβ : ((x : of (A , Θ₀)) → Δ ⊗ Θ₀ (x . term) ^ m ⊩ B (x .term) , Θ₁) → Δ ⊩ ⟨ x ∶ A , Θ₀ ⟩^ m ⊸ B x , Θ₁
  Π^Iβ fδ = (λ x → fst (fδ (- x))) , bind (λ x → curry (snd (fδ (- x))))

  infixr -5 Π^Iβ
  syntax Π^Iβ (λ x → b) = 𝛌 x ↦𝕗 b



．ΠI． : {Δ : Supply ℓ} {A : Type ℓ} {B : A → Type ℓ} {m : ℕ}
  → ((x : A) → Δ ⊗ ι x ^ m ⊩ B x ．)
  → Δ ⊩ ⟨ x ∶ A ． ⟩^ m ⊸ B x ．
．ΠI． {ℓ} {Δ} {A} = Π^I {ℓ} {Δ} {A ．}

infixr -5 ．ΠI．
syntax ．ΠI． (λ x → b) = 𝛌 x ．↦． b

．ΠI : {Δ : Supply ℓ} {A : Type ℓ} {(B , Θ₁) : (A ．) ⇒ LType} {m : ℕ}
  → ((x : A) → Δ ⊗ ι x ^ m ⊩ B x , Θ₁)
  → Δ ⊩ ⟨ x ∶ A ． ⟩^ m ⊸ B x , Θ₁
．ΠI {ℓ} {Δ} {A} = Π^I {ℓ} {Δ} {A ．}

infixr -5 ．ΠI
syntax ．ΠI (λ x → b) = 𝛌 x ．↦ b



-- just used for typesetting
module ignore {Δ₀ Δ₁ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType} (m : ℕ) where
  _﹫_ : Δ₀ ⊩ ⟨ x ∶ A , Θ₀ ⟩^ m ⊸ B x , Θ₁ → ((a , _) : Δ₁ ⊩ A , Θ₀) → (Δ₀ ⊗ Δ₁ ^ m ⊩ B a , Θ₁)
  (f , δ₀) ﹫ (a , δ₁) = f a , uncurry (free δ₀ a) ∘ (id Δ₀ ⊗ᶠ (▷^ m δ₁))


module _ {Δ₀ Δ₁ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType} (m : ℕ) where
  Π^App : Δ₀ ⊩ ⟨ x ∶ A , Θ₀ ⟩^ m ⊸ B x , Θ₁ → ((a , _) : Δ₁ ⊩ A , Θ₀) → (Δ₀ ⊗ Δ₁ ^ m ⊩ B a , Θ₁)
  Π^App (f , δ₀) (a , δ₁) = f a , uncurry (free δ₀ a) ∘ (id Δ₀ ⊗ᶠ (▷^ m δ₁))

  infixl 100 Π^App

  syntax Π^App m f a = f ≺ m ﹫ a



Π^App． : {Δ₀ Δ₁ : Supply ℓ} {(A , Θ₀) : LType ℓ}
  {B : A → Type ℓ}
  (m : ℕ)
  → Δ₀ ⊩ ⟨ x ∶ A , Θ₀ ⟩^ m ⊸ B x ．
  → ((a , _) : Δ₁ ⊩ A , Θ₀)
  → (Δ₀ ⊗ Δ₁ ^ m ⊩ B a ．)
Π^App． = Π^App


infixl 100 Π^App．

syntax Π^App． m f a = f ≺ m ﹫． a


_﹫_ : {Δ₀ Δ₁ : Supply ℓ} {(A , Θ₀) : LType ℓ} {(B , Θ₁) : (A , Θ₀) ⇒ LType}
  → Δ₀ ⊩ ⟨ x ∶ A , Θ₀ ⟩ ⊸ B x , Θ₁
  → ((a , _) : Δ₁ ⊩ A , Θ₀)
  → (Δ₀ ⊗ Δ₁ ^ 1 ⊩ B a , Θ₁)
_﹫_ = Π^App 1

infixl 100 _﹫_


_﹫．_ : {Δ₀ Δ₁ : Supply ℓ} {(A , Θ₀) : LType ℓ} {B : A → Type ℓ}
  → Δ₀ ⊩ ⟨ x ∶ A , Θ₀ ⟩ ⊸ B x ．
  → ((a , _) : Δ₁ ⊩ A , Θ₀)
  → (Δ₀ ⊗ Δ₁ ^ 1 ⊩ B a ．)
_﹫．_ = Π^App 1

infixl 100 _﹫．_




