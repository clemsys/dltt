{-# OPTIONS --cubical --safe #-}
module Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma



open import Core
open LinearTypes


private
  variable
    ℓ : Level



module _ {A : Type ℓ} {B : Type ℓ} where
  switch : (z : A × B) → η z ⊩ B × A
  switch (x , y) = ． (y , x) by prod where prod : η (x , y) ⧟ η (y , x)
                                           prod = wk, ∘ swap (η x) (η y) ∘ cn,



_⊸_ : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ⊸ B = (x : A) → η x ⊩ B



_-⟨_⟩⊸_ : Type ℓ → ℕ → Type ℓ → Type (ℓ-suc ℓ)
A -⟨ m ⟩⊸ B = (x : A) → η x ^ m ⊩ B



_⊸﹠_⊸_ :  Type ℓ → Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
A ⊸﹠ B ⊸ C = (x : A) → (y : B) → η y ⊗ η x ⊩ C

-- _⊸_⊸﹠_ :  Type ℓ → Type ℓ →  Type ℓ → Type (ℓ-suc (ℓ-suc ℓ))
-- A ⊸ B ⊸﹠ C = Lift A ⊸ B ⊸ C


_⊸D_ : (A : Type ℓ) (B : A → Type ℓ) → Type (ℓ-suc ℓ)
A ⊸D B = (x : A) → η x ⊩ B x

infixr 0 _-⟨_⟩⊸_
infixr 0 _⊸_
infixr 0 _⊸﹠_⊸_
-- infixr 0 _⊸_⊸﹠_


module Ingore {A : Type ℓ} {B : Type ℓ} where
  _,○_ : A ⊸﹠ B ⊸ A × B
  x ,○ y = ． (x , y) by wk, ∘ swap (η y) (η x)


module _ {A : Type ℓ} {B : A → Type ℓ} where
-- _,○_ : (x : A) (y : B x) → η y ⊗ η x ⊩ Σ A B
  _,○_ : (x : A) → (y : B x) → η y ⊗ η x ⊩ Σ A B
  x ,○ y = ． (x , y) by wk, ∘ swap (η y) (η x)




module Ignore2 {A : Type ℓ} {B : A → Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _＠_ : ((x : A) → η x ⊗ Δ₀ ⊩ B x) → ((a , _) : Δ₁ ⊩ A) → Δ₀ ⊗ Δ₁ ⊩ B a
  f ＠ (a , δ) = f a by swap Δ₀ (η a) ∘ id Δ₀ ⊗ᶠ δ


-- this version does not work for foldr₁
-- module _ {A B : Type ℓ} {Δ : Supply ℓ} where
-- _＠_ : (A ⊸ B) → Δ ⊩ A → Δ ⊩ B
-- f ＠ (a , δ) = f a by δ

module _ {A B : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _＠_ : ((x : A) → η x ⊗ Δ₀ ⊩ B) → Δ₁ ⊩ A → Δ₀ ⊗ Δ₁ ⊩ B
  f ＠ (a , δ) = f a by swap Δ₀ (η a) ∘ id Δ₀ ⊗ᶠ δ

  infixl -100 _＠_

module _ {A B : Type ℓ} {Δ : Supply ℓ} (m : ℕ) where
  app : A -⟨ m ⟩⊸ B → Δ ⊩ A → Δ ^ m ⊩ B
  app f (a , δ) = f a by ⧟^ m δ


-- module _ {A B : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
--   app : (m : ℕ) → ((x : A) → η x ^ m ⊗ Δ₀ ⊩ B) → ((a , _) : Δ₁ ⊩ A) → Δ₀ ⊗ Δ₁ ^ m ⊩ B
--   app m f (a , δ) = f a by swap Δ₀ (η a ^ m) ∘ id Δ₀ ⊗ᶠ ⧟^ m δ


  syntax app m f x = f ＠⟨ m ⟩ x


-- module _ {A B : Type ℓ} where
--   _,○_ : A ⊸﹠ B ⊸ A × B
--   x ,○ y = ． (x , y) by wk, ∘ swap (η y) (η x)

module _ {A B C : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  ○→◎ : A ⊸﹠ B ⊸ C → Δ₀ ⊩ A → Δ₁ ⊩ B → Δ₀ ⊗ Δ₁ ⊩ C
  ○→◎ f (a , δ) b = f a ＠ b by δ ⊗ᶠ id Δ₁




module _ {A B : Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
  _,◎_ : Δ₀ ⊩ A → Δ₁ ⊩ B → Δ₀ ⊗ Δ₁ ⊩ A × B
  _,◎_ = ○→◎ _,○_



-- module _ {A : Type ℓ} {B : A → Type ℓ} {Δ₀ Δ₁ : Supply ℓ} where
-- _,◎_ : ((x , _) : Δ₀ ⊩ A) → (Δ₁ ⊩ B x) → Δ₀ ⊗ Δ₁ ⊩ Σ A B
  -- (x , δ₀) ,◎ (y , δ₁) = {!x ,○ y by ?!}
  -- ． (x , y) by wk, ∘ δ₀ ⊗ᶠ δ₁




module _ {A : Type ℓ} {B : Type ℓ} where
  switch' : A × B ⊸ B × A
  switch' (x , y) = (． y ,◎ ． x) by swap (η x) (η y) ∘ cn,




module _ {A : Type ℓ} where
  copy : A -⟨ 2 ⟩⊸ A × A
  copy x = ． (x , x) by wk,


module _ {A B C : Type ℓ} (n m : ℕ) where
  compose : A -⟨ n ⟩⊸ B → B -⟨ m ⟩⊸ C → A -⟨ n · m ⟩⊸ C
  compose f g x = g ＠⟨ m ⟩ (f ＠⟨ n ⟩ ． x) by explaw (η x) n m

-- compose f g x = let (y , δ) = f x in g y by ⧟^ m δ ∘ explaw (η x) n m

  -- compose : {Δ₀ Δ₁ : Supply ℓ} (m n : ℕ ) →
  --     ((x : A) → η x ^ n ⊗ Δ₀ ⊩ B)
  --   → ((y : B) → η y ^ m ⊗ Δ₁ ⊩ C)
  --   → (x : A) → η x ^ (m · n) ⊗ Δ₁ ⊗ Δ₀ ^ n ⊩ C
  -- compose m n f g x = applin m g (applin n f (． x) by {!!}) by {!!}

module _ {A : Type ℓ} where
  copytwice : A -⟨ 4 ⟩⊸ (A × A) × (A × A)
  copytwice = compose 2 2 copy copy



