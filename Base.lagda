\begin{code}[hide]
{-# OPTIONS --safe #-}
module Base where

open import Prelude

data Supply (ℓ : Level) : Type (ℓ-suc ℓ) where
  ◇ : Supply ℓ
  ι : {A : Type ℓ} (a : A) → Supply ℓ
  _⊗_ : Supply ℓ → Supply ℓ → Supply ℓ
  [_,_] : Supply ℓ → Supply ℓ → Supply ℓ
  Λ : (A : Type ℓ) → (Δ : A → Supply ℓ) → Supply ℓ
  ! : Supply ℓ → Supply ℓ


infixr 20 _⊗_
infixr 30 [_,_]


LType : (ℓ : Level) → Type (ℓ-suc ℓ)
LType ℓ = Σ[ A ∈ Type ℓ ] (A → Supply ℓ)


module _ {ℓ : Level} where
  infixl 0 _▷_
  infixr 11 _⊗ᶠ_
  infixl 10 _∘_

  data _▷_ : Supply ℓ → Supply ℓ → Type (ℓ-suc ℓ) where
    id : ∀ Δ → Δ ▷ Δ
    _∘_ : ∀ {Δ₀ Δ₁ Δ₂} → Δ₁ ▷ Δ₂ → Δ₀ ▷ Δ₁ → Δ₀ ▷ Δ₂
    _⊗ᶠ_ : ∀ {Δ₀ Δ₁ Δ₂ Δ₃} → Δ₀ ▷ Δ₁ → Δ₂ ▷ Δ₃ → Δ₀ ⊗ Δ₂ ▷ Δ₁ ⊗ Δ₃

    unitr : ∀ Δ → Δ ⊗ ◇ ▷ Δ
    unitr' : ∀ Δ → Δ ▷ Δ ⊗ ◇
    swap : ∀ Δ₀ Δ₁ → Δ₀ ⊗ Δ₁ ▷ Δ₁ ⊗ Δ₀
    assoc : ∀ Δ₀ Δ₁ Δ₂ → Δ₀ ⊗ (Δ₁ ⊗ Δ₂) ▷ (Δ₀ ⊗ Δ₁) ⊗ Δ₂

    curry : ∀ {Δ₀ Δ₁ Δ₂} →  (Δ₀ ⊗ Δ₁) ▷ Δ₂ → Δ₀ ▷ [ Δ₁ , Δ₂ ]
    uncurry : ∀ {Δ₀ Δ₁ Δ₂} → Δ₀ ▷ [ Δ₁ , Δ₂ ] →  (Δ₀ ⊗ Δ₁) ▷  Δ₂

    !ᶠ : ∀ {Δ₀ Δ₁} → Δ₀ ▷ Δ₁ → ! Δ₀ ▷ ! Δ₁
    use : ∀ {Δ} → ! Δ ▷ Δ
    mult : ∀ {Δ} → ! Δ ▷ ! (! Δ)
    coh◇ : ◇ ▷ ! ◇
    coh⊗ : ∀ {Δ₀ Δ₁} → ! Δ₀ ⊗ ! Δ₁ ▷ ! (Δ₀ ⊗ Δ₁)

    dupl : ∀ {Δ} → ! Δ ▷ ! (Δ ⊗ Δ)
    erase : ∀ {Δ} → ! Δ ▷ ◇

    bind : {Δ : Supply ℓ} {(A , Θ) : LType ℓ}
      → ((x : A) → Δ ▷ Θ x) → (Δ ▷ Λ A Θ)
    free : {Δ : Supply ℓ}  {(A , Θ) : LType ℓ}
      → (Δ ▷ Λ A Θ) → ((x : A) → Δ ▷ Θ x)

    opl, :  {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
      → ι {A = Σ A B} (a , b) ▷ (ι a ⊗ ι b)
    lax, :  {A : Type ℓ} {B : A → Type ℓ} {a : A} {b : B a}
      → (ι a ⊗ ι b) ▷ ι {A = Σ A B} (a , b)

    opltt : (ι tt) ▷ ◇
    laxtt : ◇ ▷ (ι tt)

    oplinl : {A B : Type ℓ} {a : A} → ι {A = A ＋ B} (inl a) ▷ ι a
    laxinl : {A B : Type ℓ} {a : A} → ι a ▷ ι {A = A ＋ B} (inl a)
    oplinr : {A B : Type ℓ} {b : B} → ι {A = A ＋ B} (inr b) ▷ ι b
    laxinr : {A B : Type ℓ} {b : B} → ι b ▷ ι {A = A ＋ B} (inr b)

    oplinit : {F : Functor ℓ} {x : ⟦ F ⟧ (μ F)} → ι (init {F = F} x) ▷ ι x
    laxinit : {F : Functor ℓ} {x : ⟦ F ⟧ (μ F)} → ι x ▷ ι (init {F = F} x)

private
  variable
    ℓ : Level


infixl 25 Λ
syntax Λ A (λ x → Δ) = Λ[ x ∶ A ] Δ

\end{code}
\newcommand{\agdaLinJudgment}{%
\begin{code}
_⊩_ : Supply ℓ → LType ℓ → Type (ℓ-suc ℓ)
\end{code}}
\begin{code}[hide]
Δ ⊩ (A , Θ) = Σ[ a ∈ A ] (Δ ▷ Θ a)

infixl -100 _⊩_


_ⁱ : {A : Type ℓ} → (a : A) → ι a ⊩ A , ι
_ⁱ a = a , id (ι a)
infix 101 _ⁱ



-- We use the following singleton type to carry around more complex supplies
-- with functions
record of (A : LType ℓ) : Type (ℓ-suc ℓ) where
  constructor -
  field
    term : A .fst

open of public

fof : {A : LType ℓ} → of A → {A .fst} → Supply ℓ
fof {_} {A , Θ} _ {x} = Θ x

_ᵀ : {A : LType ℓ} → ( x : of A) → A .snd (x .term) ⊩ A
_ᵀ {A} x = (x .term) , (id (fof x))

infix 101 _ᵀ

_ᵀγ : {A : LType ℓ} → ( x : of A) → ! (A .snd (x .term)) ⊩ A
_ᵀγ {A} x = (x .term) , (use {Δ = fof x})

infix 101 _ᵀγ


DLType : {ℓ : Level} → LType ℓ → Type (ℓ-suc ℓ)
DLType {ℓ} (A , _) = Σ[ B ∈ (A → Type ℓ) ] ({x : A} → B x → Supply ℓ)

syntax DLType A = A ⇒ LType

_． : Type ℓ → LType ℓ
A ． = (A , ι)

infix -4 _．

module _ {Δ₀ Δ₁ : Supply ℓ} {A : LType ℓ} where
  _by_ : Δ₀ ⊩ A → (Δ₁ ▷ Δ₀) → Δ₁ ⊩ A
  (a , δ₀) by  δ₁ = a , δ₀ ∘ δ₁
  infixl 0 _by_

\end{code}
