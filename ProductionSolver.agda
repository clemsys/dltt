{-# OPTIONS #-}

module ProductionSolver where

open import Data.Nat
open import Data.List
open import Data.Product hiding (map ; zip)
open import Data.Unit
open import Data.Bool
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Reflection renaming (Type to IType)
import Level

open import Prelude hiding (⊤)
open import Base
open import Lemmas public

debug : {A : Set} → Term → TC A
debug tm = typeError (termErr tm ∷ [])

mapM : {a b : Set} → (a -> TC b) -> List a -> TC (List b)
mapM f [] = returnTC []
mapM f (x ∷ xs) = do
  a <- f x
  as <- mapM f xs
  returnTC (a ∷ as)

hide : {A : Set} → List A → List A
hide _ = []


hidArg : Arg Term → Arg Term
hidArg (arg (arg-info _ rel) t) = arg (arg-info hidden rel) t

visArg : Arg Term → Arg Term
visArg (arg (arg-info _ rel) t) = arg (arg-info visible rel) t

pattern ◇＂ ℓ = con (quote ◇) (ℓ ∷ [])

pattern ⊗＂ ℓ X Y = con (quote _⊗_) (ℓ ∷ vArg X ∷ vArg Y ∷ [])

pattern ι＂ ℓ A a = con (quote ι) (ℓ ∷ hArg A ∷ vArg a ∷ [])

id＂ : Arg Term → Term → Term
id＂ ℓ X = con (quote id) (ℓ ∷ vArg X ∷ [])

⊗ᶠ＂ : Arg Term → Term → Term → Term → Term → Term → Term → Term
⊗ᶠ＂ ℓ W X Y Z P Q = con (quote _⊗ᶠ_) (ℓ ∷ hArg W ∷ hArg X ∷ hArg Y ∷ hArg Z ∷ vArg P ∷ vArg Q ∷ [])

∘＂ : Arg Term → Term → Term → Term → Term → Term → Term
∘＂ ℓ X Y Z P Q = con (quote _∘_) (ℓ ∷ hArg X ∷ hArg Y ∷ hArg Z ∷ vArg P ∷ vArg Q ∷ [])

record normTerm : Set where
  constructor nf
  field
    changed : Bool
    sply : Term
    lprod : Term
    rprod : Term

open normTerm


module _ (lev : Arg Term) where
  {-# TERMINATING #-}
  rmconstr : Term → normTerm

  rmconstr (◇＂ ℓ) =  nf false (◇＂ ℓ) (id＂ ℓ (◇＂ ℓ)) (id＂ ℓ (◇＂ ℓ))

  rmconstr (⊗＂ ℓ Δ₀ Δ₁) = let Δ₀' = rmconstr Δ₀ ; Δ₁' = rmconstr Δ₁ in
    nf (Δ₀' .changed ∨ Δ₁' .changed) (⊗＂ ℓ (Δ₀' .sply) (Δ₁' .sply))
      (⊗ᶠ＂ ℓ Δ₀ (Δ₀' .sply) Δ₁ (Δ₁' .sply) (Δ₀' .lprod) (Δ₁' .lprod))
      (⊗ᶠ＂ ℓ (Δ₀' .sply) Δ₀ (Δ₁' .sply) Δ₁ (Δ₀' .rprod) (Δ₁' .rprod))

  rmconstr (ι＂ ℓ ΣAB (con (quote _,_) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg x ∷ vArg y ∷ []))) = nf true
    ( ⊗＂ ℓ (rmconstr (ι＂ ℓ₀ A x) .sply) (rmconstr (ι＂ ℓ₁ B y) .sply))
    (∘＂ ℓ (ι＂ ℓ ΣAB (con (quote _,_) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg x ∷ vArg y ∷ [])))
          (⊗＂ ℓ (ι＂ ℓ₀ A x) (ι＂ ℓ₁ B y))
          (rmconstr (ι＂ ℓ ΣAB (con (quote _,_) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg x ∷ vArg y ∷ []))) .sply)
          (rmconstr (⊗＂ ℓ (ι＂ ℓ₀ A x) (ι＂ ℓ₁ B y)) .lprod)
          (con (quote opl,) (ℓ ∷ hArg A ∷ hArg B ∷ hArg x ∷ hArg y ∷ [])))
    (∘＂ ℓ  (rmconstr (ι＂ ℓ ΣAB (con (quote _,_) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg x ∷ vArg y ∷ []))) .sply)
          (⊗＂ ℓ (ι＂ ℓ₀ A x) (ι＂ ℓ₁ B y))
          (ι＂ ℓ ΣAB (con (quote _,_) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg x ∷ vArg y ∷ [])))
          (con (quote lax,) (ℓ ∷ hArg A ∷ hArg B ∷ hArg x ∷ hArg y ∷ []))
          (rmconstr (⊗＂ ℓ (ι＂ ℓ₀ A x) (ι＂ ℓ₁ B y)) .rprod))

  rmconstr (ι＂ ℓ Unit (con (quote Level.lift) _)) = nf true (◇＂ ℓ) (con (quote opltt) []) (con (quote laxtt) [])

  rmconstr (ι＂ ℓ A＋B (con (quote inl) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg a ∷ []))) =
    let A' = rmconstr (ι＂ ℓ₀ A a) in
    nf true (A' .sply)
    (∘＂ ℓ  (ι＂ ℓ A＋B (con (quote inl) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg a ∷ [])))
      (ι＂ ℓ₀ A a)
      (A' .sply)
      (A' .lprod)
      (con (quote oplinl) (ℓ ∷ hArg A ∷ hArg B ∷ hArg a ∷ [])))
    (∘＂ ℓ  (A' .sply)
          (ι＂ ℓ₀ A a)
          (ι＂ ℓ A＋B (con (quote inl) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg a ∷ [])))
          (con (quote laxinl) (ℓ ∷ hArg A ∷ hArg B ∷ hArg a  ∷ []))
          (A' .rprod))

  rmconstr (ι＂ ℓ A＋B (con (quote inr) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg b ∷ []))) =
    let B' = rmconstr (ι＂ ℓ₀ A b) in
    nf true (B' .sply)
    (∘＂ ℓ (ι＂ ℓ A＋B (con (quote inr) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg b ∷ [])))
          (ι＂ ℓ₀ A b)
          (B' . sply)
          (B' .lprod)
          (con (quote oplinr) (ℓ ∷ hArg A ∷ hArg B ∷ hArg b  ∷ [])))
    (∘＂ ℓ  (B' . sply)
          (ι＂ ℓ₀ A b)
          (ι＂ ℓ A＋B (con (quote inr) (ℓ₀ ∷ ℓ₁ ∷ hArg A ∷ hArg B ∷ vArg b ∷ [])))
          (con (quote laxinr) (ℓ ∷ hArg A ∷ hArg B ∷ hArg b  ∷ []))
          (B' .rprod))

  rmconstr (ι＂ ℓ (def (quote μ) (_ ∷ vArg F ∷ _)) (con (quote init) (_ ∷ _ ∷ vArg x ∷ _))) =
    let x' = rmconstr (ι＂ ℓ (def (quote ⟦_⟧) (ℓ ∷ vArg F ∷ vArg (def (quote μ) (ℓ ∷ vArg F ∷ [])) ∷ [])) x) in
    nf true (x' .sply)
    (∘＂ ℓ (ι＂ ℓ (def (quote μ) (ℓ ∷ vArg F ∷ [])) (con (quote init) (ℓ ∷ hArg F ∷ vArg x ∷ [])))
          (ι＂ ℓ (def (quote ⟦_⟧) (ℓ ∷ vArg F ∷ vArg (def (quote μ) (ℓ ∷ vArg F ∷ [])) ∷ [])) x)
          (x' .sply)
          (x' .lprod)
          (con (quote oplinit) (ℓ ∷ hArg F ∷ hArg x ∷ [])))

    (∘＂ ℓ  (x' .sply)
          (ι＂ ℓ (def (quote ⟦_⟧) (ℓ ∷ vArg F ∷ vArg (def (quote μ) (ℓ ∷ vArg F ∷ [])) ∷ [])) x)
          (ι＂ ℓ (def (quote μ) (ℓ ∷ vArg F ∷ [])) (con (quote init) (ℓ ∷ hArg F ∷ vArg x ∷ [])))
          (con (quote laxinit) (ℓ ∷ hArg F ∷ hArg x ∷ []))
          (x' .rprod))

  rmconstr Δ  = nf false Δ (id＂ lev Δ) (id＂ lev Δ)

module _ (lev : Arg Term) where

  {-# TERMINATING #-}
  reassocify : Term → normTerm
  reassocify (◇＂ ℓ) = nf false (◇＂ ℓ) (id＂ ℓ (◇＂ ℓ)) (id＂ ℓ (◇＂ ℓ))

  reassocify (⊗＂ ℓ (⊗＂ _ Δ₀ Δ₁) Δ₂) = let reassoc = reassocify (⊗＂ ℓ Δ₀ (⊗＂ ℓ Δ₁ Δ₂)) in
    nf true (reassoc .sply)
    (∘＂ ℓ  (⊗＂ ℓ (⊗＂ ℓ Δ₀ Δ₁) Δ₂) (⊗＂ ℓ Δ₀ (⊗＂ ℓ Δ₁ Δ₂)) (reassoc .sply) (reassoc .lprod) (def (quote assoc') (ℓ ∷ vArg Δ₀ ∷ vArg Δ₁ ∷ vArg Δ₂ ∷ [])))
    (∘＂ ℓ  (reassoc .sply) (⊗＂ ℓ Δ₀ (⊗＂ ℓ Δ₁ Δ₂)) (⊗＂ ℓ (⊗＂ ℓ Δ₀ Δ₁) Δ₂) (con (quote assoc) (ℓ ∷ vArg Δ₀ ∷ vArg Δ₁ ∷ vArg Δ₂ ∷ [])) (reassoc .rprod))

  reassocify (⊗＂ ℓ Δ₀ Δ₁) = let Δ₁' = reassocify Δ₁ in
    nf (Δ₁' .changed) (⊗＂ ℓ Δ₀ (Δ₁' .sply))
    (⊗ᶠ＂ ℓ Δ₀ Δ₀ Δ₁ (Δ₁' .sply) (id＂ ℓ Δ₀) (Δ₁' .lprod))
    (⊗ᶠ＂ ℓ Δ₀ Δ₀ (Δ₁' .sply) Δ₁ (id＂ ℓ Δ₀) (Δ₁' .rprod))

  reassocify Δ  = nf false Δ (id＂ lev Δ) (id＂ lev Δ)

module _ (lev : Arg Term) where

  unitify : Term → normTerm

  unitify (◇＂ ℓ) = nf false (◇＂ ℓ) (id＂ ℓ (◇＂ ℓ)) (id＂ ℓ (◇＂ ℓ))

  unitify (⊗＂ ℓ (◇＂ _) Δ) = let Δ' = unitify Δ in
    nf true (Δ' .sply)
    (∘＂ ℓ (⊗＂ ℓ (◇＂ ℓ) Δ) Δ (Δ' .sply) (Δ' .lprod) (def (quote unitl) (ℓ ∷ vArg Δ ∷ [])))
    (∘＂ ℓ (Δ' .sply) Δ (⊗＂ ℓ (◇＂ ℓ) Δ) (def (quote unitl') (ℓ ∷ vArg Δ ∷ [])) (Δ' .rprod))

  unitify (⊗＂ ℓ Δ₀ Δ₁) = let Δ₁' = unitify Δ₁ in
    nf (Δ₁' .changed) (⊗＂ ℓ Δ₀ (Δ₁' .sply))
      (⊗ᶠ＂ ℓ Δ₀ Δ₀ Δ₁ (Δ₁' .sply) (id＂ ℓ Δ₀) (Δ₁' .lprod))
      (⊗ᶠ＂ ℓ Δ₀ Δ₀ (Δ₁' .sply) Δ₁ (id＂ ℓ Δ₀) (Δ₁' .rprod))

  unitify Δ  = nf true (⊗＂ lev Δ (◇＂ lev))
    (con (quote unitr') (lev ∷ vArg Δ ∷ []))
    (con (quote unitr) (lev ∷ vArg Δ ∷ []))


module _ (lev : Arg Term) where

  {-# TERMINATING #-}
  sort : Term → normTerm

  sort (⊗＂ ℓ (ι＂ _ A (var x xargs)) (⊗＂ _ (ι＂ _ B (var y yargs)) Δ₂)) with x ≤ᵇ y 
  ... | true =
    let ιx : Term
        ιx = ι＂ ℓ A (var x xargs)
        ιy : Term
        ιy = ι＂ ℓ B (var y yargs)
        rest = sort (⊗＂ ℓ ιx Δ₂) in
    nf true (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂))

    (∘＂ ℓ  (⊗＂ ℓ ιx (⊗＂ ℓ ιy Δ₂)) ( ⊗＂ ℓ (⊗＂ ℓ ιx ιy) Δ₂) (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂))
      (∘＂ ℓ (⊗＂ ℓ (⊗＂ ℓ ιx ιy) Δ₂) (⊗＂ ℓ (⊗＂ ℓ ιy ιx) Δ₂) (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂))
        (def (quote assoc') (ℓ ∷ vArg ιy ∷ vArg ιx ∷ vArg Δ₂ ∷ []))
        (⊗ᶠ＂ ℓ (⊗＂ ℓ ιx ιy) (⊗＂ ℓ ιy ιx) Δ₂ Δ₂ (con (quote _▷_.swap) (ℓ ∷ vArg ιx ∷ vArg ιy ∷ [])) (id＂ ℓ Δ₂)))
      (con (quote assoc) (ℓ ∷ vArg ιx ∷ vArg ιy ∷ vArg Δ₂ ∷ [])))

    (∘＂ ℓ  (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂)) ( ⊗＂ ℓ (⊗＂ ℓ ιy ιx) Δ₂) (⊗＂ ℓ ιx (⊗＂ ℓ ιy Δ₂))
      (∘＂ ℓ (⊗＂ ℓ (⊗＂ ℓ ιy ιx) Δ₂) (⊗＂ ℓ (⊗＂ ℓ ιx ιy) Δ₂) (⊗＂ ℓ ιx (⊗＂ ℓ ιy Δ₂))
        (def (quote assoc') (ℓ ∷ vArg ιx ∷ vArg ιy ∷ vArg Δ₂ ∷ []))
        (⊗ᶠ＂ ℓ (⊗＂ ℓ ιy ιx) (⊗＂ ℓ ιx ιy) Δ₂ Δ₂ (con (quote _▷_.swap) (ℓ ∷ vArg ιy ∷ vArg ιx ∷ [])) (id＂ ℓ Δ₂)))
      (con (quote assoc) (ℓ ∷ vArg ιy ∷ vArg ιx ∷ vArg Δ₂ ∷ [])))

  ... | false =
    let ιx : Term
        ιx = ι＂ ℓ A (var x xargs)
        ιy : Term
        ιy = ι＂ ℓ B (var y yargs)
        rest = sort (⊗＂ ℓ ιy Δ₂) in
    nf (rest .changed) (⊗＂ ℓ ιx (rest .sply))
      (⊗ᶠ＂ ℓ ιx ιx (rest .sply) (⊗＂ ℓ ιy Δ₂) (id＂ ℓ ιx) (rest .lprod))

      (⊗ᶠ＂ ℓ ιx ιx (rest .sply) (⊗＂ ℓ ιy Δ₂) (id＂ ℓ ιx) (rest .rprod))

  sort Δ  = nf false Δ (id＂ lev Δ) (id＂ lev Δ)





module _ (lev : Arg Term) where

  {-# TERMINATING #-}
  lsort : Term → normTerm

  lsort (⊗＂ ℓ (ι＂ _ A (var x xargs)) (⊗＂ _ (ι＂ _ B (var y yargs)) Δ₂)) with x <ᵇ y
  ... | true =
    let ιx : Term
        ιx = ι＂ ℓ A (var x xargs)
        ιy : Term
        ιy = ι＂ ℓ B (var y yargs) in
    nf true (⊗＂ ℓ ιx (⊗＂ ℓ ιy Δ₂))
    (∘＂ ℓ  (⊗＂ ℓ ιx (⊗＂ ℓ ιy Δ₂)) ( ⊗＂ ℓ (⊗＂ ℓ ιx ιy) Δ₂) (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂))
      (∘＂ ℓ (⊗＂ ℓ (⊗＂ ℓ ιx ιy) Δ₂) (⊗＂ ℓ (⊗＂ ℓ ιy ιx) Δ₂) (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂))
        (def (quote assoc') (ℓ ∷ vArg ιy ∷ vArg ιx ∷ vArg Δ₂ ∷ []))
        (⊗ᶠ＂ ℓ (⊗＂ ℓ ιx ιy) (⊗＂ ℓ ιy ιx) Δ₂ Δ₂ (con (quote _▷_.swap) (ℓ ∷ vArg ιx ∷ vArg ιy ∷ [])) (id＂ ℓ Δ₂)))
      (con (quote assoc) (ℓ ∷ vArg ιx ∷ vArg ιy ∷ vArg Δ₂ ∷ [])))
    unknown

  ... | false =
    let ιx : Term
        ιx = ι＂ ℓ A (var x xargs)
        ιy : Term
        ιy = ι＂ ℓ B (var y yargs)
        rest = lsort (⊗＂ ℓ ιx Δ₂) in
    nf (rest .changed) (⊗＂ ℓ ιy (rest .sply))
      (⊗ᶠ＂ ℓ (rest .sply) (⊗＂ ℓ ιx Δ₂) ιy ιy (rest .lprod) (id＂ ℓ ιy))
      unknown

  lsort Δ  = nf false Δ (id＂ lev Δ) (id＂ lev Δ)




module _ (lev : Arg Term) where

  {-# TERMINATING #-}
  rsort : Term → normTerm

  rsort (⊗＂ ℓ (ι＂ _ A (var x xargs)) (⊗＂ _ (ι＂ _ B (var y yargs)) Δ₂)) with x <ᵇ y
  ... | true =
    let ιx : Term
        ιx = ι＂ ℓ A (var x xargs)
        ιy : Term
        ιy = ι＂ ℓ B (var y yargs) in
    nf true (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂)) unknown
    (∘＂ ℓ  (⊗＂ ℓ ιy (⊗＂ ℓ ιx Δ₂)) ( ⊗＂ ℓ (⊗＂ ℓ ιy ιx) Δ₂) (⊗＂ ℓ ιx (⊗＂ ℓ ιy Δ₂))
      (∘＂ ℓ (⊗＂ ℓ (⊗＂ ℓ ιy ιx) Δ₂) (⊗＂ ℓ (⊗＂ ℓ ιx ιy) Δ₂) (⊗＂ ℓ ιx (⊗＂ ℓ ιy Δ₂))
        (def (quote assoc') (ℓ ∷ vArg ιx ∷ vArg ιy ∷ vArg Δ₂ ∷ []))
        (⊗ᶠ＂ ℓ (⊗＂ ℓ ιy ιx) (⊗＂ ℓ ιx ιy) Δ₂ Δ₂ (con (quote _▷_.swap) (ℓ ∷ vArg ιy ∷ vArg ιx ∷ [])) (id＂ ℓ Δ₂)))
      (con (quote assoc) (ℓ ∷ vArg ιy ∷ vArg ιx ∷ vArg Δ₂ ∷ [])))

  ... | false =
    let ιx : Term
        ιx = ι＂ ℓ A (var x xargs)
        ιy : Term
        ιy = ι＂ ℓ B (var y yargs)
        rest = rsort (⊗＂ ℓ ιy Δ₂) in
    nf (rest .changed) (⊗＂ ℓ ιx (rest .sply)) unknown
      (⊗ᶠ＂ ℓ ιx ιx (rest .sply) (⊗＂ ℓ ιy Δ₂) (id＂ ℓ ιx) (rest .rprod))



  rsort (⊗＂ ℓ Δ₁ (⊗＂ _ (ι＂ _ B (var y yargs)) Δ₂)) =
    let ιy : Term
        ιy = ι＂ ℓ B (var y yargs) in
    nf true (⊗＂ ℓ ιy (⊗＂ ℓ Δ₁ Δ₂)) unknown
    (∘＂ ℓ  (⊗＂ ℓ ιy (⊗＂ ℓ Δ₁ Δ₂)) ( ⊗＂ ℓ (⊗＂ ℓ ιy Δ₁) Δ₂) (⊗＂ ℓ Δ₁ (⊗＂ ℓ ιy Δ₂))
      (∘＂ ℓ (⊗＂ ℓ (⊗＂ ℓ ιy Δ₁) Δ₂) (⊗＂ ℓ (⊗＂ ℓ Δ₁ ιy) Δ₂) (⊗＂ ℓ Δ₁ (⊗＂ ℓ ιy Δ₂))
        (def (quote assoc') (ℓ ∷ vArg Δ₁ ∷ vArg ιy ∷ vArg Δ₂ ∷ []))
        (⊗ᶠ＂ ℓ (⊗＂ ℓ ιy Δ₁) (⊗＂ ℓ Δ₁ ιy) Δ₂ Δ₂ (con (quote _▷_.swap) (ℓ ∷ vArg ιy ∷ vArg Δ₁ ∷ [])) (id＂ ℓ Δ₂)))
      (con (quote assoc) (ℓ ∷ vArg ιy ∷ vArg Δ₁ ∷ vArg Δ₂ ∷ [])))


  rsort (⊗＂ ℓ Δ₀ (⊗＂ _ Δ₁ Δ₂)) =
    let rest = rsort (⊗＂ ℓ Δ₁ Δ₂) in
    nf (rest .changed) (⊗＂ ℓ Δ₀ (rest .sply)) unknown ((⊗ᶠ＂ ℓ Δ₀ Δ₀  (rest .sply) (⊗＂ ℓ Δ₁ Δ₂) (id＂ ℓ Δ₀) (rest .rprod)))

  rsort Δ  = nf false Δ (id＂ lev Δ) (id＂ lev Δ)


module _ (ℓ : Arg Term) (dir : Bool) where
  {-# TERMINATING #-}

  apnorms : Term → List (Term → normTerm) → Term × Term

  apnorms Δ [] with (if dir then lsort ℓ else rsort ℓ) Δ
  ... | nf false _ _ _ =  Δ , id＂ ℓ Δ
  ... | nf true Δ' L R = let next = apnorms Δ' [] in
    (next .fst , (if dir
      then  ∘＂ ℓ Δ Δ' (next .fst) (next .snd) L
      else  ∘＂ ℓ (next .fst) Δ' Δ R (next .snd)))


  apnorms Δ (f ∷ fs) with f Δ
  ... | nf false _ _ _ = apnorms Δ fs
  ... | nf true Δ' L R = let next = apnorms Δ' fs in
    (next .fst , (if dir
      then  ∘＂ ℓ Δ Δ' (next .fst) (next .snd) L
      else  ∘＂ ℓ (next .fst) Δ' Δ R (next .snd)))


solver : Term → TC Term
solver (def (quote _▷_) (ℓ ∷ vArg lhs ∷ vArg rhs ∷ [])) = do
  let nlhs = apnorms ℓ true lhs (rmconstr ℓ ∷ reassocify ℓ ∷ unitify ℓ  ∷ [])
  let nrhs = apnorms ℓ false rhs (rmconstr ℓ ∷ reassocify ℓ ∷ unitify ℓ ∷ [])
  returnTC (∘＂ ℓ lhs (nlhs .fst) rhs (nrhs .snd) (nlhs .snd))


solver _ = returnTC unknown

macro
  solve : Term → TC ⊤
  solve hole = do
    goal <- inferType hole >>= normalise
    sol <- solver goal
    unify hole sol


