---
title: Unary Type Theory
isIndex: true
---

```agda
module index where

open import Level using (Level; _⊔_; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; subst; cong)
open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)
open import Data.String using (String; _≟_)
```

# Syntax

```agda
record Signature (ℓ₁ ℓ₂ : Level) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    Type : Set ℓ₁
    Function : Set ℓ₂
    domain : Function → Type
    codomain : Function → Type

module sigs {ℓ₁ ℓ₂} (Sg : Signature ℓ₁ ℓ₂) where
  open Signature Sg

  Id : Set
  Id = String

  infixl 7  _·_
  infix  9  `_

  data Term : Set ℓ₂ where
    `_                     :  Id → Term
    _·_                    :  Function → Term → Term

  FV : Term → Id
  FV (` x) = x
  FV (f · m) = FV m

  infix 9 _[_:=_]
  _[_:=_] : Term → Id → Term → Term
  (` x) [ y := V ] with x ≟ y
  ... | yes _         = V
  ... | no  _         = ` x
  (L · M) [ y := V ]  = L · M [ y := V ]

  subst-id : ∀ {x} m
        → m [ x := (` x) ] ≡ m
  subst-id {x} (` y) with y ≟ x
  ... | yes p         = cong (`_) (sym p)
  ... | no  _         = refl
  subst-id {x} (L · M) = cong (L ·_) (subst-id M)
```

# Proved Terms

```agda
  data Context : Set ℓ₁ where
    _⦂_ : Id → Type → Context

  data _⊢_˸_ : Context → Term → Type → Set (ℓ₁ ⊔ ℓ₂) where
    ⊢` : ∀ {x α}
        -------------------
      → (x ⦂ α) ⊢ (` x) ˸ α
    ⊢· : ∀ {x α m β f}
      → (x ⦂ α) ⊢ m ˸ β
      → domain f ≡ β
        ------------------------------
      → (x ⦂ α) ⊢ (f · m) ˸ codomain f

  unique-types : ∀ {x α m β γ}
    → (x ⦂ α) ⊢ m ˸ β
    → (x ⦂ α) ⊢ m ˸ γ
    -----------------
    → β ≡ γ
  unique-types ⊢` ⊢` = refl
  unique-types (⊢· _ _) (⊢· _ _) = refl

  ⊢`-uniq₁ : ∀ {x y α β}
    → (x ⦂ α) ⊢ (` y) ˸ β
    ---------------------
    → x ≡ y
  ⊢`-uniq₁ ⊢` = refl

  ⊢`-uniq₂ : ∀ {x y α β}
    → (x ⦂ α) ⊢ (` y) ˸ β
    ---------------------
    → α ≡ β
  ⊢`-uniq₂ ⊢` = refl

  ⊢·-f₁ : ∀ {x α f m β}
    → (x ⦂ α) ⊢ f · m ˸ β
    → (x ⦂ α) ⊢ m ˸ (domain f)
  ⊢·-f₁ {x} {α} {f} {m} (⊢· t p) =
    subst (λ - → (x ⦂ α) ⊢ m ˸ -) (sym p) t

  ⊢·-f₂ : ∀ {x α f m γ}
    → (x ⦂ α) ⊢ f · m ˸ γ
    → codomain f ≡ γ
  ⊢·-f₂ {x} {α} {f} {m} (⊢· t p) = refl

  rename : ∀ {x α m β y}
    → ((x ⦂ α) ⊢ m ˸ β)
      ----------------------------------
    → ((y ⦂ α) ⊢ (m [ x := (` y) ]) ˸ β)
  rename {x} {α} {m = ` z} {y = y} t with z ≟ x
  ... | yes _   = subst (λ - → (y ⦂ α) ⊢ ` y ˸ -) (⊢`-uniq₂ t) ⊢`
  ... | no  x≢y = ⊥-elim (x≢y (sym (⊢`-uniq₁ t)))
  rename {x} {α} {m = f · m} {y = y} t =
    subst (λ - → (y ⦂ α) ⊢ f · m [ x := ` y ] ˸ -)
      (⊢·-f₂ t) (⊢· (rename {y = y} (⊢·-f₁ t)) refl)

  ⊢-subst : ∀ {x α m β y θ n}
        → ((x ⦂ α) ⊢ m ˸ β)
        → ((y ⦂ θ) ⊢ n ˸ α)
        --------------------------------
        → ((y ⦂ θ) ⊢ (m [ x := n ]) ˸ β)
  ⊢-subst {x} ⊢` t with x ≟ x
  ... | yes _ = t
  ... | no x≢x = ⊥-elim (x≢x refl)
  ⊢-subst (⊢· t' p) t = ⊢· (⊢-subst t' t) p
```

# Theories

```agda
  data _⊢_＝_˸_ : Context → Term → Term → Type → Set (ℓ₁ ⊔ ℓ₂) where
    ⊢＝ : ∀ {x α m m' β}
       → ((x ⦂ α) ⊢ m ˸ β)
       → ((x ⦂ α) ⊢ m' ˸ β)
       → ((x ⦂ α) ⊢ m ＝ m' ˸ β)

  ⊢＝-refl : ∀ {x α m β}
    → ((x ⦂ α) ⊢ m ˸ β)
    → ((x ⦂ α) ⊢ m ＝ m ˸ β)
  ⊢＝-refl t = ⊢＝ t t

  ⊢＝-sym : ∀ {x α m m' β}
    → ((x ⦂ α) ⊢ m ＝ m' ˸ β)
    → ((x ⦂ α) ⊢ m' ＝ m ˸ β)
  ⊢＝-sym (⊢＝ e e') = ⊢＝ e' e

  ⊢＝-trans : ∀ {x α m m' m'' β}
    → ((x ⦂ α) ⊢ m ＝ m' ˸ β)
    → ((x ⦂ α) ⊢ m' ＝ m'' ˸ β)
    → ((x ⦂ α) ⊢ m ＝ m'' ˸ β)
  ⊢＝-trans (⊢＝ e _) (⊢＝ _ e') = ⊢＝ e e'

  ⊢＝-subst : ∀ {x α m m' β y γ n n'}
       → (x ⦂ α) ⊢ m ＝ m' ˸ β
       → (y ⦂ γ) ⊢ n ＝ n' ˸ α
       → (y ⦂ γ) ⊢ (m [ x := n ]) ＝ (m' [ x := n' ]) ˸ β
  ⊢＝-subst (⊢＝ e e') (⊢＝ e'' e''') = ⊢＝ (⊢-subst e e'') (⊢-subst e' e''')

  record Equation : Set (suc (ℓ₁ ⊔ ℓ₂)) where
    constructor [_⊢_＝_˸_][_]
    field
      ctx : Context
      termˡ : Term
      termʳ : Term
      type : Type
      eq : ctx ⊢ termˡ ＝ termʳ ˸ type

  record Theory (ℓ₃ : Level) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
    field
      Axiom : Equation → Set ℓ₃

module _ {ℓ₁ ℓ₂ ℓ₃} (Sg : Signature ℓ₁ ℓ₂)
         (Th : sigs.Theory {ℓ₁} {ℓ₂} Sg ℓ₃) where
  open sigs Sg
  open Theory Th

  data Theorem : Equation → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where

    Ax : ∀ {eq}
       → Axiom eq
         -------------------
       → Theorem eq

    Th-refl : ∀ {x α m β}
       → (t : (x ⦂ α) ⊢ m ˸ β)
         -------------------
       → Theorem [ (x ⦂ α) ⊢ m ＝ m ˸ β ][ ⊢＝-refl t ]

    Th-sym : ∀ {x α m m' β e}
       → Theorem [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ e ]
         -------------------
       → Theorem [ (x ⦂ α) ⊢ m' ＝ m ˸ β ][ ⊢＝-sym e ]

    Th-trans : ∀ {x α m m' m'' β e e'}
       → Theorem [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ e ]
       → Theorem [ (x ⦂ α) ⊢ m' ＝ m'' ˸ β ][ e' ]
         -------------------
       → Theorem [ (x ⦂ α) ⊢ m ＝ m'' ˸ β ][ ⊢＝-trans e e' ]

    Th-subst : ∀ {x α m m' β e y γ n n' e'}
       → Theorem [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ e ]
       → Theorem [ (y ⦂ γ) ⊢ n ＝ n' ˸ α ][ e' ]
         -------------------
       → Theorem [ (y ⦂ γ) ⊢ (m [ x := n ]) ＝ (m' [ x := n' ]) ˸ β ][ ⊢＝-subst e e' ]
```
