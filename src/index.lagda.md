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
open import Relation.Nullary using (yes; no)
open import Data.String using (String; _≟_)

open import Categories.Category.Core using (Category)
```

# 1. Syntax

## 1.1. Terms

```agda
variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

record Signature : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    Type : Set ℓ₁
    Function : Set ℓ₂
    domain : Function → Type
    codomain : Function → Type

module sigs (Sg : Signature {ℓ₁} {ℓ₂}) where
  open Signature Sg public

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
  ... | yes refl       = refl
  ... | no  _          = refl
  subst-id {x} (L · M) = cong (L ·_) (subst-id M)
```

## 1.2 Proved Terms

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

  record ProvedTerm : Set (suc (ℓ₁ ⊔ ℓ₂)) where
    constructor [_⊢_˸_][_]
    field
      ctx : Context
      term : Term
      type : Type
      wit : ctx ⊢ term ˸ type

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
  ⊢·-f₁ {x} {α} {f} {m} (⊢· t refl) = t

  ⊢·-f₂ : ∀ {x α f m γ}
    → (x ⦂ α) ⊢ f · m ˸ γ
    → codomain f ≡ γ
  ⊢·-f₂ {x} {α} {f} {m} (⊢· t refl) = refl

  rename : ∀ {x α m β y}
    → ((x ⦂ α) ⊢ m ˸ β)
      ----------------------------------
    → ((y ⦂ α) ⊢ (m [ x := (` y) ]) ˸ β)
  rename {x} {α} {m = ` z} {y = y} t with z ≟ x
  ... | yes refl   = subst (λ - → (y ⦂ α) ⊢ ` y ˸ -) (⊢`-uniq₂ t) ⊢`
  ... | no  x≢y    = ⊥-elim (x≢y (sym (⊢`-uniq₁ t)))
  rename {x} {α} {m = f · m} {y = y} t =
    subst (λ - → (y ⦂ α) ⊢ f · m [ x := ` y ] ˸ -)
      (⊢·-f₂ t) (⊢· (rename {y = y} (⊢·-f₁ t)) refl)

  ⊢-subst : ∀ {x α m β y θ n}
    → ((x ⦂ α) ⊢ m ˸ β)
    → ((y ⦂ θ) ⊢ n ˸ α)
    --------------------------------
    → ((y ⦂ θ) ⊢ (m [ x := n ]) ˸ β)
  ⊢-subst {x} ⊢` t with x ≟ x
  ... | yes _  = t
  ... | no x≢x = ⊥-elim (x≢x refl)
  ⊢-subst (⊢· t' refl) t = ⊢· (⊢-subst t' t) refl

  `-subst : ∀ {x n}
    -----------------------
    →  (` x) [ x := n ] ≡ n
  `-subst {x} with x ≟ x
  ... | yes _  = refl
  ... | no x≢x = ⊥-elim (x≢x refl)
```

## 1.3. Theories

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
  ⊢＝-subst (⊢＝ e e') (⊢＝ e'' e''') =
    ⊢＝ (⊢-subst e e'') (⊢-subst e' e''')

  record Equation : Set (ℓ₁ ⊔ ℓ₂) where
    constructor [_⊢_＝_˸_][_]
    field
      ctx : Context
      termˡ : Term
      termʳ : Term
      type : Type
      wit : ctx ⊢ termˡ ＝ termʳ ˸ type

  record Theory : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
    field
      Axiom : Equation → Set ℓ₃
```

## 1.4. Theorems

```agda
module _ (Sg : Signature {ℓ₁} {ℓ₂})
         (Th : sigs.Theory {ℓ₁} {ℓ₂} Sg {ℓ₃}) where
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
       → Theorem [ (y ⦂ γ) ⊢ (m [ x := n ]) ＝
           (m' [ x := n' ]) ˸ β ][ ⊢＝-subst e e' ]
```

# 2. Semantics

## 2.1. Structures

```agda
  record Structure : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)) where
    field
      𝒞 : Category ℓ₄ ℓ₅ ℓ₆
      ⟦_⟧ₒ : Type → Category.Obj 𝒞
      ⟦_⟧ₐ : (f : Function)
           → Category._⇒_ 𝒞 ⟦ domain f ⟧ₒ ⟦ codomain f ⟧ₒ

module _ (Sg : Signature {ℓ₁} {ℓ₂})
         (Th : sigs.Theory {ℓ₁} {ℓ₂} Sg {ℓ₃})
         (ℳ : Structure Sg Th {ℓ₄} {ℓ₅} {ℓ₆}) where
  open sigs Sg
  open Theory Th
  open Structure ℳ
  open Category 𝒞
  open HomReasoning

  Ctx⟦_⟧ : Context → Obj
  Ctx⟦ x ⦂ α ⟧ = ⟦ α ⟧ₒ

  ⟦⟧-helper : ∀ ctx m β
    → (ctx ⊢ m ˸ β)
    → (Ctx⟦ ctx ⟧) ⇒ (⟦ β ⟧ₒ)
  ⟦⟧-helper (x ⦂ α) m β ⊢` = id
  ⟦⟧-helper (x ⦂ α) (f · m) β (⊢· {β = θ} t refl) =
    ⟦ f ⟧ₐ ∘ (⟦⟧-helper (x ⦂ α) m θ t)

  ⟦_⟧ : (t : ProvedTerm)
      → (Ctx⟦ ProvedTerm.ctx t ⟧) ⇒ (⟦ ProvedTerm.type t ⟧ₒ)
  ⟦ [ ctx ⊢ term ˸ type ][ wit ] ⟧ = ⟦⟧-helper ctx term type wit

  ⟦⟧-irrelevance : ∀ {x α m m' β}
    → m ≡ m'
    → (w : (x ⦂ α) ⊢ m ˸ β)
    → (w' : (x ⦂ α) ⊢ m' ˸ β)
    → ⟦ [ (x ⦂ α) ⊢ m ˸ β ][ w ] ⟧ ≡ ⟦ [ (x ⦂ α) ⊢ m' ˸ β ][ w' ] ⟧
  ⟦⟧-irrelevance {x} {α} {(` x)} refl ⊢` ⊢` = refl
  ⟦⟧-irrelevance {x} {α} {(f · m)} {β} refl (⊢· w refl) (⊢· w' refl) =
    cong (⟦ f ⟧ₐ ∘_) (⟦⟧-irrelevance refl w w')

  ⟦⟧-subst : ∀ {x α m β y θ n}
    → (w : (x ⦂ α) ⊢ m ˸ β)
    → (w' : (y ⦂ θ) ⊢ n ˸ α)
    --------------------------------
    → (⟦ [ (y ⦂ θ) ⊢ (m [ x := n ]) ˸ β ][ ⊢-subst w w' ] ⟧) ≈
        (⟦ [ (x ⦂ α) ⊢ m ˸ β ][ w ] ⟧) ∘
        (⟦ [ (y ⦂ θ) ⊢ n ˸ α ][ w' ] ⟧)
  ⟦⟧-subst {x} {α} {` x} {β} {y} {θ} {n} ⊢` w = begin
    ⟦ [ y ⦂ θ ⊢ (` x) [ x := n ] ˸ α ][ ⊢-subst ⊢` w ] ⟧ ≡⟨ irrelevant ⟩
    ⟦ [ y ⦂ θ ⊢ n ˸ α ][ w ] ⟧                           ≈˘⟨ identityˡ ⟩
    id ∘ ⟦ [ y ⦂ θ ⊢ n ˸ α ][ w ] ⟧                      ≡⟨⟩
    ⟦ [ x ⦂ α ⊢ ` x ˸ α ][ ⊢` ] ⟧ ∘ ⟦ [ y ⦂ θ ⊢ n ˸ α ][ w ] ⟧ ∎
   where
    irrelevant = ⟦⟧-irrelevance (`-subst {x} {n}) (⊢-subst ⊢` w) w

  ⟦⟧-subst {x} {α} {f · m} {β} {y} {θ} {n} (⊢· t refl) w = begin
    ⟦ [ y ⦂ θ ⊢ (f · m) [ x := n ] ˸ β ][ ⊢-subst (⊢· t refl) w ] ⟧ ≡⟨⟩
    ⟦ [ y ⦂ θ ⊢ f · (m [ x := n ]) ˸ β ][ ⊢-subst (⊢· t refl) w ] ⟧ ≡⟨⟩
    ⟦ f ⟧ₐ ∘ ⟦ [ y ⦂ θ ⊢ m [ x := n ] ˸ domain f ][ ⊢-subst t w  ] ⟧ ≈⟨ ind ⟩
    ⟦ f ⟧ₐ ∘ ((⟦ [ (x ⦂ α) ⊢ m ˸ domain f ][ t ] ⟧) ∘
               (⟦ [ (y ⦂ θ) ⊢ n ˸ α ][ w ] ⟧)) ≈˘⟨ assoc ⟩
    (⟦ f ⟧ₐ ∘ (⟦ [ (x ⦂ α) ⊢ m ˸ domain f ][ t ] ⟧)) ∘
               (⟦ [ (y ⦂ θ) ⊢ n ˸ α ][ w ] ⟧) ≈⟨ rearrenge ⟩
    ⟦ [ x ⦂ α ⊢ f · m ˸ β ][ ⊢· t refl ] ⟧ ∘
      ⟦ [ y ⦂ θ ⊢ n ˸ α ][ w ] ⟧ ∎
   where
    ind = ∘-resp-≈ʳ (⟦⟧-subst t w)
    rearrenge = ∘-resp-≈ˡ Equiv.refl
```


## 2.2. Models

```agda

```

## 2.3. Categories of Models

```agda

```

## 2.4. Clasifying category

```agda

```

## 2.5. Correspondence Theorem

```agda

```

## 3. Example

```agda

```
