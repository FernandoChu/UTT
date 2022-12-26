---
title: Unary Ty Theory
isIndex: true
---

```agda
module index where

open import Level using (Level; _⊔_; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; subst; cong; cong₂; cong-app)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _≟_)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Nullary using (yes; no)

open import Categories.Category using
  (Category; _[_,_]; _[_≈_]; _[_∘_]; module Definitions)
open import Categories.Functor using (Functor)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.NaturalTransformation using
  (NaturalTransformation) renaming (id to idN)
import Categories.Morphism.Reasoning
```

# 1. Syntax

## 1.1. Terms

```agda
variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₄' ℓ₅' ℓ₆' : Level

record Signature : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    Ty : Set ℓ₁
    Fun : Set ℓ₂
    Dom : Fun → Ty
    Cod : Fun → Ty

module sigs (Sg : Signature {ℓ₁} {ℓ₂}) where
  open Signature Sg public

  Id : Set
  Id = String

  infixl 7  _·_
  infix  9  `_

  data Term : Set ℓ₂ where
    `_  : Id → Term
    _·_ : Fun → Term → Term

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

  subst-≡ : ∀ {x m m'}
        → ` x ≡ m
        → m [ x := m' ] ≡ m'
  subst-≡ {x} {m} {m'} refl with x ≟ x
  ... | yes _  = refl
  ... | no x≢x = ⊥-elim (x≢x refl)

```

## 1.2 Proved Terms

```agda
  infix 5  _⦂_
  data Context : Set ℓ₁ where
    _⦂_ : Id → Ty → Context

  ContextTy : Context → Ty
  ContextTy (x ⦂ α) = α

  infix 4 _⊢_˸_
  data _⊢_˸_ : Context → Term → Ty → Set (ℓ₁ ⊔ ℓ₂) where
    ⊢` : ∀ {x α}
        -------------------
       → x ⦂ α ⊢ (` x) ˸ α
    ⊢· : ∀ {x α m β f}
       → (x ⦂ α) ⊢ m ˸ β
       → Dom f ≡ β
       ------------------------------
       → (x ⦂ α) ⊢ (f · m) ˸ Cod f

  infix 4 [_⊢_˸_][_]
  record ProvedTerm : Set (suc (ℓ₁ ⊔ ℓ₂)) where
    constructor [_⊢_˸_][_]
    field
      ctx : Context
      term : Term
      ty : Ty
      wit : ctx ⊢ term ˸ ty

    PTContextTy : Ty
    PTContextTy = ContextTy ctx

  unique-Tys : ∀ {x α m β γ}
    → (x ⦂ α) ⊢ m ˸ β
    → (x ⦂ α) ⊢ m ˸ γ
    -----------------
    → β ≡ γ
  unique-Tys ⊢` ⊢` = refl
  unique-Tys (⊢· _ _) (⊢· _ _) = refl

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

  ⊢-uniq-wit : ∀ {x α β m}
      → (w w' : (x ⦂ α) ⊢ m ˸ β)
      → w ≡ w'
  ⊢-uniq-wit ⊢` ⊢` = refl
  ⊢-uniq-wit (⊢· w refl) (⊢· w' refl) =
    cong-app (cong ⊢· (⊢-uniq-wit w w')) refl

  ⊢·-f₁ : ∀ {x α f m β}
    → (x ⦂ α) ⊢ f · m ˸ β
    → (x ⦂ α) ⊢ m ˸ (Dom f)
  ⊢·-f₁ {x} {α} {f} {m} (⊢· t refl) = t

  ⊢·-f₂ : ∀ {x α f m γ}
    → (x ⦂ α) ⊢ f · m ˸ γ
    → Cod f ≡ γ
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
  infix 4 _⊢_＝_˸_
  data _⊢_＝_˸_ : Context → Term → Term → Ty → Set (ℓ₁ ⊔ ℓ₂) where
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

  subst-assoc : ∀ {x y z α β θ γ m m' m''}
      → (x ⦂ α) ⊢ m ˸ β
      → (y ⦂ β) ⊢ m' ˸ θ
      → (z ⦂ θ) ⊢ m'' ˸ γ
      → (m'' [ z := m' ]) [ y := m ] ≡  m'' [ z := m' [ y := m ] ]
  subst-assoc {x} {y} {z} {α} {β} {θ} {.θ} {m} {m'} {.(` z)} t t' ⊢`
    with z ≟ z
  ...  | yes _  = refl
  ...  | no z≢z = ⊥-elim (z≢z refl)
  subst-assoc t t' (⊢· {f = f} t'' p) =
      cong (f ·_) (subst-assoc t t' t'')

  infix 4 [_⊢_＝_˸_][_]
  record Equation : Set (ℓ₁ ⊔ ℓ₂) where
    constructor [_⊢_＝_˸_][_]
    field
      ctx : Context
      termˡ : Term
      termʳ : Term
      Ty : Ty
      wit : ctx ⊢ termˡ ＝ termʳ ˸ Ty

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

  Th-wit-irrelevance : ∀ {x α β m m' w w'}
      → Theorem [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ w ]
      → Theorem [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ w' ]
  Th-wit-irrelevance {x} {α} {β} {m} {m'} {⊢＝ w₁ w₂} {⊢＝ w₁' w₂'} th =
    subst (λ - → Theorem [ x ⦂ α ⊢ m ＝ m' ˸ β ][ - ])
      (cong₂ ⊢＝ (⊢-uniq-wit w₁ w₁') (⊢-uniq-wit w₂ w₂')) th

  ⊢＝-uniq-type : ∀ {x α β β' m m'}
      → (x ⦂ α) ⊢ m ˸ β
      → (x ⦂ α) ⊢ m ＝ m' ˸ β'
      → β ≡ β'
  ⊢＝-uniq-type ⊢` (⊢＝ w w') = unique-Tys ⊢` w
  ⊢＝-uniq-type (⊢· wit p) (⊢＝ (⊢· w x) w') = refl

  Th-≡ : ∀ {x α β m m' w}
      → (x ⦂ α) ⊢ m ˸ β
      → m ≡ m'
      → Theorem [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ w ]
  Th-≡ {w = w'} w refl = Th-wit-irrelevance {w' = w'} (Th-refl w)

  Th-subst-sym : ∀ {x y α β m m' w w'}
    → Theorem [ (x ⦂ α) ⊢ m ＝ m' [ y := ` x ] ˸ β ][ w ]
    → Theorem [ (y ⦂ α) ⊢ m' ＝ m [ x := ` y ] ˸ β ][ w' ]
  Th-subst-sym {x} {y} {α} {β} {m} {m'} {⊢＝ w₁ w₂} {⊢＝ w₁' w₂'} th =
      Th-wit-irrelevance (Th-trans th-lemma' th-lemma)
    where
      open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)
      th-lemma :
        Theorem
            [ y ⦂ α ⊢
              (m' [ y := ` x ]) [ x := ` y ] ＝
                m [ x := ` y ] ˸ β ][
                ⊢＝-subst (⊢＝-sym (⊢＝ w₁ w₂)) (⊢＝-refl ⊢`) ]
      th-lemma =
        Th-subst (Th-sym (Th-wit-irrelevance {w' = ⊢＝ w₁ w₂ } th)) (Th-refl (⊢` {x = y}))

      ≡-lemma : m' ≡ (m' [ y := ` x ]) [ x := ` y ]
      ≡-lemma = begin
        m' ≡˘⟨ subst-id m' ⟩
        (m') [ y := ` y ] ≡˘⟨ cong (λ - → m' [ y := - ]) (subst-≡ refl) ⟩
        (m' [ y := (` x) [ x := ` y ] ]) ≡˘⟨ subst-assoc (⊢` {y} {α}) (⊢` {x} {α}) w₁' ⟩
        ((m' [ y := ` x ]) [ x := ` y ]) ∎

      th-lemma' :
        Theorem
            [ y ⦂ α ⊢ m' ＝ (m' [ y := ` x ]) [ x := ` y ] ˸ β ][
              ⊢＝ w₁' (subst (λ - → y ⦂ α ⊢ - ˸ β) ≡-lemma w₁' ) ]
      th-lemma' = Th-≡ w₁' ≡-lemma

  Th-subst-trans : ∀ {x y z α β m m' m'' w w' w''}
    → (z ⦂ α) ⊢ m'' ˸ β
    → Theorem [ (x ⦂ α) ⊢ m ＝ m' [ y := ` x ] ˸ β ][ w ]
    → Theorem [ (y ⦂ α) ⊢ m' ＝ m'' [ z := ` y ] ˸ β ][ w' ]
    → Theorem [ (x ⦂ α) ⊢ m ＝ m'' [ z := ` x ] ˸ β ][ w'' ]
  Th-subst-trans {x} {y} {z} {α} {β} {m} {m'} {m''} {⊢＝ w₁ w₂} {⊢＝ w₁' w₂'} {⊢＝ w₁'' w₂''} t th th' =
      Th-wit-irrelevance (Th-trans (Th-trans th th-lemma') th-lemma)
    where
      open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)
      ≡-lemma : (m'' [ z := ` y ]) [ y := ` x ] ≡ m'' [ z := ` x ]
      ≡-lemma = begin
        (m'' [ z := ` y ]) [ y := ` x ] ≡⟨ subst-assoc (⊢` {x = x}) (⊢` {x = y}) t ⟩
        m'' [ z := (` y) [ y := ` x ] ] ≡⟨ cong (λ - → m'' [ z := - ]) (`-subst {y} {` x}) ⟩
        m'' [ z := ` x ] ∎
      th-lemma :
        Theorem
            [ x ⦂ α ⊢ (m'' [ z := ` y ]) [ y := ` x ] ＝ m'' [ z := ` x ] ˸ β ][
               ⊢＝ (⊢-subst w₂' (⊢` {x = x})) w₂'' ]
      th-lemma = Th-wit-irrelevance
        (Th-≡ {w = subst (λ - → x ⦂ α ⊢ - ＝ m'' [ z := ` x ] ˸ β) (sym ≡-lemma)
          (⊢＝-refl {x} {α} {m'' [ z := ` x ]} {β} w₂'')} (⊢-subst w₂' (⊢` {x = x})) ≡-lemma)
      th-lemma' :
        Theorem
            [ x ⦂ α ⊢ (m' [ y := ` x ]) ＝ (m'' [ z := ` y ]) [ y := ` x ] ˸ β ][
               ⊢＝ w₂ (subst (λ - → x ⦂ α ⊢ - ˸ β) (sym ≡-lemma) w₂'')  ]
      th-lemma' = Th-wit-irrelevance (Th-subst th' (Th-refl (⊢` {x = x})))

  Th-subst-resp : ∀ {x y x' y' α β θ m m' n n'}
    → (w1 : x ⦂ α ⊢ m ˸ β)
    → (w1' : x' ⦂ α ⊢ m' ˸ β)
    → (w2 : y ⦂ β ⊢ n ˸ θ)
    → (w2' : y' ⦂ β ⊢ n' ˸ θ)
    → Theorem [ x ⦂ α ⊢ m ＝ m' [ x' := ` x ] ˸ β ][ ⊢＝ w1 (⊢-subst w1' ⊢`) ]
    → Theorem [ y ⦂ β ⊢ n ＝ n' [ y' := ` y ] ˸ θ ][ ⊢＝ w2 (⊢-subst w2' ⊢`) ]
    → Theorem [ x ⦂ α ⊢ n [ y := m ] ＝ (n' [ y' := m' ]) [ x' := ` x ] ˸ θ ][ ⊢＝ (⊢-subst w2 w1) (⊢-subst (⊢-subst w2' w1') ⊢`) ]
  Th-subst-resp {x} {y} {x'} {y'} {α} {β} {θ} {m} {m'} {n} {n'} w1 w1' w2 w2' th th' =
      Th-wit-irrelevance (Th-trans th-lemma th-lemma')
    where
      open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)
      wi' : x ⦂ α ⊢ m' [ x' := (` x) ] ˸ β
      wi' = ⊢-subst w1' (⊢` {x})
      ≡-lemma : (n' [ y' := (` y) ]) [ y := (m' [ x' := (` x) ])] ≡ (n' [ y' := m' ]) [ x' := (` x) ]
      ≡-lemma = begin
        (n' [ y' := (` y) ]) [ y := (m' [ x' := (` x) ])] ≡⟨ subst-assoc wi' (⊢` {y}) w2' ⟩
        n' [ y' := (` y) [ y := (m' [ x' := (` x) ])] ] ≡⟨ cong (λ - → n' [ y' := - ]) `-subst ⟩
        n' [ y' := (m' [ x' := (` x) ]) ] ≡˘⟨ subst-assoc (⊢` {x}) w1' w2' ⟩
        (n' [ y' := m' ]) [ x' := (` x) ] ∎

      th-lemma : Theorem
                   [ x ⦂ α ⊢ n [ y := m ] ＝
                   (n' [ y' := ` y ]) [ y := m' [ x' := ` x ] ] ˸ θ ][ ⊢＝-subst (⊢＝ w2 (⊢-subst w2' ⊢`)) (⊢＝ w1 (⊢-subst w1' ⊢`)) ]
      th-lemma = Th-subst th' th

      idk : x ⦂ α ⊢ (n' [ y' := (` y) ]) [ y := (m' [ x' := (` x) ])] ˸ θ
      idk = ⊢-subst (⊢-subst w2' (⊢` {y})) (⊢-subst w1' (⊢` {x}))

      th-lemma' :
        Theorem
            [ x ⦂ α ⊢ (n' [ y' := (` y) ]) [ y := (m' [ x' := (` x) ])] ＝
                   (n' [ y' := m' ]) [ x' := (` x) ] ˸ θ ][
               ⊢＝ idk (⊢-subst (⊢-subst w2' w1') ⊢`) ]
      th-lemma' = Th-wit-irrelevance (Th-≡ {w = ⊢＝ idk (⊢-subst (⊢-subst w2' w1') ⊢`) } idk ≡-lemma)

```

# 2. Semantics

## 2.1. Structures

```agda
  record Structure (𝒞 : Category ℓ₄ ℓ₅ ℓ₆) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)) where
    field
      ⟦_⟧ₒ : Ty → Category.Obj 𝒞
      ⟦_⟧ₐ : (f : Fun)
           → Category._⇒_ 𝒞 ⟦ Dom f ⟧ₒ ⟦ Cod f ⟧ₒ

module _ (Sg : Signature {ℓ₁} {ℓ₂})
         (Th : sigs.Theory {ℓ₁} {ℓ₂} Sg {ℓ₃})
         (𝒞 : Category ℓ₄ ℓ₅ ℓ₆)
         (ℳ : Structure Sg Th 𝒞) where
  open sigs Sg
  open Theory Th
  open Category 𝒞
  open Structure ℳ
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
      → (Ctx⟦ ProvedTerm.ctx t ⟧) ⇒ (⟦ ProvedTerm.ty t ⟧ₒ)
  ⟦ [ ctx ⊢ term ˸ Ty ][ wit ] ⟧ = ⟦⟧-helper ctx term Ty wit

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
    ⟦ f ⟧ₐ ∘ ⟦ [ y ⦂ θ ⊢ m [ x := n ] ˸ Dom f ][ ⊢-subst t w  ] ⟧ ≈⟨ ind ⟩
    ⟦ f ⟧ₐ ∘ ((⟦ [ (x ⦂ α) ⊢ m ˸ Dom f ][ t ] ⟧) ∘
               (⟦ [ (y ⦂ θ) ⊢ n ˸ α ][ w ] ⟧)) ≈˘⟨ assoc ⟩
    (⟦ f ⟧ₐ ∘ (⟦ [ (x ⦂ α) ⊢ m ˸ Dom f ][ t ] ⟧)) ∘
               (⟦ [ (y ⦂ θ) ⊢ n ˸ α ][ w ] ⟧) ≈⟨ rearrange ⟩
    ⟦ [ x ⦂ α ⊢ f · m ˸ β ][ ⊢· t refl ] ⟧ ∘
      ⟦ [ y ⦂ θ ⊢ n ˸ α ][ w ] ⟧ ∎
   where
    ind = ∘-resp-≈ʳ (⟦⟧-subst t w)
    rearrange = ∘-resp-≈ˡ Equiv.refl
```

## 2.2. Models

```agda
  satisfies : Equation → Set ℓ₆
  satisfies [ x ⦂ α ⊢ m ＝ m' ˸ β ][ ⊢＝ w w' ] =
    ⟦ [ (x ⦂ α) ⊢ m ˸ β ][ w ] ⟧ ≈ ⟦ [ (x ⦂ α) ⊢ m' ˸ β ][ w' ] ⟧

  satisfies-irrelevance :
      ∀ {x α m m' β w w'}
    → satisfies [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ w ]
    → satisfies [ (x ⦂ α) ⊢ m ＝ m' ˸ β ][ w' ]
  satisfies-irrelevance {x} {α} {m} {m'} {β} {⊢＝ w₁ w₂} {⊢＝ w₁' w₂'} p =
    begin
      ⟦ [ x ⦂ α ⊢ m ˸ β ][ w₁' ]  ⟧ ≡⟨ ⟦⟧-irrelevance refl w₁' w₁ ⟩
      ⟦ [ x ⦂ α ⊢ m ˸ β ][ w₁ ]   ⟧ ≈⟨ p ⟩
      ⟦ [ x ⦂ α ⊢ m' ˸ β ][ w₂ ]  ⟧ ≡⟨ ⟦⟧-irrelevance refl w₂ w₂' ⟩
      ⟦ [ x ⦂ α ⊢ m' ˸ β ][ w₂' ] ⟧ ∎

  models : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₆)
  models = ∀ {eq}
         → Axiom eq
         → satisfies eq

  Soundness : models
        → ∀ eq
        → Theorem Sg Th eq
        → satisfies eq
  Soundness M eq (Ax ax) = M ax
  Soundness M eq (Th-refl t) = Equiv.refl
  Soundness M eq (Th-sym {e = ⊢＝ e e'} T) =
    Equiv.sym (Soundness M _ T)
  Soundness M eq (Th-trans {x} {α} {m} {m'} {m''} {β} {⊢＝ e₁ e₁'} {⊢＝ e₂ e₂'} T T') =
    begin
      ⟦ [ x ⦂ α ⊢ m ˸ β ][ e₁ ]    ⟧ ≈⟨ Soundness M _ T ⟩
      ⟦ [ x ⦂ α ⊢ m' ˸ β ][ e₁' ]  ⟧ ≡⟨ ⟦⟧-irrelevance refl e₁' e₂  ⟩
      ⟦ [ x ⦂ α ⊢ m' ˸ β ][ e₂ ]   ⟧ ≈⟨ Soundness M _ T' ⟩
      ⟦ [ x ⦂ α ⊢ m'' ˸ β ][ e₂' ] ⟧ ∎
  Soundness M eq (Th-subst {x} {α} {m} {m'} {β} {⊢＝ {m' = m'} e₁ e₁'} {y} {θ} {n} {n'} {⊢＝ e₂ e₂'} T T') =
    begin
      ⟦ [ y ⦂ θ ⊢ m [ x := n ] ˸ β ][ ⊢-subst e₁ e₂ ]             ⟧ ≈⟨ ⟦⟧-subst e₁ e₂ ⟩
      ⟦ [ x ⦂ α ⊢ m ˸ β ][ e₁ ] ⟧ ∘ ⟦ [ y ⦂ θ ⊢ n ˸ α ][ e₂ ]     ⟧ ≈⟨ ind ⟩
      ⟦ [ x ⦂ α ⊢ m' ˸ β ][ e₁' ] ⟧ ∘ ⟦ [ y ⦂ θ ⊢ n' ˸ α ][ e₂' ] ⟧ ≈˘⟨ ⟦⟧-subst e₁' e₂' ⟩
      ⟦ [ y ⦂ θ ⊢ m' [ x := n' ] ˸ β ][ ⊢-subst e₁' e₂' ]         ⟧ ∎
   where
    ind = ∘-resp-≈ (Soundness M _ T ) (Soundness M _ T')

```

## 2.3. Categories of Models

```agda
module _ (Sg : Signature {ℓ₁} {ℓ₂})
         (Th : sigs.Theory {ℓ₁} {ℓ₂} Sg {ℓ₃}) where
  open sigs Sg
  open Theory Th

  record ℳℴ𝒹ₒ (𝒞 : Category ℓ₄ ℓ₅ ℓ₆) : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)) where
    field
      ℳℴ𝒹⟦⟧ : Structure Sg Th 𝒞
      ℳℴ𝒹⊨ : models Sg Th 𝒞 ℳℴ𝒹⟦⟧

  open ℳℴ𝒹ₒ public

  record ℳℴ𝒹ₐ (𝒞 : Category ℓ₄ ℓ₅ ℓ₆)
              (ℳ 𝒩 : ℳℴ𝒹ₒ 𝒞)
             : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)) where
    private
      module ℳ = Structure (ℳℴ𝒹⟦⟧ ℳ)
      module 𝒩 = Structure (ℳℴ𝒹⟦⟧ 𝒩)
    open Category 𝒞
    open Definitions 𝒞
    field
      comp : (α : Ty) → ℳ.⟦ α ⟧ₒ ⇒ 𝒩.⟦ α ⟧ₒ
      square : (f : Fun) → CommutativeSquare (ℳ.⟦ f ⟧ₐ) (comp (Dom f)) (comp (Cod f)) (𝒩.⟦ f ⟧ₐ)
  open ℳℴ𝒹ₐ public

  ℳℴ𝒹 : Category ℓ₄ ℓ₅ ℓ₆ → Category (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆))
    (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆)) (ℓ₁ ⊔ ℓ₆)
  ℳℴ𝒹 𝒞 = record
    { Obj = ℳℴ𝒹ₒ 𝒞
    ; _⇒_ = ℳℴ𝒹ₐ 𝒞
    ; _≈_ = λ {ℳ} {𝒩} h h' → (α : Ty) → comp h α ≈ comp h' α
    ; id = record
      { comp = λ α → id
      ; square = λ f → identityˡ ○ ⟺ identityʳ
      }
    ; _∘_ = λ h' h → record
      { comp = λ α → comp h' α ∘ comp h α
      ; square = λ f → glue (square h' f) (square h f)
      }
    ; assoc = λ α → assoc
    ; sym-assoc = λ α → sym-assoc
    ; identityˡ = λ α → identityˡ
    ; identityʳ = λ α → identityʳ
    ; identity² = λ α → identity²
    ; equiv = record
      { refl = λ h → Equiv.refl
      ; sym = λ h α → Equiv.sym (h α)
      ; trans = λ h' h α → Equiv.trans (h' α) (h α)
      }
    ; ∘-resp-≈ = λ p' p α → ∘-resp-≈ (p' α) (p α)
    }
      where
        open Category 𝒞
        open HomReasoning
        open Categories.Morphism.Reasoning 𝒞

  _₊ : {𝒞 : Category ℓ₄ ℓ₅ ℓ₆} {𝒟 : Category ℓ₄' ℓ₅' ℓ₆'}
     → Functor 𝒞 𝒟
     → ℳℴ𝒹ₒ 𝒞 → ℳℴ𝒹ₒ 𝒟
  _₊ {𝒞 = 𝒞} {𝒟} F ℳ = record
    { ℳℴ𝒹⟦⟧ = ℳℴ𝒹⟦⟧₊
    ; ℳℴ𝒹⊨ = ℳℴ𝒹⊨₊
    }
    where
      open Functor F
      module ℳ = Structure (ℳℴ𝒹⟦⟧ ℳ)
      open Category 𝒟
      open HomReasoning
      ℳℴ𝒹⟦⟧₊ = record
        { ⟦_⟧ₒ = λ α → F₀ ℳ.⟦ α ⟧ₒ
        ; ⟦_⟧ₐ = λ f → F₁ ℳ.⟦ f ⟧ₐ
        }

      ℳ⟦_⟧ = ⟦_⟧ Sg Th 𝒞 (ℳℴ𝒹⟦⟧ ℳ)
      Fℳ⟦_⟧ = ⟦_⟧ Sg Th 𝒟 ℳℴ𝒹⟦⟧₊

      lemma : ∀ {x α m β w} →
        Fℳ⟦ [ x ⦂ α ⊢ m ˸ β ][ w ] ⟧ ≈
        F₁ ℳ⟦ [ x ⦂ α ⊢ m ˸ β ][ w ] ⟧
      lemma {w = ⊢`} = Equiv.sym identity
      lemma {x} {α} {(f · m)} {β} {w = ⊢· t refl} =
        begin
          Fℳ⟦ [ x ⦂ α ⊢ f · m ˸ Cod f ][ ⊢· t refl ] ⟧          ≡⟨⟩
          F₁ ℳ.⟦ f ⟧ₐ ∘ Fℳ⟦ [ x ⦂ α ⊢ m ˸ Dom f ][ t ] ⟧        ≈⟨ refl⟩∘⟨ lemma {w = t} ⟩
          F₁ ℳ.⟦ f ⟧ₐ ∘ F₁ ℳ⟦ [ x ⦂ α ⊢ m ˸ Dom f ][ t ] ⟧      ≈˘⟨ homomorphism ⟩
          F₁ (𝒞 [ ℳ.⟦ f ⟧ₐ ∘ ℳ⟦ [ x ⦂ α ⊢ m ˸ Dom f ][ t ] ⟧ ]) ≡⟨⟩
          F₁ (ℳ⟦ [ x ⦂ α ⊢ f · m ˸ Cod f ][ ⊢· t refl ] ⟧)      ∎

      ℳℴ𝒹⊨₊ : models Sg Th 𝒟 ℳℴ𝒹⟦⟧₊
      ℳℴ𝒹⊨₊ eq@{[ x ⦂ α ⊢ m ＝ m' ˸ β ][ ⊢＝ w w' ]} M =
        begin
          Fℳ⟦ [ x ⦂ α ⊢ m ˸ β ][ w ] ⟧     ≈⟨ lemma {w = w} ⟩
          F₁ ℳ⟦ [ x ⦂ α ⊢ m ˸ β ][ w ] ⟧   ≈⟨ F-resp-≈ ((ℳℴ𝒹⊨ ℳ) M) ⟩
          F₁ ℳ⟦ [ x ⦂ α ⊢ m' ˸ β ][ w' ] ⟧ ≈˘⟨ lemma {w = w'} ⟩
          Fℳ⟦ [ x ⦂ α ⊢ m' ˸ β ][ w' ] ⟧   ∎

  Ap₁ : {𝒞 : Category ℓ₄ ℓ₅ ℓ₆} {𝒟 : Category ℓ₄' ℓ₅' ℓ₆'}
       (ℳ : ℳℴ𝒹ₒ 𝒞)
       {F G : Functor 𝒞 𝒟}
     → Functors 𝒞 𝒟 [ F , G ] → ℳℴ𝒹 𝒟 [ (F ₊) ℳ , (G ₊) ℳ ]
  Ap₁ {𝒞 = 𝒞} {𝒟} ℳ {F} {G} ϕ = record
    { comp = λ α → ϕ.η ℳ.⟦ α ⟧ₒ 
    ; square = λ f → ϕ.commute (ℳ.⟦ f ⟧ₐ)
    }
    where
      module ℳ = Structure (ℳℴ𝒹⟦⟧ ℳ)
      module ϕ = NaturalTransformation ϕ

  Ap : {𝒞 : Category ℓ₄ ℓ₅ ℓ₆} {𝒟 : Category ℓ₄' ℓ₅' ℓ₆'}
     → ℳℴ𝒹ₒ 𝒞
     → Functor (Functors 𝒞 𝒟) (ℳℴ𝒹 𝒟)
  Ap {𝒞 = 𝒞} {𝒟} ℳ = record
    { F₀ = λ F → (F ₊) ℳ
    ; F₁ = Ap₁ ℳ
    ; identity = λ α → Equiv.refl
    ; homomorphism = λ α → Equiv.refl
    ; F-resp-≈ = λ f≈g α → f≈g
    }
    where
      open Category 𝒟
```

## 2.4. Clasifying category

```agda
  record 𝒞𝓁ₐ (α β : Ty) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
    constructor 𝒞𝓁ₐ⟨_,_,_⟩
    field
      pt : ProvedTerm
      ptα : ProvedTerm.PTContextTy pt ≡ α
      ptβ : ProvedTerm.ty pt ≡ β

  𝒞𝓁 : Category ℓ₁ (suc ℓ₁ ⊔ suc ℓ₂) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
  𝒞𝓁 = record
    { Obj = Ty
    ; _⇒_ = 𝒞𝓁ₐ
    ; _≈_ = _≈'_
    ; id = id'
    ; _∘_ = _∘'_
    ; assoc = assoc-helper
    ; sym-assoc = λ {α} {β} {θ} {γ} {f} {g} {h} → IsEquivalence.sym (equiv-helper) (assoc-helper {f = f} {g} {h})
    ; identityˡ = idˡ-helper
    ; identityʳ = idʳ-helper
    ; identity² = λ {α} → idʳ-helper {f = id'}
    ; equiv = equiv-helper
    ; ∘-resp-≈ = λ where
      {α} {β} {θ}
        { 𝒞𝓁ₐ⟨ [ y ⦂ β ⊢ n ˸ θ ][ w2 ] , refl , refl ⟩ }
        { 𝒞𝓁ₐ⟨ [ y' ⦂ β ⊢ n' ˸ θ ][ w2' ] , refl , refl ⟩ }
        { 𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ β ][ w1 ] , refl , refl ⟩ }
        { 𝒞𝓁ₐ⟨ [ x' ⦂ α ⊢ m' ˸ β ][ w1' ] , refl , refl ⟩ }
        th th'
        → Th-subst-resp Sg Th w1 w1' w2 w2' th' th
    }
    where
      id' : ∀ {α} → (𝒞𝓁ₐ α α)
      id' {α} = record
        { pt = [ (( "x" ⦂ α )) ⊢ ` "x" ˸ α ][ ⊢` ]
        ; ptα = refl
        ; ptβ = refl
        }
      _∘'_ : ∀ {A B C} → (𝒞𝓁ₐ B C) → (𝒞𝓁ₐ A B) → (𝒞𝓁ₐ A C)
      _∘'_ = λ where
       𝒞𝓁ₐ⟨ ([ y ⦂ β ⊢ m' ˸ θ ][ w' ]) , refl , refl ⟩
         𝒞𝓁ₐ⟨ ([ x ⦂ α ⊢ m ˸ β ][ w ]) , refl , refl ⟩
           → 𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m' [ y := m ] ˸ θ ][ ⊢-subst w' w  ]  , refl , refl ⟩
      _≈'_ : ∀ {A B} → Rel (𝒞𝓁ₐ A B) (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
      _≈'_ = λ where
       𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩
         𝒞𝓁ₐ⟨ [ y ⦂ α ⊢ m' ˸ β ][ w' ] , refl , refl ⟩
          → Theorem Sg Th
            [ x ⦂ α ⊢ m ＝ (m' [ y := (` x) ]) ˸ β ][ ⊢＝ w (⊢-subst w' ⊢` ) ]
      assoc-helper : ∀ {A B C D} {f : 𝒞𝓁ₐ A B} {g : 𝒞𝓁ₐ B C} {h : 𝒞𝓁ₐ C D} → _≈'_ (_∘'_ (_∘'_ h g) f) (_∘'_ h (_∘'_ g f))
      assoc-helper {α} {β} {θ} {γ}
          { 𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩ }
          { 𝒞𝓁ₐ⟨ [ y ⦂ β ⊢ m' ˸ θ ][ w' ] , refl , refl ⟩ }
          { 𝒞𝓁ₐ⟨ [ z ⦂ θ ⊢ m'' ˸ γ ][ w'' ] , refl , refl ⟩ }
          = Th-≡ Sg Th (⊢-subst (⊢-subst w'' w') w)
              (trans (subst-assoc w w' w'') (sym (subst-id _)) )
      equiv-helper : ∀ {A B} → IsEquivalence (_≈'_ {A} {B})
      equiv-helper = record
        { refl = λ where
            {𝒞𝓁ₐ⟨ ([ x ⦂ α ⊢ m ˸ β ][ w ]) , refl , refl ⟩}
              → Th-≡ Sg Th w ((sym (subst-id _)) )
        ; sym = λ where
            {𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩}
              { 𝒞𝓁ₐ⟨ [ y ⦂ α ⊢ m' ˸ β ][ w' ] , refl , refl ⟩ }
              th → Th-wit-irrelevance Sg Th ((Th-subst-sym Sg Th {w' = ⊢＝ w' (⊢-subst w ⊢`)} th) )
        ; trans = λ where
            {𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩}
              { 𝒞𝓁ₐ⟨ [ y ⦂ α ⊢ m' ˸ β ][ w' ] , refl , refl ⟩ }
              { 𝒞𝓁ₐ⟨ [ z ⦂ θ ⊢ m'' ˸ β ][ w'' ] , refl , refl ⟩ }
              th th' → Th-wit-irrelevance Sg Th
                (Th-subst-trans Sg Th {w'' = ⊢＝ w (⊢-subst w'' ⊢`)} w'' th th')
        }
      idˡ-helper : ∀ {A B} {f : 𝒞𝓁ₐ A B} → (id' ∘' f) ≈' f
      idˡ-helper {f = 𝒞𝓁ₐ⟨ [ y ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩} =
          Th-wit-irrelevance Sg Th
            (Th-≡ Sg Th {w = ⊢＝ (⊢-subst (⊢` {"x"}) w)
            (⊢-subst w ⊢`)} ((⊢-subst (⊢` {"x"}) w)) ≡-lemma)
        where
          open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)
          ≡-lemma : (` "x") [ "x" := m ] ≡ m [ y := ` y ]
          ≡-lemma = begin
            (` "x") [ "x" := m ] ≡⟨ `-subst {"x"} {m} ⟩
            m ≡˘⟨ subst-id m ⟩
            m [ y := ` y ] ∎
      idʳ-helper : ∀ {A B} {f : 𝒞𝓁ₐ A B} → (f ∘' id') ≈' f
      idʳ-helper {f = 𝒞𝓁ₐ⟨ [ y ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩} =
           Th-wit-irrelevance Sg Th
            (Th-≡ Sg Th {w = ⊢＝ (⊢-subst w ⊢`) (⊢-subst w ⊢`)}
              (⊢-subst w ⊢`) refl)

  𝒢⟦_⟧ₐ : (f : Fun) → 𝒞𝓁ₐ (Dom f) (Cod f)
  𝒢⟦_⟧ₐ = λ f →
      𝒞𝓁ₐ⟨ [ ("x" ⦂ Dom f) ⊢ (f · (` "x")) ˸ (Cod f) ][ ⊢· (⊢` {"x"}) refl ]
        , refl , refl ⟩

  𝒢st : Structure Sg Th 𝒞𝓁
  𝒢st = record
    { ⟦_⟧ₒ = λ - → -
    ; ⟦_⟧ₐ = 𝒢⟦_⟧ₐ
    }

  𝒢⟦_⟧ = ⟦_⟧ Sg Th 𝒞𝓁 𝒢st

  𝒞𝓁-⟦⟧ : ∀ {x α m β w}
    → Category._≈_ 𝒞𝓁 (𝒢⟦ [ (x ⦂ α) ⊢ m ˸ β ][ w ] ⟧) 𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩
  𝒞𝓁-⟦⟧ {x} {α} {.(` x)} {.α} {⊢`} = goal
    where
      open Category 𝒞𝓁
      goal : Theorem Sg Th [ "x" ⦂ α ⊢ ` "x"
        ＝ (` x) [ x := ` "x" ] ˸ α ][ ⊢＝ ⊢` (⊢-subst ⊢` ⊢`) ]
      goal = Th-wit-irrelevance Sg Th
        ((Th-≡ Sg Th {w =  ⊢＝ ⊢` (⊢-subst ⊢` ⊢`)}
          ⊢` (sym (subst-≡ {x} {` x} {` "x"} refl))))
  𝒞𝓁-⟦⟧ {x} {α} {.(f · m)} {.(Cod f)} {sigs.⊢· {x} {α} {m} {β} {f} w refl} = goal
    where
      open Category 𝒞𝓁
      open HomReasoning
      goal : 𝒢⟦ f ⟧ₐ ∘ (𝒢⟦ [ (x ⦂ α) ⊢ m ˸ (Dom f) ][ w ] ⟧) ≈
               𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ f · m ˸ Cod f ][ ⊢· w refl ] , refl , refl ⟩
      goal = begin
        𝒢⟦ f ⟧ₐ ∘ (𝒢⟦ [ (x ⦂ α) ⊢ m ˸ (Dom f) ][ w ] ⟧) ≈⟨ refl⟩∘⟨ 𝒞𝓁-⟦⟧ ⟩
        𝒢⟦ f ⟧ₐ ∘ 𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ (Dom f) ][ w ] , refl , refl ⟩ ≈⟨ lemma ⟩
        𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ f · m ˸ Cod f ][ ⊢· w refl ] , refl , refl ⟩ ∎
       where
        lemma : Theorem Sg Th [ x ⦂ α ⊢ (f · ` "x") [ "x" := m ] ＝ (f · m) [ x := ` x ] ˸ Cod f
                               ][ ⊢＝ ( ⊢-subst (⊢· {"x"} ⊢` refl) w) (⊢-subst (⊢· w refl) ⊢`) ]
        lemma = Th-wit-irrelevance Sg Th
           (Th-≡ Sg Th {w =  ⊢＝ ( ⊢-subst (⊢· {"x"} ⊢` refl) w) (⊢-subst (⊢· w refl) ⊢`)}
             ( ⊢-subst (⊢· {"x"} ⊢` refl) w) (sym (subst-id {x} (f · m))))

  𝒢⊨ : ∀ {eq}
     → Axiom eq
     → satisfies Sg Th 𝒞𝓁 𝒢st eq
  𝒢⊨ {[ x ⦂ α ⊢ m ＝ m' ˸ β ][ ⊢＝ w w' ]} ax = begin
    𝒢⟦ [ (x ⦂ α) ⊢ m ˸ β ][ w ] ⟧ ≈⟨ 𝒞𝓁-⟦⟧ ⟩
    𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m ˸ β ][ w ] , refl , refl ⟩ ≈⟨ lemma ⟩
    𝒞𝓁ₐ⟨ [ x ⦂ α ⊢ m' ˸ β ][ w' ] , refl , refl ⟩ ≈˘⟨ 𝒞𝓁-⟦⟧ ⟩
    𝒢⟦ [ (x ⦂ α) ⊢ m' ˸ β ][ w' ] ⟧ ∎
   where
    open Category 𝒞𝓁
    open HomReasoning
    th-lemma : Theorem Sg Th [ x ⦂ α ⊢ m' ＝ m' [ x := ` x ] ˸ β ][ ⊢＝ w' (⊢-subst w' ⊢`) ]
    th-lemma = Th-wit-irrelevance Sg Th (Th-≡ Sg Th {w =  ⊢＝ w' (⊢-subst w' ⊢` )} w' (sym (subst-id {x} m')))
    lemma : Theorem Sg Th [ x ⦂ α ⊢ m ＝ m' [ x := ` x ] ˸ β ][ ⊢＝ w (⊢-subst w' ⊢`) ]
    lemma = Th-wit-irrelevance Sg Th (Th-trans (Ax ax) th-lemma)

  𝒢 : ℳℴ𝒹ₒ 𝒞𝓁
  𝒢 = record
    { ℳℴ𝒹⟦⟧ = 𝒢st
    ; ℳℴ𝒹⊨ = 𝒢⊨
    }
```

## 2.5. Correspondence Theorem

```agda

```

## 3. Example

```agda

```
