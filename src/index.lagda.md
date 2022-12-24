---
title: Unary Ty Theory
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
open import Data.Product using (Σ; _,_; Σ-syntax)

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
```

## 1.2 Proved Terms

```agda
  infix 5  _⦂_
  data Context : Set ℓ₁ where
    _⦂_ : Id → Ty → Context

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
      Ty : Ty
      wit : ctx ⊢ term ˸ Ty

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
      → (Ctx⟦ ProvedTerm.ctx t ⟧) ⇒ (⟦ ProvedTerm.Ty t ⟧ₒ)
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

```

## 2.5. Correspondence Theorem

```agda

```

## 3. Example

```agda

```
