{-# OPTIONS --without-K --safe #-}

module Bicategory.Instance.Basic.EnrichedStyle where

import Basic.EnrichedStyle as Basic

open import Categories.Bicategory using (Bicategory)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Instance.One using (One)
open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Enriched.Category using () renaming (Category to Enriched)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Function using () renaming (id to idf; _∘_ to _∘f_)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open Product using (Cats-Monoidal)

module _ {o ℓ : Level} where

  module _ (C D : Basic.Category o ℓ) where

    private
      module D = Basic.Category D

    hom-category : Category (o ⊔ ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
    hom-category = categoryHelper record
        { Obj = Basic.Functor C D
        ; _⇒_ = Basic.NaturalTransformation
        ; _≈_ = Basic._≃_
        ; id = Basic.id⇒
        ; _∘_ = Basic._∘ᵥ_
        ; assoc = λ _ → D.assoc
        ; identityˡ = λ _ → D.identityˡ
        ; identityʳ = λ _ → D.identityʳ
        ; equiv = Basic.≃-isEquivalence
        ; ∘-resp-≈ = λ α≗β γ≗δ x → ≡.cong₂ D._∘_ (α≗β x) (γ≗δ x)
        }

  open import Data.Product using (uncurry′; _,_)

  id : {A : Basic.Category o ℓ} → Functor (One {o ⊔ ℓ} {o ⊔ ℓ} {o ⊔ ℓ}) (hom-category A A)
  id {A} = record
      { F₀ = λ _ → Basic.Id {o} {ℓ} {A = A}
      ; F₁ = λ _ → Basic.id⇒
      ; identity = λ _ → ≡.refl
      ; homomorphism = λ _ → ≡.sym A.identityˡ
      ; F-resp-≈ = λ _ _ → ≡.refl
      }
    where
      module A = Basic.Category A
