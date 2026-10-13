{-# OPTIONS --without-K --safe #-}

module Basic.EnrichedStyle.Instance.Sets where

open import Basic.EnrichedStyle using (Category)
open import Function using (id; _∘_)
open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (refl)

Sets : (o : Level) → Category (suc o) o
Sets o = record
    { Obj = Set o
    ; _⇒_ = λ A B → A → B
    ; id = id
    ; _∘_ = λ f g → f ∘ g
    ; assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
  }

module Sets {o : Level} = Category (Sets o)
