{-# OPTIONS --without-K --safe #-}

module Basic.Instance.Nat where

open import Basic using (Category)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; tabulate; lookup; map)
open import Data.Vec.Properties using (map-id; map-cong; map-∘; lookup∘tabulate; lookup-map; tabulate-∘; tabulate∘lookup)
open import Function using (id; _∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; module ≡-Reasoning)

open ≡-Reasoning

assoc
    : {A B C D : ℕ}
      (f : Vec (Fin B) A)
      (g : Vec (Fin C) B)
      (h : Vec (Fin D) C)
    → map (lookup (map (lookup h) g)) f ≡ map (lookup h) (map (lookup g) f)
assoc f g h = begin
    map (lookup (map (lookup h) g)) f ≡⟨ map-cong (λ x → lookup-map x (lookup h) g) f ⟩
    map (lookup h ∘ lookup g) f       ≡⟨ map-∘ (lookup h) (lookup g) f ⟩
    map (lookup h) (map (lookup g) f) ∎

module _ {A B : ℕ} {f : Vec (Fin B) A} where

  identityˡ : map (lookup (tabulate id)) f ≡ f
  identityˡ = begin
      map (lookup (tabulate id)) f  ≡⟨ map-cong (lookup∘tabulate id) f ⟩
      map id f                      ≡⟨ map-id f ⟩
      f                             ∎

  identityʳ : map (lookup f) (tabulate id) ≡ f
  identityʳ = begin
      map (lookup f) (tabulate id)  ≡⟨ tabulate-∘ (lookup f) id ⟨
      tabulate (lookup f)           ≡⟨ tabulate∘lookup f ⟩
      f                             ∎

Nat : Category 0ℓ 0ℓ
Nat = record
    { Obj = ℕ
    ; _⇒_ = λ n m → Vec (Fin m) n
    ; id = tabulate id
    ; _∘_ = λ f g → map (lookup f) g
    ; assoc = λ {f = f} {g h} → assoc f g h
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    }

module Nat = Category Nat
