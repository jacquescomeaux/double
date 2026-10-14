{-# OPTIONS --without-K --safe #-}
module StrictCategory where

open import Data.Product using (Σ; _×_; _,_)
open import Function using (flip)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Indexed.Heterogeneous using (IRel; IsIndexedEquivalence)

-- Strict category
record Category (o oℓ ℓ e : Level) : Set (suc (o ⊔ oℓ ⊔ ℓ ⊔ e)) where
  eta-equality
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Objₛ : Setoid o oℓ

  open Setoid Objₛ using (refl; sym; trans) renaming (Carrier to Obj; _≈_ to _≈ₒ_) public

    -- Equivalence class of A
  [_] : Obj → Set (o ⊔ oℓ)
  [_] A = Σ Obj (A ≈ₒ_)

  field
    _⇒_ : IRel {I = Obj} [_] ℓ
    _≈_ : {A₀ B₀ : Obj} → IRel {I = [ A₀ ] × [ B₀ ]} (λ (A , B) → A ⇒ B) e
    id : {A₀ : Obj} {A₁ A₂ : [ A₀ ]} → A₁ ⇒ A₂
    _∘_ : {A₀ B₀ C₀ : Obj} {A : [ A₀ ]} {B B′ : [ B₀ ]} {C : [ C₀ ]} → (B′ ⇒ C) → (A ⇒ B) → (A ⇒ C)
    assoc
        : {A₀ B₀ C₀ D₀ : Obj}
          {A : [ A₀ ]}
          {B B′ : [ B₀ ]}
          {C C′ : [ C₀ ]}
          {D : [ D₀ ]}
          {f : A ⇒ B}
          {g : B′ ⇒ C}
          {h : C′ ⇒ D}
        → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    sym-assoc
        : {A₀ B₀ C₀ D₀ : Obj}
          {A : [ A₀ ]}
          {B B′ : [ B₀ ]}
          {C C′ : [ C₀ ]}
          {D : [ D₀ ]}
          {f : A ⇒ B}
          {g : B′ ⇒ C}
          {h : C′ ⇒ D}
        → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
    identityˡ
        : {A₀ B₀ : Obj}
          {A : [ A₀ ]}
          {B₁ B₂ B₃ : [ B₀ ]}
          {f : A ⇒ B₁}
        → id {B₀} {B₂} {B₃} ∘ f ≈ f
    identityʳ
        : {A₀ B₀ : Obj}
          {A₁ A₂ A₃ : [ A₀ ]}
          {B : [ B₀ ]}
          {f : A₃ ⇒ B}
        → f ∘ id {A₀} {A₁} {A₂} ≈ f
    identity²
        : {A₀ : Obj}
          {A₁ A₂ A₃ A₄ : [ A₀ ]}
        → id {A₀} {A₃} {A₄} ∘ id {A₀} {A₁} {A₂} ≈ id {A₀} {A₁} {A₄}
    equiv : {A B : Obj} → IsIndexedEquivalence {I = [ A ] × [ B ]} (λ (A , B) → A ⇒ B) (_≈_ {A} {B})
    ∘-resp-≈
        : {A B C : Obj}
          {A₁ A₂ : [ A ]}
          {B₁ B₂ B₁′ B₂′ : [ B ]}
          {C₁ C₂ : [ C ]}
          {f : B₁′ ⇒ C₁}
          {h : B₂′ ⇒ C₂}
          {g : A₁ ⇒ B₁}
          {i : A₂ ⇒ B₂}
        → f ≈ h
        → g ≈ i
        → f ∘ g ≈ h ∘ i
    cast
        : {A A′ B B′ : Obj}
          {A₁ : [ A ]}
          {A₂ : [ A′ ]}
          {B₁ : [ B ]}
          {B₂ : [ B′ ]}
        → A ≈ₒ A′
        → B ≈ₒ B′
        → A₁ ⇒ B₁
        → A₂ ⇒ B₂

  module Equiv {A B} = IsIndexedEquivalence (equiv {A} {B})

  op : Category o oℓ ℓ e
  op = record
      { Objₛ      = Objₛ
      ; _⇒_       = flip _⇒_
      ; _≈_       = _≈_
      ; _∘_       = flip _∘_
      ; id        = id
      ; assoc     = sym-assoc
      ; sym-assoc = assoc
      ; identityˡ = identityʳ
      ; identityʳ = identityˡ
      ; identity² = identity²
      ; equiv     = record { IsIndexedEquivalence equiv }
      ; ∘-resp-≈  = flip ∘-resp-≈
      ; cast      = λ ≈A ≈B → cast ≈B ≈A
      }
