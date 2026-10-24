{-# OPTIONS --without-K --safe #-}
module Evil.Category where

open import Function using (flip)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

-- Ordinarily, we'd like to do as much category theory as possible
-- without ever referring to equality of objects.
-- As such, this type of category is "evil" since it lets us do exactly that.
-- However, objects don't necessarily form a "Set": for objects A B, different witnesses of A ≈ B
-- can induce meaningfully distinct tranports between hom-sets
record Category (o oℓ ℓ e : Level) : Set (suc (o ⊔ oℓ ⊔ ℓ ⊔ e)) where
  eta-equality
  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    Objₛ : Setoid o oℓ

  open Setoid Objₛ using (refl; sym; trans) renaming (Carrier to Obj; _≈_ to _≈ₒ_) public

  field
    _⇒_ : Rel Obj ℓ
    _≈_ : {A B : Obj} → Rel (A ⇒ B) e
    id  : {A : Obj} → A ⇒ A
    _∘_ : {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C
    assoc : {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    sym-assoc : {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
    identityˡ : {A B : Obj} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : {A B : Obj} {f : A ⇒ B} → f ∘ id ≈ f
    identity² : {A : Obj} → id {A} ∘ id ≈ id
    equiv : {A B : Obj} → IsEquivalence (_≈_ {A} {B})
    ∘-resp-≈ : {A B C : Obj} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
    cast : {A A′ B B′ : Obj} → A ≈ₒ A′ → B ≈ₒ B′ → A ⇒ B → A′ ⇒ B′
    cast-cong : {A A′ B B′ : Obj} (≈A : A ≈ₒ A′) (≈B : B ≈ₒ B′) (f g : A ⇒ B) → f ≈ g → cast ≈A ≈B f ≈ cast ≈A ≈B g
    cast-refl : {A B : Obj} (f : A ⇒ B) → cast refl refl f ≈ f
    cast-symˡ : {A A′ B B′ : Obj} (≈A : A ≈ₒ A′) (≈B : B ≈ₒ B′) (f : A ⇒ B) → cast (sym ≈A) (sym ≈B) (cast ≈A ≈B f) ≈ f
    cast-symʳ : {A A′ B B′ : Obj} (≈A : A ≈ₒ A′) (≈B : B ≈ₒ B′) (f : A′ ⇒ B′) → cast ≈A ≈B (cast (sym ≈A) (sym ≈B) f) ≈ f
    cast-trans
        : {A A′ B B′ C C′ : Obj}
          (A≈B : A ≈ₒ B)
          (B≈C : B ≈ₒ C)
          (A′≈B′ : A′ ≈ₒ B′)
          (B′≈C′ : B′ ≈ₒ C′)
          (f : A ⇒ A′)
        → cast (trans A≈B B≈C) (trans A′≈B′ B′≈C′) f ≈ cast B≈C B′≈C′ (cast A≈B A′≈B′ f)
    cast-id : {A B : Obj} (≈A : A ≈ₒ B) → cast ≈A ≈A id ≈ id
    cast-∘
        : {A A′ B B′ C C′ : Obj}
          (≈A : A ≈ₒ A′)
          (≈B : B ≈ₒ B′)
          (≈C : C ≈ₒ C′)
          (f : A ⇒ B)
          (g : B ⇒ C)
        → cast ≈B ≈C g ∘ cast ≈A ≈B f ≈ cast ≈A ≈C (g ∘ f)

  module Equiv {A B} = IsEquivalence (equiv {A} {B})

  op : Category o oℓ ℓ e
  op = record
      { Objₛ       = Objₛ
      ; _⇒_        = flip _⇒_
      ; _≈_        = λ {A B} → _≈_ {B} {A}
      ; _∘_        = flip _∘_
      ; id         = id
      ; assoc      = sym-assoc
      ; sym-assoc  = assoc
      ; identityˡ  = identityʳ
      ; identityʳ  = identityˡ
      ; identity²  = identity²
      ; equiv      = equiv
      ; ∘-resp-≈   = flip ∘-resp-≈
      ; cast       = flip cast
      ; cast-cong  = flip cast-cong
      ; cast-refl  = cast-refl
      ; cast-id    = cast-id
      ; cast-symˡ  = flip cast-symˡ
      ; cast-symʳ  = flip cast-symʳ
      ; cast-∘     = λ ≈A ≈B ≈C f g → cast-∘ ≈C ≈B ≈A g f
      ; cast-trans = λ A≈B B≈C A′≈B′ B′≈C′ → cast-trans A′≈B′ B′≈C′ A≈B B≈C
      }
