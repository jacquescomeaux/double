{-# OPTIONS --without-K --safe #-}

module Strict.Category where

open import Function using (flip)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- In a strict category, objects form a "Set".
-- This is witnessed by cast-unique which shows that the transport maps
-- do not depend on which proofs of object equality are used
record Category (o ≈o ℓ e : Level) : Set (suc (o ⊔ ≈o ⊔ ℓ ⊔ e)) where

  infix  4 _≈_ _⇒_
  infixr 9 _∘_

  field
    -- A setoid of objects instead of just a type
    Objₛ : Setoid o ≈o

  open Setoid Objₛ using () renaming (Carrier to Obj; _≈_ to _≈ₒ_) public
  open Setoid Objₛ using (isEquivalence)
  module ObjEquiv = IsEquivalence isEquivalence

  field
    -- All the ordinary fields of a category
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
    -- Transport maps between hom-sets
    cast : {A A′ B B′ : Obj} → A ≈ₒ A′ → B ≈ₒ B′ → A ⇒ B → A′ ⇒ B′
    cast-cong : {A A′ B B′ : Obj} (≈A : A ≈ₒ A′) (≈B : B ≈ₒ B′) (f g : A ⇒ B) → f ≈ g → cast ≈A ≈B f ≈ cast ≈A ≈B g
    -- Proof-irrelevance
    cast-is-id : {A B : Obj} (≈A : A ≈ₒ A) (≈B : B ≈ₒ B) (f : A ⇒ B) → cast ≈A ≈B f ≈ f
    cast-cast
        : {A A′ B B′ C C′ : Obj}
          (A≈B : A ≈ₒ B)
          (B≈C : B ≈ₒ C)
          (A≈C : A ≈ₒ C)
          (A′≈B′ : A′ ≈ₒ B′)
          (B′≈C′ : B′ ≈ₒ C′)
          (A′≈C′ : A′ ≈ₒ C′)
          (f : A ⇒ A′)
        → cast B≈C B′≈C′ (cast A≈B A′≈B′ f) ≈ cast A≈C A′≈C′ f
    -- Transport coherence
    cast-id : {A A′ : Obj} (≈A : A ≈ₒ A′) → cast ≈A ≈A id ≈ id
    cast-∘
        : {A A′ B B′ C C′ : Obj}
          (≈A : A ≈ₒ A′)
          (≈B : B ≈ₒ B′)
          (≈C : C ≈ₒ C′)
          (f : A ⇒ B)
          (g : B ⇒ C)
        → cast ≈B ≈C g ∘ cast ≈A ≈B f ≈ cast ≈A ≈C (g ∘ f)

  module Equiv {A B} = IsEquivalence (equiv {A} {B})

  cast-unique : {A A′ B B′ : Obj} (≈A ≈A′ : A ≈ₒ A′) (≈B ≈B′ : B ≈ₒ B′) (f : A ⇒ B) → cast ≈A ≈B f ≈ cast ≈A′ ≈B′ f
  cast-unique ≈A ≈A′ ≈B ≈B′ f =
      Equiv.trans
        (Equiv.sym (cast-cast ≈A′ ObjEquiv.refl ≈A ≈B′ ObjEquiv.refl ≈B f))
        (cast-is-id ObjEquiv.refl ObjEquiv.refl (cast ≈A′ ≈B′ f))

  op : Category o ≈o ℓ e
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
      ; cast-is-id = flip cast-is-id
      ; cast-cast  = λ A≈B B≈C A≈C A′≈B′ B′≈C′ A′≈C′ → cast-cast A′≈B′ B′≈C′ A′≈C′ A≈B B≈C A≈C
      ; cast-id    = cast-id
      ; cast-∘     = λ ≈A ≈B ≈C f g → cast-∘ ≈C ≈B ≈A g f
      }

private

  open Category using (op)

  op-involutive : {o ≈o ℓ e : Level} {C : Category o ≈o ℓ e} → op (op C) ≡ C
  op-involutive = ≡.refl
