{-# OPTIONS --without-K --safe #-}

module Basic.EnrichedStyle where

open import Function using () renaming (id to idf; _∘_ to _∘f_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

-- Enriched-style category
record Category (o ℓ : Level) : Set (suc (o ⊔ ℓ)) where
  infix  4 _⇒_
  infixr 9 _∘_
  field
    Obj : Set o
    _⇒_ : Obj → Obj → Set ℓ
    id  : {A : Obj} → A ⇒ A
    _∘_ : {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C
    assoc
        : {A B C D : Obj}
          {f : A ⇒ B}
          {g : B ⇒ C}
          {h : C ⇒ D}
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    identityˡ : {A B : Obj} {f : A ⇒ B} → id ∘ f ≡ f
    identityʳ : {A B : Obj} {f : A ⇒ B} → f ∘ id ≡ f

  record Iso {A B : Obj} (f : A ⇒ B) (g : B ⇒ A) : Set ℓ where
    field
      isôˡ : f ∘ g ≡ id
      isôʳ : g ∘ f ≡ id

  record _≅_ (A B : Obj) : Set ℓ where
    field
      from : A ⇒ B
      to : B ⇒ A
      iso : Iso from to

record Functor
    {o₁ o₂ ℓ₁ ℓ₂ : Level}
    (C : Category o₁ ℓ₁)
    (D : Category o₂ ℓ₂)
  : Set (o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂) where

  private
    module C = Category C
    module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : {X Y : C.Obj} → X C.⇒ Y → F₀ X D.⇒ F₀ Y
    identity : {X : C.Obj} → F₁ (C.id {X}) ≡ D.id {F₀ X}
    homomorphism
        : {X Y Z : C.Obj}
          {f : X C.⇒ Y}
          {g : Y C.⇒ Z}
        → F₁ (g C.∘ f) ≡ F₁ g D.∘ F₁ f

  ₀ : C.Obj → D.Obj
  ₀ = F₀

  ₁ : {X Y : C.Obj} → X C.⇒ Y → F₀ X D.⇒ F₀ Y
  ₁ = F₁

module _ {o₁ o₂ ℓ₁ ℓ₂ : Level} {C : Category o₁ ℓ₁} {D : Category o₂ ℓ₂} where

  record NaturalTransformation (F G : Functor C D) : Set (o₁ ⊔ ℓ₁ ⊔ ℓ₂) where

    private
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G

    field
      η : (X : C.Obj) → F.₀ X D.⇒ G.₀ X
      commute : {X Y : C.Obj} (f : X C.⇒ Y) → η Y D.∘ F.₁ f ≡ G.₁ f D.∘ η X

  record NaturalIsomorphism (F G : Functor C D) : Set (o₁ ⊔ ℓ₁ ⊔ ℓ₂) where

    private
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G

    field
      ⇒ : NaturalTransformation F G
      ⇐ : NaturalTransformation G F

    module ⇒ = NaturalTransformation ⇒
    module ⇐ = NaturalTransformation ⇐

    field
      iso : (X : C.Obj) → D.Iso (⇒.η X) (⇐.η X)

  module _ {F G : Functor C D} where

    infix 4 _≃_

    private
      module C = Category C
      module D = Category D

    open NaturalTransformation using (η)

    _≃_ : Rel (NaturalTransformation F G) (o₁ ⊔ ℓ₂)
    _≃_ α β = (x : C.Obj) → η α x ≡ η β x

    ≃-isEquivalence : IsEquivalence _≃_
    ≃-isEquivalence = record
      { refl  = λ {α} x → ≡.refl {x = η α x}
      ; sym   = λ α≗β x → ≡.sym (α≗β x)
      ; trans = λ α≗β β≗γ x → ≡.trans (α≗β x) (β≗γ x)
      }

  ≃-setoid : (F G : Functor C D) → Setoid (o₁ ⊔ ℓ₁ ⊔ ℓ₂) (o₁ ⊔ ℓ₂)
  ≃-setoid F G = record
    { Carrier       = NaturalTransformation F G
    ; _≈_           = _≃_
    ; isEquivalence = ≃-isEquivalence
    }

module _ {o ℓ : Level} where

  -- The identity functor
  Id : {o ℓ : Level} {A : Category o ℓ} → Functor A A
  Id = record
      { F₀ = idf
      ; F₁ = idf
      ; identity = ≡.refl
      ; homomorphism = ≡.refl
      }

  -- Composition of functors
  _∘F_ : {A B C : Category o ℓ} → Functor B C → Functor A B → Functor A C
  _∘F_ F G = record
      { F₀ = F.₀ ∘f G.₀
      ; F₁ = F.₁ ∘f G.₁
      ; identity = ≡.trans (≡.cong F.₁ G.identity) F.identity
      ; homomorphism = ≡.trans (≡.cong F.₁ G.homomorphism) F.homomorphism
      }
    where
      module F = Functor F
      module G = Functor G

  module _ {C D : Category o ℓ} where

    private
      module C = Category C
      module D = Category D

    -- The identity natural transformation
    id⇒ : {F : Functor C D} → NaturalTransformation F F
    id⇒ {F} = record
        { η = λ X → D.id {F₀ X}
        ; commute = λ f → ≡.trans D.identityˡ (≡.sym D.identityʳ)
        }
      where
        open Functor F

    -- Vertical composition of natural transformations
    _∘ᵥ_
        : {F G H : Functor C D}
        → NaturalTransformation G H
        → NaturalTransformation F G
        → NaturalTransformation F H
    _∘ᵥ_ {F} {G} {H} α β = record
        { η = λ X → α.η X D.∘ β.η X
        ; commute = commute
        }
      where
        module α = NaturalTransformation α
        module β = NaturalTransformation β
        module F = Functor F
        module G = Functor G
        module H = Functor H
        open ≡-Reasoning
        commute
            : {X Y : C.Obj} (f : X C.⇒ Y)
            → (α.η Y D.∘ β.η Y) D.∘ F.₁ f ≡ H.₁ f D.∘ α.η X D.∘ β.η X
        commute {X} {Y} f = begin
            (α.η Y D.∘ β.η Y) D.∘ F.₁ f ≡⟨ D.assoc ⟩
            α.η Y D.∘ β.η Y D.∘ F.₁ f   ≡⟨ ≡.cong (α.η Y D.∘_) (β.commute f) ⟩
            α.η Y D.∘ G.₁ f D.∘ β.η X   ≡⟨ D.assoc ⟨
            (α.η Y D.∘ G.₁ f) D.∘ β.η X ≡⟨ ≡.cong (D._∘ β.η X) (α.commute f) ⟩
            (H.₁ f D.∘ α.η X) D.∘ β.η X ≡⟨ D.assoc ⟩
            H.₁ f D.∘ α.η X D.∘ β.η X   ∎

    infixr 7 _∘ᵥ_

  -- Horizontal composition of natural transformations
  _∘ₕ_
      : {A B C : Category o ℓ}
        {F G : Functor B C}
        {H I : Functor A B}
      → NaturalTransformation F G
      → NaturalTransformation H I
      → NaturalTransformation (F ∘F H) (G ∘F I)
  _∘ₕ_ {A} {B} {C} {F} {G} {H} {I} α β = record
      { η = λ X → G.₁ (β.η X) C.∘ α.η (H.₀ X)
      ; commute = commute
      }
    where
      module A = Category A
      module B = Category B
      module C = Category C
      module F = Functor F
      module G = Functor G
      module H = Functor H
      module I = Functor I
      module α = NaturalTransformation α
      module β = NaturalTransformation β
      open ≡-Reasoning
      commute
          : {X Y : A.Obj}
            (f : X A.⇒ Y)
          → (G.₁ (β.η Y) C.∘ α.η (H.₀ Y)) C.∘ F.₁ (H.₁ f) ≡ G.₁ (I.₁ f) C.∘ G.₁ (β.η X) C.∘ α.η (H.₀ X)
      commute {X} {Y} f = begin
          (G.₁ (β.η Y) C.∘ α.η (H.₀ Y)) C.∘ F.₁ (H.₁ f) ≡⟨ C.assoc ⟩
          G.₁ (β.η Y) C.∘ (α.η (H.₀ Y) C.∘ F.₁ (H.₁ f)) ≡⟨ ≡.cong (G.₁ (β.η Y) C.∘_) (α.commute (H.₁ f)) ⟩
          G.₁ (β.η Y) C.∘ (G.₁ (H.₁ f) C.∘ α.η (H.₀ X)) ≡⟨ C.assoc ⟨
          (G.₁ (β.η Y) C.∘ G.₁ (H.₁ f)) C.∘ α.η (H.₀ X) ≡⟨ ≡.cong (C._∘ α.η (H.₀ X)) G.homomorphism ⟨
          G.₁ (β.η Y B.∘ H.₁ f) C.∘ α.η (H.₀ X)         ≡⟨ ≡.cong (C._∘ α.η (H.₀ X)) (≡.cong G.₁ (β.commute f)) ⟩
          G.₁ (I.₁ f B.∘ β.η X) C.∘ α.η (H.₀ X)         ≡⟨ ≡.cong (C._∘ α.η (H.₀ X)) G.homomorphism ⟩
          (G.₁ (I.₁ f) C.∘ G.₁ (β.η X)) C.∘ α.η (H.₀ X) ≡⟨ C.assoc ⟩
          G.₁ (I.₁ f) C.∘ G.₁ (β.η X) C.∘ α.η (H.₀ X)   ∎

  infixr 11 _∘ₕ_
