{-# OPTIONS --without-K --safe #-}

module Basic where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

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
