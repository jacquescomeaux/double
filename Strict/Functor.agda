{-# OPTIONS --without-K --safe #-}

module Strict.Functor where

open import Function using (flip; _⟶ₛ_; Func; _⟨$⟩_) renaming (id to idf; _∘_ to _∘f_)
open import Function.Construct.Composition using () renaming (function to Compose)
open import Function.Construct.Identity using () renaming (function to Id)
open import Level using (Level; _⊔_)
open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Strict.Category using (Category)

open Func

module _ {o o′ ≈o ≈o′ ℓ ℓ′ e e′ : Level} where

  -- Functor between strict categories
  record Functor (C : Category o ≈o ℓ e) (D : Category o′ ≈o′ ℓ′ e′) : Set (o ⊔ ≈o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ≈o′ ⊔ ℓ′ ⊔ e′) where

    private
      module C = Category C
      module D = Category D

    open Func

    field
      -- Extensional (i.e. equality-respecting) function on object setoids
      -- instead of raw function on object types
      F₀ : C.Objₛ ⟶ₛ D.Objₛ
      -- Ordinary functor fields
      F₁ : {A B : C.Obj} (f : A C.⇒ B) → F₀ ⟨$⟩ A D.⇒ F₀ ⟨$⟩ B
      identity : {A : C.Obj} → F₁ (C.id {A}) D.≈ D.id
      homomorphism : {X Y Z : C.Obj} {f : X C.⇒ Y} {g : Y C.⇒ Z} → F₁ (g C.∘ f) D.≈ F₁ g D.∘ F₁ f
      F-resp-≈ : {A B : C.Obj} {f : A C.⇒ B} {g : A C.⇒ B} → f C.≈ g → F₁ f D.≈ F₁ g
      -- Must also respect transports
      F-cast
          : {A A′ B B′ : C.Obj}
            (≈A : A C.≈ₒ A′)
            (≈B : B C.≈ₒ B′)
            (f : A C.⇒ B)
          → F₁ (C.cast ≈A ≈B f) D.≈ D.cast (cong F₀ ≈A) (cong F₀ ≈B) (F₁ f)

    op : Functor C.op D.op
    op = record
      { F₀           = F₀
      ; F₁           = F₁
      ; identity     = identity
      ; homomorphism = homomorphism
      ; F-resp-≈     = F-resp-≈
      ; F-cast       = flip F-cast
      }

  private

    open Functor using (op)

    op-involutive
        : {C : Category o ≈o ℓ e}
          {D : Category o′ ≈o′ ℓ′ e′}
          {F : Functor C D}
        → op (op F) ≡ F
    op-involutive = ≡.refl

  module _ {C : Category o ≈o ℓ e} {D : Category o′ ≈o′ ℓ′ e′}  where

    private
      module C = Category C
      module D = Category D

    -- Extensional equality of functors between strict categories
    record _≈F_ (F G : Functor C D) : Set (ℓ ⊔ o ⊔ o′ ⊔ e′ ⊔ ≈o′ ⊔ ≈o) where

      private
        module F = Functor F
        module G = Functor G

      open F using (F₀; F₁)
      open G using () renaming (F₀ to G₀; F₁ to G₁)
      open D

      field
        eq₀ : ∀ X → F₀ ⟨$⟩ X ≈ₒ G₀ ⟨$⟩ X
        eq₁ : {X Y : C.Obj} (f : X C.⇒ Y) → cast (eq₀ X) (eq₀ Y) (F₁ f) ≈ G₁ f

    infix 4 _≈F_

    ≈F-refl : {F : Functor C D} → F ≈F F
    ≈F-refl {F} = record
        { eq₀ = λ _ → D.ObjEquiv.refl
        ; eq₁ = λ f → D.cast-is-id D.ObjEquiv.refl D.ObjEquiv.refl (Functor.F₁ F f)
        }

    ≈F-sym : {F G : Functor C D} → F ≈F G → G ≈F F
    ≈F-sym {F} {G} F≈G = record
        { eq₀ = λ X → D.ObjEquiv.sym (eq₀ X)
        ; eq₁ = λ {X Y} f →
            D.Equiv.sym
              (D.Equiv.trans
                (D.Equiv.sym
                  (D.cast-is-id
                    D.ObjEquiv.refl
                    D.ObjEquiv.refl
                    (F.F₁ f)))
                  (D.Equiv.trans
                    (D.Equiv.sym
                      (D.cast-cast
                        (eq₀ X)
                        (D.ObjEquiv.sym (eq₀ X))
                        D.ObjEquiv.refl
                        (eq₀ Y)
                        (D.ObjEquiv.sym (eq₀ Y))
                        D.ObjEquiv.refl
                        (F.F₁ f)))
                    (D.cast-cong
                      (D.ObjEquiv.sym (eq₀ X))
                      (D.ObjEquiv.sym (eq₀ Y))
                      (eq₁ f))))
        }
      where
        open _≈F_ F≈G
        module F = Functor F
        module G = Functor G

    ≈F-trans : {F G H : Functor C D} → F ≈F G → G ≈F H → F ≈F H
    ≈F-trans {F} {G} {H} F≈G G≈H = record
        { eq₀ = λ X → D.ObjEquiv.trans (F≈G.eq₀ X) (G≈H.eq₀ X)
        ; eq₁ = λ {X Y} f →
              D.Equiv.trans
                (D.Equiv.sym
                  (D.cast-cast
                    (F≈G.eq₀ X)
                    (G≈H.eq₀ X)
                    (D.ObjEquiv.trans (F≈G.eq₀ X) (G≈H.eq₀ X))
                    (F≈G.eq₀ Y)
                    (G≈H.eq₀ Y)
                    (D.ObjEquiv.trans (F≈G.eq₀ Y) (G≈H.eq₀ Y))
                    (F.F₁ f)))
                (D.Equiv.trans
                  (D.cast-cong
                    (G≈H.eq₀ X)
                    (G≈H.eq₀ Y)
                    (F≈G.eq₁ f))
                  (G≈H.eq₁ f))
        }
      where
        module F = Functor F
        module G = Functor G
        module F≈G = _≈F_ F≈G
        module G≈H = _≈F_ G≈H

    ≈F-isEquiv : IsEquivalence _≈F_
    ≈F-isEquiv = record
        { refl = ≈F-refl
        ; sym = ≈F-sym
        ; trans = ≈F-trans
        }

    ≈F-setoid : Setoid (o ⊔ o′ ⊔ ≈o ⊔ ≈o′ ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′) (o ⊔ o′ ⊔ ≈o ⊔ ≈o′ ⊔ ℓ ⊔ e′)
    ≈F-setoid = record
        { Carrier = Functor C D
        ; _≈_ = _≈F_
        ; isEquivalence = ≈F-isEquiv
        }

module _ {o ≈o ℓ e : Level} where

  -- The identity functor
  idF : {C : Category o ≈o ℓ e} → Functor C C
  idF {C} = record
      { F₀ = Id Objₛ
      ; F₁ = idf
      ; identity = Equiv.refl
      ; homomorphism = Equiv.refl
      ; F-resp-≈ = idf
      ; F-cast = λ _ _ _ → Equiv.refl
      }
    where
      open Category C

  -- Composition of functors
  _∘F_ : {A B C : Category o ≈o ℓ e} → Functor B C → Functor A B → Functor A C
  _∘F_ {A = A} {B} {C} F G = record
      { F₀ = Compose G.F₀ F.F₀
      ; F₁ = F.F₁ ∘f G.F₁
      ; identity = λ {A} → trans (F.F-resp-≈ G.identity) F.identity
      ; homomorphism = λ {X Y Z f g} → trans (F.F-resp-≈ G.homomorphism) F.homomorphism
      ; F-resp-≈ = F.F-resp-≈ ∘f G.F-resp-≈
      ; F-cast = λ ≈A ≈B f → C.Equiv.trans (F.F-resp-≈ (G.F-cast ≈A ≈B f)) (F.F-cast (cong G.F₀ ≈A) (cong G.F₀ ≈B) (G.F₁ f))
      }
    where
      module F = Functor F
      module G = Functor G
      module C = Category C
      open C.Equiv
