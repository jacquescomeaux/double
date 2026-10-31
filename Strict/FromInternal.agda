{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Strict.FromInternal {c ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category.Instance.Setoids using (Setoids)
open import Data.Product using (_,_)
open import Function using (_⟨$⟩_; Func)
open import Internal.WithPullbacks using (InternalCategory)
open import Relation.Binary using (Rel; Setoid)
open import Pullback.Setoids using (pullback)
open import Strict.Category using (Category)

open Func

module _ (C : InternalCategory (Setoids (c ⊔ ℓ) ℓ) (pullback {c ⊔ ℓ})) where

  open InternalCategory C

  module Obj = Setoid Obj
  module Mor = Setoid Mor
  open Setoid using (Carrier)

  infix  4 _⇒_

  record _⇒_ (x y : Obj.Carrier) : Set (c ⊔ ℓ) where
    constructor morphism
    field
      f : Mor.Carrier
      ≈dom : dom ⟨$⟩ f Obj.≈ x
      ≈cod : cod ⟨$⟩ f Obj.≈ y

  _≈_ : {A B : Obj.Carrier} → Rel (A ⇒ B) ℓ
  _≈_ {A} {B} (morphism f _ _) (morphism g _ _) = f Mor.≈ g

  _∘_ : {X Y Z : Obj.Carrier} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
  _∘_ {X} {Y} {Z} (morphism f f-dom f-cod) (morphism g g-dom g-cod) = morphism f∘g dom-f∘g cod-f∘g
    where
      elem : Carrier Cmp.P
      elem = f , g , Obj.trans f-dom (Obj.sym g-cod)
      f∘g : Mor.Carrier
      f∘g = -∘- ⟨$⟩ elem
      open ≈-Reasoning Obj
      dom-f∘g : dom ⟨$⟩ f∘g Obj.≈ X
      dom-f∘g = begin
          dom ⟨$⟩ f∘g ≈⟨ ∘-dom ⟩
          dom ⟨$⟩ g   ≈⟨ g-dom ⟩
          X           ∎
      cod-f∘g : cod ⟨$⟩ f∘g Obj.≈ Z
      cod-f∘g = begin
          cod ⟨$⟩ f∘g ≈⟨ ∘-cod ⟩
          cod ⟨$⟩ f   ≈⟨ f-cod ⟩
          Z           ∎

  category : Category (c ⊔ ℓ) ℓ (c ⊔ ℓ) ℓ
  category = record
      { Objₛ = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = _≈_
      ; id = λ {A} → morphism (id ⟨$⟩ A) id-dom id-cod
      ; _∘_ = _∘_
      ; assoc =
          λ { {f = morphism f f-dom f-cod}
              {morphism g g-dom g-cod}
              {morphism h h-dom h-cod}
            → Mor.trans
                (cong -∘- (cong -∘- (Mor.refl , Mor.refl) , Mor.refl))
                (Mor.trans
                  (assoc {(h , g , Obj.trans h-dom (Obj.sym g-cod)) , f , Obj.trans g-dom (Obj.sym f-cod)})
                  (cong -∘- (Mor.refl , cong -∘- (Mor.refl , Mor.refl))))
            }
      ; sym-assoc =
          λ { {f = morphism f f-dom f-cod}
              {morphism g g-dom g-cod}
              {morphism h h-dom h-cod}
            → Mor.sym
                (Mor.trans
                  (cong -∘- (cong -∘- (Mor.refl , Mor.refl) , Mor.refl))
                  (Mor.trans
                    (assoc {(h , g , Obj.trans h-dom (Obj.sym g-cod)) , f , Obj.trans g-dom (Obj.sym f-cod)})
                    (cong -∘- (Mor.refl , cong -∘- (Mor.refl , Mor.refl)))))
            }
      ; identityˡ = λ { {f = morphism _ _ f-cod} → Mor.trans (cong -∘- (cong id (Obj.sym f-cod) , Mor.refl)) identityˡ }
      ; identityʳ = λ { {f = morphism _ f-dom _} → Mor.trans (cong -∘- (Mor.refl , cong id (Obj.sym f-dom))) identityʳ }
      ; identity² = λ {A} → Mor.trans (cong -∘- (cong id (Obj.sym id-cod) , Mor.refl)) (identityˡ {id ⟨$⟩ A})
      ; equiv = record
          { refl = Mor.refl
          ; sym = Mor.sym
          ; trans = Mor.trans
          }
      ; ∘-resp-≈ = λ ≈f ≈g → cong -∘- (≈f , ≈g)
      ; cast = λ { ≈A ≈B (morphism f f-dom f-cod) → morphism f (Obj.trans f-dom ≈A) (Obj.trans f-cod ≈B) }
      ; cast-cong = λ _ _ x → x
      ; cast-is-id = λ _ _ _ → Mor.refl
      ; cast-cast = λ _ _ _ _ _ _ _ → Mor.refl
      ; cast-id = cong id
      ; cast-∘ = λ ≈A ≈B ≈C ≈D g → cong -∘- (Mor.refl , Mor.refl)
      }

open import Internal.Functor using (InternalFunctor)
open import Strict.Functor using (Functor)

module _
    {C D : InternalCategory (Setoids (c ⊔ ℓ) ℓ) (pullback {c ⊔ ℓ})}
    (F : InternalFunctor (Setoids (c ⊔ ℓ) ℓ) (pullback {c ⊔ ℓ}) C D)
    where

  private
    module C = InternalCategory C
    module D = InternalCategory D

  module DObj = Setoid D.Obj
  module DMor = Setoid D.Mor

  open InternalFunctor F

  functor : Functor (category C) (category D)
  functor = record
      { F₀ = F₀
      ; F₁ = λ (morphism f f-dom f-cod) →
          morphism
            (F₁ ⟨$⟩ f)
            (DObj.trans F-dom (cong F₀ f-dom))
            (DObj.trans F-cod (cong F₀ f-cod))
      ; identity = identity
      ; homomorphism = DMor.trans homomorphism (cong D.-∘- (DMor.refl , DMor.refl))
      ; F-resp-≈ = cong F₁
      ; F-cast = λ _ _ _ → DMor.refl
      }
