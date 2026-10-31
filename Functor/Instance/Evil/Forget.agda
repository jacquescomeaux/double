{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Evil.Forget where

import Evil.Category as EvilC
import Evil.Functor as EvilF

import Categories.Morphism.Properties as ⇒-Properties
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category using (Category)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; module ≃; niHelper)
open import Category.Instance.EvilCats using (EvilCats)
open import Level using (Level; _⊔_)

open EvilF using (_≈F_)

-- Forget a category's evilness

module _ {o oℓ oe ℓ e : Level} where

  forget : EvilC.Category o oℓ oe ℓ e → Category o ℓ e
  forget C = record { EvilC.Category C }

  forget₁
      : {A B : EvilC.Category o oℓ oe ℓ e}
      → EvilF.Functor A B
      → Functor (forget A) (forget B)
  forget₁ F = record { EvilF.Functor F }

  forget-∘
      : {X Y Z : EvilC.Category o oℓ oe ℓ e}
        (F : EvilF.Functor X Y)
        (G : EvilF.Functor Y Z)
      → forget₁ (G EvilF.∘F F) ≃ forget₁ G ∘F forget₁ F
  forget-∘ {X} {Y} {Z} F G = niHelper record
      { η = λ _ → id
      ; η⁻¹ = λ _ → id
      ; commute = λ _ → id-comm-sym
      ; iso = λ X → id-iso {G.F₀ (F.F₀ X)}
      }
    where
      module F = EvilF.Functor F
      module G = EvilF.Functor G
      open EvilC.Category Z
      open ⇒-Properties (forget Z) using (id-iso)
      open ⇒-Reasoning (forget Z) using (id-comm-sym)

  forget-resp-≈F
      : {A B : EvilC.Category o oℓ oe ℓ e}
        {F G : EvilF.Functor A B}
      → F ≈F G
      → forget₁ F ≃ forget₁ G
  forget-resp-≈F {A} {B} {F} {G} F≈G = niHelper record
      { η = λ X → cast refl (eq₀ X) id
      ; η⁻¹ = λ X → cast (eq₀ X) refl id
      ; commute = λ {X Y} f →
          Equiv.trans
            (Equiv.trans
              (Equiv.trans
                (Equiv.trans
                  (∘-resp-≈ Equiv.refl (Equiv.sym (cast-refl (F.F₁ f))))
                  (Equiv.trans
                    (cast-∘ refl refl (eq₀ Y) (F.F₁ f) id)
                    (cast-cong refl (eq₀ Y) identityˡ)))
                (cast-cong refl (eq₀ Y) (Equiv.sym identityʳ)))
              (Equiv.sym (cast-∘ refl (eq₀ X) (eq₀ Y) id (F.F₁ f)))) (∘-resp-≈ (eq₁ f) Equiv.refl)
      ; iso = λ X → record
          { isoˡ = Equiv.trans (cast-∘ refl (eq₀ X) refl id id) (Equiv.trans (cast-refl (id ∘ id)) identity²)
          ; isoʳ =
              Equiv.trans
                (cast-∘ (eq₀ X) refl (eq₀ X) id id)
                (Equiv.trans
                  (cast-cong (eq₀ X) (eq₀ X) identity²)
                  (Equiv.trans
                    (cast-cong (eq₀ X) (eq₀ X) (Equiv.sym F.identity))
                    (Equiv.trans (eq₁ A.id) G.identity)))
          }
      }
    where
      module A = EvilC.Category A
      open EvilC.Category B
      module G = EvilF.Functor G
      module F = EvilF.Functor F
      open _≈F_ F≈G

  Forget : Functor (EvilCats o oℓ oe ℓ e) (Cats o ℓ e)
  Forget = record
      { F₀ = forget
      ; F₁ = forget₁
      ; identity = ≃.refl
      ; homomorphism = λ {f = F} {G} → forget-∘ F G
      ; F-resp-≈ = forget-resp-≈F
      }

  module Forget = Functor Forget
