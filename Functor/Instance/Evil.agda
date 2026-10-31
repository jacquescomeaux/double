{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Evil where

import Categories.Morphism as Morphism
import Categories.Morphism.IsoEquiv as IsoEquiv
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Evil.Category as EvilC
import Evil.Functor as EvilF

open import Categories.Category using (Category)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Functor using (Functor)
open import Categories.Functor.Instance.Core using (Core)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Category.Instance.EvilCats using (EvilCats)
open import Level using (Level; _⊔_)

-- Any category can be made evil by letting isomorphic objects be "equal"

module _ {o ℓ e : Level} where

  module Core = Functor (Core {o} {ℓ} {e})

  evil : Category o ℓ e → EvilC.Category o (ℓ ⊔ e) e ℓ e
  evil C = record
      { 𝕆𝕓𝕛 = Core.₀ C
      ; Category C
      ; cast = λ ≅A ≅B f → from ≅B ∘ f ∘ to ≅A
      ; cast-cong = λ ≅A ≅B f≈g → refl⟩∘⟨ f≈g ⟩∘⟨refl
      ; cast-refl = λ f → identityˡ ○ identityʳ
      ; cast-cong₂ = λ  ≈₂A ≈₂B f → from-≈ ≈₂B ⟩∘⟨ Equiv.refl ⟩∘⟨ to-≈ ≈₂A
      ; cast-trans = λ A≅B B≅C A′≅B′ B′≅C′ f → pullʳ (pushʳ sym-assoc)
      ; cast-id = λ ≅A → refl⟩∘⟨ identityˡ ○ isoʳ ≅A
      ; cast-∘ = λ ≅A ≅B ≅C f g → pullʳ (pullʳ (cancelˡ (isoˡ ≅B)) ○ sym-assoc)
      }
    where
      open Category C
      open ⇒-Reasoning C using (pullˡ; pullʳ; pushʳ; extendˡ; extendʳ; cancelˡ; cancelʳ; insertˡ; insertʳ)
      open HomReasoning
      open Morphism C using (≅-setoid; _≅_)
      open IsoEquiv C using (_≃_)
      open _≃_
      open _≅_ using (to; from; isoˡ; isoʳ)

  evil₁
      : {A B : Category o ℓ e}
      → Functor A B
      → EvilF.Functor (evil A) (evil B)
  evil₁ {_} {B} F = record
      { F-Obj = Core.₁ F
      ; Functor F
      ; F-cast = λ _ _ _ → homomorphism ○ (refl⟩∘⟨ homomorphism)
      }
    where
      open Category B
      open HomReasoning
      open Functor F

  Evil : Functor (Cats o ℓ e) (EvilCats o (ℓ ⊔ e) e ℓ e)
  Evil = record
      { F₀ = evil
      ; F₁ = evil₁
      ; identity = λ {A} → record
          { eq₀ = λ X → ≅.refl A {X}
          ; eq₁ = λ f → Equiv.trans A (identityˡ A) (identityʳ A)
          }
      ; homomorphism = λ {Z = Z} → record
          { eq₀ = λ _ → ≅.refl Z
          ; eq₁ = λ _ → Equiv.trans Z (identityˡ Z) (identityʳ Z)
          }
      ; F-resp-≈ = λ {A B} F≃G → record
          { eq₀ = λ X → FX≅GX F≃G {X}
          ; eq₁ = λ {X _} f → Equiv.trans B (extendʳ B (⇒.commute F≃G f)) (elimʳ B (iso.isoʳ F≃G X))
          }
      }
    where
      open Category
      open Morphism using (module ≅)
      open ⇒-Reasoning
      open NaturalIsomorphism using (FX≅GX; module ⇒; module iso)

  module Evil = Functor Evil
