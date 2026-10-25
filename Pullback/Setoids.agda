{-# OPTIONS --without-K --safe #-}
module Pullback.Setoids where

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Pullback using (Pullback)
open import Data.Product using (Σ-syntax; _×_; _,_; map; zip; <_,_>)
open import Function using (_⟨$⟩_; Func ; _⟶ₛ_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)

open Func
open Setoid using (Carrier)

module _ {c ℓ : Level} {A B C : Setoid (c ⊔ ℓ) ℓ} (f : A ⟶ₛ C) (g : B ⟶ₛ C) where

  private
    module A = Setoid A
    module B = Setoid B
    module C = Setoid C

  P : Setoid (c ⊔ ℓ) ℓ
  P = record
      { Carrier = Σ[ x ∈ A.Carrier ] Σ[ y ∈ B.Carrier ] f ⟨$⟩ x C.≈ g ⟨$⟩ y
      ; _≈_ = λ (x , y , _) (x′ , y′ ,  _) → x A.≈ x′ × y B.≈ y′
      ; isEquivalence = record
          { refl = A.refl , B.refl
          ; sym = map A.sym B.sym
          ; trans = zip A.trans B.trans
          }
      }

  p₁ : P ⟶ₛ A
  p₁ = record
      { to = λ (x , _) → x
      ; cong = λ (≈x , _) → ≈x
      }

  p₂ : P ⟶ₛ B
  p₂ = record
      { to = λ (_ , y , _) → y
      ; cong = λ (_ , ≈y) → ≈y
      }

  universal
      : {X : Setoid (c ⊔ ℓ) ℓ}
        {h₁ : X ⟶ₛ A}
        {h₂ : X ⟶ₛ B}
      → ({x : Carrier X} → f ⟨$⟩ (h₁ ⟨$⟩ x) C.≈ g ⟨$⟩ (h₂ ⟨$⟩ x))
      → X ⟶ₛ P
  universal {X} {h₁} {h₂} eq = record
      { to = λ x → h₁ ⟨$⟩ x , h₂ ⟨$⟩ x , eq {x}
      ; cong = < cong h₁ , cong h₂ >
      }

  pullback : Pullback (Setoids (c ⊔ ℓ) ℓ) f g
  pullback = record
      { P = P
      ; p₁ = p₁
      ; p₂ = p₂
      ; isPullback = record
          { commute = λ {(_ , _ , fx≈gy)} → fx≈gy
          ; universal = λ {A h₁ h₂} → universal {A} {h₁} {h₂}
          ; p₁∘universal≈h₁ = A.refl
          ; p₂∘universal≈h₂ = B.refl
          ; unique-diagram = λ eq₁ eq₂ {x} → eq₁ {x} , eq₂ {x}
          }
      }
