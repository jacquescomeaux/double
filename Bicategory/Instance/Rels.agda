{-# OPTIONS --without-K --safe #-}

module Bicategory.Instance.Rels where

open import Categories.Bicategory using (Bicategory)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Data.Product using (_,_)
open import Function using (id; _∘′_)
open import Level using (Level; suc; _⊔_; Lift; lift)
open import Relation.Binary using (REL; _⇒_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

pattern lrefl = lift ≡.refl

-- The bicategory of proof-relevant relations
Rels : (o ℓ e : Level) → Bicategory (suc (o ⊔ ℓ)) (o ⊔ ℓ) (o ⊔ ℓ) (suc o)
Rels o ℓ e = record
    { enriched = record
        { Obj = Set o
        ; hom = λ A B → record
            { Obj = REL A B (o ⊔ ℓ)
            ; _⇒_ = λ R S → R ⇒ S
            ; _≈_ = λ {R S} ⇒₁ ⇒₂ → {x : A} {y : B} (xRy : R x y) → ⇒₁ xRy ≡ ⇒₂ xRy
            ; id = id
            ; _∘_ = λ S⇒T R⇒S → S⇒T ∘′ R⇒S
            ; assoc = λ _ → ≡.refl
            ; sym-assoc = λ _ → ≡.refl
            ; identityˡ = λ _ → ≡.refl
            ; identityʳ = λ _ → ≡.refl
            ; identity² = λ _ → ≡.refl
            ; equiv = record
                { refl = λ _ → ≡.refl
                ; sym = λ f≈g xRy → ≡.sym (f≈g xRy)
                ; trans = λ f≈g g≈h xRy → ≡.trans (f≈g xRy) (g≈h xRy)
                }
            ; ∘-resp-≈ = λ {f = f} {i = i} f≈h g≈i xRy → ≡.trans (≡.cong f (g≈i xRy)) (f≈h (i xRy))
            }
        ; id = λ {A} → record
            { F₀ = λ _ x y → Lift ℓ (x ≡ y)
            ; F₁ = λ _ → id
            ; identity = ≡.erefl
            ; homomorphism = ≡.erefl
            ; F-resp-≈ = λ _ → ≡.erefl
            }
        ; ⊚ = record
            { F₀ = λ (R , S) → S ; R
            ; F₁ = λ (α , β) (z , xSz , zRy) → z , β xSz , α zRy
            ; identity = ≡.erefl
            ; homomorphism = λ _ → ≡.refl
            ; F-resp-≈ = λ (≗α , ≗β) (z , xSz , zRy) → ≡.dcong₂ _,_ ≡.refl (≡.cong₂ _,_ (≗β xSz) (≗α zRy))
            }
        ; ⊚-assoc = niHelper record
            { η = λ _ (z , xTz , w , zSw , wRy) → w , (z , xTz , zSw) , wRy
            ; η⁻¹ = λ _ (w , (z , xTz , zSw) , wRy) → z , xTz , w , zSw , wRy
            ; commute = λ _ _ → ≡.refl
            ; iso = λ _ → record
                { isoˡ = λ _ → ≡.refl
                ; isoʳ = λ _ → ≡.refl
                }
            }
        ; unitˡ = niHelper record
            { η = λ { _ (_ , xSy , lrefl) → xSy }
            ; η⁻¹ = λ  _ xSy → _ , xSy , lrefl
            ; commute = λ { _ (_ , _ , lrefl) → ≡.refl }
            ; iso = λ X → record
                { isoˡ = λ { (_ , _ , lrefl) → ≡.refl }
                ; isoʳ = ≡.erefl
                }
            }
        ; unitʳ = niHelper record
            { η = λ { _ (_ , lrefl , xRy) → xRy }
            ; η⁻¹ = λ _ xRy → _ , lrefl , xRy
            ; commute = λ { _ (_ , lrefl , _) → ≡.refl }
            ; iso = λ X → record
                { isoˡ = λ { (_ , lrefl , _) → ≡.refl }
                ; isoʳ = ≡.erefl
                }
            }
        }
    ; triangle = λ { (_ , _ , _ , lrefl , _) → ≡.refl }
    ; pentagon = λ _ → ≡.refl
    }
