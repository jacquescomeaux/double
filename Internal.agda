{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Level using (Level; _⊔_)

module Internal {o ℓ e : Level} (C : Category o ℓ e) where

private module C = Category C

open import Categories.Diagram.Pullback C using (Pullback)
open import Categories.Morphism.Reasoning C using (cancelˡ; extendʳ; pullˡ; pushˡ; pushʳ)

-- An internal category in C
record InternalCategory : Set (o ⊔ ℓ ⊔ e) where

  open C hiding (Obj; id)

  -- Data
  field
    Obj Mor : C.Obj
    dom cod : Mor ⇒ Obj

  -- Two compatible morphisms
  field
    P₁ : Pullback dom cod

  open module P₁ = Pullback P₁ using () renaming (P to Mor×ₒMor)

  -- Three compatible morphisms
  field
    P₂ : Pullback (dom ∘ P₁.p₂) cod
    P₃ : Pullback dom (cod ∘ P₁.p₁)

  open module P₂ = Pullback P₂ using () renaming (P to [Mor×ₒMor]×ₒMor)
  open module P₃ = Pullback P₃ using () renaming (P to Mor×ₒ[Mor×ₒMor])

  -- To express associativity, we build this limit with pullbacks (arrows pointing down)
  --
  -- Mor × Mor × Mor
  --  /     |     \
  -- Mor   Mor   Mor
  --   \  c/ \  c/
  --   d\ /  d\ /
  --    Obj   Obj

  -- Operations
  field
    -- Identity morphism for every object
    id : Obj ⇒ Mor
    id-dom : dom ∘ id ≈ C.id
    id-cod : cod ∘ id ≈ C.id
    -- Composition of two compatible morphisms
    -∘- : Mor×ₒMor ⇒ Mor
    ∘-dom : dom ∘ -∘- ≈ dom ∘ P₁.p₂
    ∘-cod : cod ∘ -∘- ≈ cod ∘ P₁.p₁

  open Equiv
  open HomReasoning

  -- λ f → (id , f)
  id×ₒ- : Mor ⇒ Mor×ₒMor
  id×ₒ- = P₁.universal (cancelˡ id-dom ○ sym identityʳ)

  -- λ f → (f , id)
  -×ₒid : Mor ⇒ Mor×ₒMor
  -×ₒid = P₁.universal (identityʳ ○ sym (cancelˡ id-cod))

  private
    drop₁ : [Mor×ₒMor]×ₒMor ⇒ Mor×ₒMor
    drop₁ = P₁.universal (sym-assoc ○ P₂.commute)

  -- λ ((f , g) , h) → (f , (g , h))
  α : [Mor×ₒMor]×ₒMor ⇒ Mor×ₒ[Mor×ₒMor]
  α = P₃.universal {h₂ = drop₁} (extendʳ P₁.commute ○ pushʳ (sym P₁.p₁∘universal≈h₁))

  -- λ ((f , g) , h) → (f ∘ g , h)
  -∘-×ₒid : [Mor×ₒMor]×ₒMor ⇒ Mor×ₒMor
  -∘-×ₒid = P₁.universal (pullˡ ∘-dom ○ P₂.commute)

  -- λ (f , (g , h)) → (f , g ∘ h)
  id×ₒ-∘- : Mor×ₒ[Mor×ₒMor] ⇒ Mor×ₒMor
  id×ₒ-∘- = P₁.universal (P₃.commute ○ (pushˡ (sym ∘-cod)))

  -- Properties
  field
    identityˡ : -∘- ∘ id×ₒ- ≈ C.id
    identityʳ : -∘- ∘ -×ₒid ≈ C.id
    assoc : -∘- ∘ -∘-×ₒid ≈ -∘- ∘ id×ₒ-∘- ∘ α
