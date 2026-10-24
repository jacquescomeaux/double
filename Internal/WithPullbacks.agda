{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Level using (Level; _⊔_)

module Internal.WithPullbacks {o ℓ e : Level} (C : Category o ℓ e) where

private module C = Category C

import Internal C as WithoutPullbacks

open import Categories.Diagram.Pullback C using (Pullback)
open import Categories.Morphism.Reasoning C using (cancelˡ; extendʳ; pullˡ; pushˡ; pushʳ)

open C hiding (Obj; id)

-- If C has pullbacks, we can simplify the construction of an internal category
HasPullbacks : Set (o ⊔ ℓ ⊔ e)
HasPullbacks = {A B C : C.Obj} (f : A ⇒ C) (g : B ⇒ C) → Pullback f g

-- An internal category in a C with pullbacks
record InternalCategory (pullback : HasPullbacks) : Set (o ⊔ ℓ ⊔ e) where

  open C hiding (Obj; id)

  field
    Obj Mor : C.Obj
    dom cod : Mor ⇒ Obj

  Cmp : Pullback dom cod
  Cmp = pullback dom cod
  open module Cmp = Pullback Cmp using () renaming (P to Mor×ₒMor)

  Assocˡ : Pullback (dom ∘ Cmp.p₂) cod
  Assocˡ = pullback (dom ∘ Cmp.p₂) cod
  open module Assocˡ = Pullback Assocˡ using () renaming (P to [Mor×ₒMor]×ₒMor)

  Assocʳ : Pullback dom (cod ∘ Cmp.p₁)
  Assocʳ = pullback dom (cod ∘ Cmp.p₁)
  open module Assocʳ = Pullback Assocʳ using () renaming (P to Mor×ₒ[Mor×ₒMor])

  field
    id : Obj ⇒ Mor
    id-dom : dom ∘ id ≈ C.id
    id-cod : cod ∘ id ≈ C.id
    -∘- : Mor×ₒMor ⇒ Mor
    ∘-dom : dom ∘ -∘- ≈ dom ∘ Cmp.p₂
    ∘-cod : cod ∘ -∘- ≈ cod ∘ Cmp.p₁

  open Equiv
  open HomReasoning

  id×ₒ- : Mor ⇒ Mor×ₒMor
  id×ₒ- = Cmp.universal (cancelˡ id-dom ○ sym identityʳ)

  -×ₒid : Mor ⇒ Mor×ₒMor
  -×ₒid = Cmp.universal (identityʳ ○ sym (cancelˡ id-cod))

  private
    drop₁ : [Mor×ₒMor]×ₒMor ⇒ Mor×ₒMor
    drop₁ = Cmp.universal (sym-assoc ○ Assocˡ.commute)

  α : [Mor×ₒMor]×ₒMor ⇒ Mor×ₒ[Mor×ₒMor]
  α = Assocʳ.universal {h₂ = drop₁} (extendʳ Cmp.commute ○ pushʳ (sym Cmp.p₁∘universal≈h₁))

  -∘-×ₒid : [Mor×ₒMor]×ₒMor ⇒ Mor×ₒMor
  -∘-×ₒid = Cmp.universal (pullˡ ∘-dom ○ Assocˡ.commute)

  id×ₒ-∘- : Mor×ₒ[Mor×ₒMor] ⇒ Mor×ₒMor
  id×ₒ-∘- = Cmp.universal (Assocʳ.commute ○ (pushˡ (sym ∘-cod)))

  field
    identityˡ : -∘- ∘ id×ₒ- ≈ C.id
    identityʳ : -∘- ∘ -×ₒid ≈ C.id
    assoc : -∘- ∘ -∘-×ₒid ≈ -∘- ∘ id×ₒ-∘- ∘ α

internalCategoryHelper : (pb : HasPullbacks) → InternalCategory pb → WithoutPullbacks.InternalCategory
internalCategoryHelper pb C = record { InternalCategory C}
