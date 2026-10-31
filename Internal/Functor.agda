
{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Categories.Category using (Category)

module Internal.Functor {o ℓ e : Level} (C : Category o ℓ e) where

import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Internal.WithPullbacks C using (InternalCategory; HasPullbacks)

module _ (pb : HasPullbacks) where

  open Category C
  open HomReasoning
  open ⇒-Reasoning C

  record InternalFunctor (D E : InternalCategory pb) : Set (ℓ ⊔ e) where

    private
      module D = InternalCategory D
      module E = InternalCategory E

    field
      F₀ : D.Obj ⇒ E.Obj
      F₁ : D.Mor ⇒ E.Mor
      F-dom : E.dom ∘ F₁ ≈ F₀ ∘ D.dom
      F-cod : E.cod ∘ F₁ ≈ F₀ ∘ D.cod

    F₁×ₒF₁ : D.Cmp.P ⇒ E.Cmp.P
    F₁×ₒF₁ = E.Cmp.universal (extendʳ F-dom ○ refl⟩∘⟨ D.Cmp.commute ○ extendʳ (Equiv.sym F-cod))

    field
      identity : F₁ ∘ D.id ≈ E.id ∘ F₀
      homomorphism : F₁ ∘ D.-∘- ≈ E.-∘- ∘ F₁×ₒF₁
