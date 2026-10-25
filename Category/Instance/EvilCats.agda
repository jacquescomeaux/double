{-# OPTIONS --without-K --safe #-}

module Category.Instance.EvilCats where

import Categories.Category as NonStrict

open import Evil.Category using (Category)
open import Evil.Functor using (Functor; idF; _∘F_; _≈F_; ≈F-sym; ≈F-isEquiv)
open import Function using (Func; _⟨$⟩_)
open import Level using (Level; suc; _⊔_)

∘F-assoc
    : {o oℓ ℓ e : Level}
      {A B C D : Category o oℓ ℓ e}
      {f : Functor A B}
      {g : Functor B C}
      {h : Functor C D}
    → (h ∘F g) ∘F f ≈F h ∘F (g ∘F f)
∘F-assoc {A = A} {B} {C} {D} {F} {G} {H} = record
    { eq₀ = λ _ → D.refl
    ; eq₁ = λ f → D.cast-refl (H.F₁ (G.F₁ (F.F₁ f)))
    }
  where
    module D = Category D
    module F = Functor F
    module G = Functor G
    module H = Functor H

∘F-identityˡ
    : {o oℓ ℓ e : Level}
      {A B : Category o oℓ ℓ e}
      {f : Functor A B}
    → idF ∘F f ≈F f
∘F-identityˡ {A = A} {B} {F} = record
    { eq₀ = λ _ → B.refl
    ; eq₁ = λ f → B.cast-refl (F.F₁ f)
    }
  where
    module B = Category B
    module F = Functor F

∘F-identityʳ
    : {o oℓ ℓ e : Level}
      {A B : Category o oℓ ℓ e}
      {f : Functor A B}
    → f ∘F idF ≈F f
∘F-identityʳ {A = A} {B} {F} = record
    { eq₀ = λ _ → B.refl
    ; eq₁ = λ f → B.cast-refl (F.F₁ f)
    }
  where
    module B = Category B
    module F = Functor F

open Func

∘F-resp-≈F
    : {o oℓ ℓ e : Level}
      {A B C : Category o oℓ ℓ e}
      {F H : Functor B C}
      {G I : Functor A B}
    → F ≈F H
    → G ≈F I
    → F ∘F G ≈F H ∘F I
∘F-resp-≈F {A = A} {B} {C} {F} {G} {H} {I} F≈H G≈I = record
    { eq₀ = λ X → C.trans (cong F.F₀ (G≈I.eq₀ X)) (F≈H.eq₀ (I.F₀ ⟨$⟩ X))
    ; eq₁ = λ {X Y} f →
        C.Equiv.trans
          (C.cast-trans
            (cong F.F₀ (G≈I.eq₀ X))
            (F≈H.eq₀ (I.F₀ ⟨$⟩ X))
            (cong F.F₀ (G≈I.eq₀ Y))
            (F≈H.eq₀ (I.F₀ ⟨$⟩ Y))
            (F.F₁ (H.F₁ f)))
          (C.Equiv.trans
            (C.cast-cong
              (F≈H.eq₀ (I.F₀ ⟨$⟩ X))
              (F≈H.eq₀ (I.F₀ ⟨$⟩ Y))
              (C.Equiv.trans
                (C.Equiv.sym (F.F-cast (G≈I.eq₀ X) (G≈I.eq₀ Y) (H.F₁ f)))
                (F.F-resp-≈ (G≈I.eq₁ f))))
            (F≈H.eq₁ (I.F₁ f)))
    }
  where
    module C = Category C
    module F = Functor F
    module G = Functor G
    module H = Functor H
    module I = Functor I
    module F≈H = _≈F_ F≈H
    module G≈I = _≈F_ G≈I

EvilCats : (o oℓ ℓ e : Level) → NonStrict.Category (suc (o ⊔ oℓ ⊔ ℓ ⊔ e)) (o ⊔ oℓ ⊔ ℓ ⊔ e) (o ⊔ oℓ ⊔ ℓ ⊔ e)
EvilCats o oℓ ℓ e = record
    { Obj = Category o oℓ ℓ e
    ; _⇒_ = Functor
    ; _≈_ = _≈F_
    ; id = idF
    ; _∘_ = _∘F_
    ; assoc = λ {f = f} {g} {h} → ∘F-assoc {f = f} {g} {h}
    ; sym-assoc = λ {f = f} {g} {h} → ≈F-sym (∘F-assoc {f = f} {g} {h})
    ; identityˡ = ∘F-identityˡ
    ; identityʳ = ∘F-identityʳ
    ; identity² = ∘F-identityˡ
    ; equiv = ≈F-isEquiv
    ; ∘-resp-≈ = ∘F-resp-≈F
    }
