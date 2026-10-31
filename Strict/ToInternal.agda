{-# OPTIONS --without-K --safe #-}
module Strict.ToInternal where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Pullback using (Pullback)
open import Data.Product using (∃₂; _,_)
open import Function using (_⟨$⟩_; Func; _⟶ₛ_)
open import Internal.WithPullbacks using (InternalCategory)
open import Level using (Level; _⊔_)
open import Pullback.Setoids using (pullback)
open import Relation.Binary using (Rel; Setoid)
open import Strict.Category using (Category)

open Func

module _ {o ≈o ℓ e : Level} (C : Category (o ⊔ ≈o ⊔ ℓ ⊔ e) (o ⊔ ≈o ⊔ ℓ ⊔ e) ℓ e) where

  open Category C
  module Obj = Setoid Objₛ

  ∣Mor∣ : Set (o ⊔ ≈o ⊔ ℓ ⊔ e)
  ∣Mor∣ = ∃₂ _⇒_

  data _≈′_ : Rel ∣Mor∣ (o ⊔ ≈o ⊔ ℓ ⊔ e) where
    mk-≈
        : {A A′ B B′ : Obj}
          {f : A ⇒ B}
          {g : A′ ⇒ B′}
          (≈A : A Obj.≈ A′)
          (≈B : B Obj.≈ B′)
        → cast ≈A ≈B f ≈ g
        → (A , B , f) ≈′ (A′ , B′ , g)

  open ObjEquiv

  ≈-refl : {f : ∣Mor∣} → f ≈′ f
  ≈-refl {A , B , f} = mk-≈ refl refl (cast-is-id refl refl f)

  ≈-sym : {f g : ∣Mor∣} → f ≈′ g → g ≈′ f
  ≈-sym (mk-≈ ≈A ≈B f≈g) =
      mk-≈
        (sym ≈A)
        (sym ≈B)
        (Equiv.trans
          (cast-cong _ _ (Equiv.sym f≈g))
          (Equiv.trans
            (cast-cast _ _ _ _ _ _ _)
            (cast-is-id refl refl _)))

  ≈-trans : {f g h : ∣Mor∣} → f ≈′ g → g ≈′ h → f ≈′ h
  ≈-trans (mk-≈ {f = f} {g} ≈A₁ ≈B₁ f≈g) (mk-≈ ≈A₂ ≈B₂ g≈h) =
      mk-≈
        (trans ≈A₁ ≈A₂)
        (trans ≈B₁ ≈B₂)
        (Equiv.trans
          (Equiv.sym (cast-cast ≈A₁ ≈A₂ (trans ≈A₁ ≈A₂) ≈B₁ ≈B₂ (trans ≈B₁ ≈B₂) f))
          (Equiv.trans
            (cast-cong ≈A₂ ≈B₂ f≈g)
            g≈h))

  Mor : Setoid (o ⊔ ≈o ⊔ ℓ ⊔ e) (o ⊔ ≈o ⊔ ℓ ⊔ e)
  Mor = record
      { Carrier = ∣Mor∣
      ; _≈_ = _≈′_
      ; isEquivalence = record
          { refl = ≈-refl
          ; sym = ≈-sym
          ; trans = ≈-trans
          }
      }

  dom : Mor ⟶ₛ Objₛ
  dom = record
    { to = λ (A , _) → A
    ; cong = λ { (mk-≈ ≈A _ _) → ≈A }
    }

  cod : Mor ⟶ₛ Objₛ
  cod = record
    { to = λ (_ , B , _) → B
    ; cong = λ { (mk-≈ _ ≈B _) → ≈B }
    }

  id⇒ : Objₛ ⟶ₛ Mor
  id⇒ = record
    { to = λ A → (A , A , id)
    ; cong = λ ≈A → mk-≈ ≈A ≈A (cast-id ≈A)
    }

  Cmp : Pullback (Setoids (o ⊔ ≈o ⊔ ℓ ⊔ e) (o ⊔ ≈o ⊔ ℓ ⊔ e)) dom cod
  Cmp = pullback {o ⊔ ≈o ⊔ ℓ ⊔ e} dom cod

  module Cmp = Pullback Cmp

  -∘- : Cmp.P ⟶ₛ Mor
  -∘- = record
      { to = λ { ((B₂ , C , f) , (A , B₁ , g) , ≈B) → A , C , cast ≈B refl f ∘ g }
      ; cong =
          λ { {_ , _ , C≈B}
              {_ , _ , C′≈B′}
              (mk-≈ {C} {C′} {D} {D′} {f} {f′} ≈C ≈D ≈f , mk-≈ {A} {A′} {B} {B′} {g} {g′} ≈A ≈B ≈g)
            → mk-≈
                ≈A
                ≈D
                (Equiv.trans
                  (Equiv.sym (cast-∘ ≈A ≈B ≈D g (cast C≈B refl f)))
                  (∘-resp-≈
                    (Equiv.trans
                      (cast-cast C≈B ≈B (trans ≈C C′≈B′) refl ≈D ≈D f)
                      (Equiv.trans
                        (Equiv.sym (cast-cast ≈C C′≈B′ (trans ≈C C′≈B′) ≈D refl ≈D f))
                        (cast-cong C′≈B′ refl ≈f)))
                    ≈g))
            }
      }

  internalCategory : InternalCategory (Setoids (o ⊔ ≈o ⊔ ℓ ⊔ e) (o ⊔ ≈o ⊔ ℓ ⊔ e)) (pullback {o})
  internalCategory = record
      { Obj = Objₛ
      ; Mor = Mor
      ; dom = dom
      ; cod = cod
      ; id = id⇒
      ; id-dom = refl
      ; id-cod = refl
      ; -∘- = -∘-
      ; ∘-dom = refl
      ; ∘-cod = refl
      ; identityˡ = mk-≈ refl refl (Equiv.trans (cast-is-id refl refl _) (Equiv.trans (∘-resp-≈ (cast-is-id _ _ _) Equiv.refl) identityˡ))
      ; identityʳ = mk-≈ refl refl (Equiv.trans (cast-is-id refl refl _) (Equiv.trans (∘-resp-≈ (cast-is-id _ _ _) Equiv.refl) identityʳ))
      ; assoc = λ { {(((C₂ , D , f) , (B₂ , C₁ , g) , ≈C) , (A , B₁ , h) , ≈B)} →
          mk-≈
            refl
            refl
            (Equiv.trans
              (cast-is-id refl refl (cast (trans (trans refl (trans (trans refl refl) refl)) ≈B) refl (cast ≈C refl f ∘ g) ∘ h))
              (Equiv.trans
                (∘-resp-≈
                  (Equiv.trans
                    (Equiv.sym (cast-∘ (trans (trans refl (trans (trans refl refl) refl)) ≈B) refl refl g (cast ≈C refl f)))
                    (∘-resp-≈
                      (Equiv.trans
                        (cast-cast ≈C refl ≈C refl refl refl f)
                        (cast-unique
                          ≈C
                          (trans
                            (trans
                              (trans (trans refl (trans (trans ≈C refl) refl)) (trans refl refl))
                              (trans (trans refl (sym refl)) (trans refl refl)))
                            (trans (trans (sym refl) refl) (trans refl refl)))
                          refl refl f))
                      (cast-unique (trans (trans refl (trans (trans refl refl) refl)) ≈B) (trans refl ≈B) refl refl g)))
                  Equiv.refl)
                assoc)) }
      }
