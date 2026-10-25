{-# OPTIONS --without-K --safe #-}
module Pullback.StrictCats where

open import Categories.Diagram.Pullback using (Pullback)
open import Category.Instance.StrictCats using (StrictCats)
open import Data.Product using (Σ-syntax; _×_; _,_; zip; <_,_>; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-isEquivalence)
open import Function using (_⟨$⟩_; Func) renaming (_∘_ to _∘f_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Strict.Category using (Category)
open import Strict.Functor using (Functor; _≈F_; _∘F_)

-- Pullback of strict categories

open Func

module _ {o ≈o ℓ e : Level} {A B C : Category (o ⊔ ≈o) ≈o (ℓ ⊔ e) e} (F : Functor A C) (G : Functor B C) where

  private
    module A = Category A
    module B = Category B
    module C = Category C
    module F = Functor F
    module G = Functor G

  open C hiding (Obj; Objₛ; _≈_; _⇒_)

  Obj : Set (o ⊔ ≈o)
  Obj = Σ[ X ∈ A.Obj ] Σ[ Y ∈ B.Obj ] F.F₀ ⟨$⟩ X C.≈ₒ G.F₀ ⟨$⟩ Y

  _≈_ : Rel Obj ≈o
  _≈_ (A , B , _) (A′ , B′ , _) = A A.≈ₒ A′ × B B.≈ₒ B′

  ≈-equiv : IsEquivalence _≈_
  ≈-equiv = record { IsEquivalence (×-isEquivalence A.obj-equiv B.obj-equiv) }

  Objₛ : Setoid (o ⊔ ≈o) ≈o
  Objₛ = record
      { Carrier = Obj
      ; _≈_ = _≈_
      ; isEquivalence = ≈-equiv
      }

  _⇒_ : Rel Obj (ℓ ⊔ e)
  _⇒_ (X , Y , ≈Y) (X′ , Y′ , ≈Y′) =
      Σ[ f ∈ X A.⇒ X′ ]
      Σ[ g ∈ Y B.⇒ Y′ ]
      cast ≈Y ≈Y′ (F.F₁ f) C.≈ G.F₁ g

  P : Category (o ⊔ ≈o) ≈o (ℓ ⊔ e) e
  P = record
      { Objₛ = Objₛ
      ; _⇒_ = _⇒_
      ; _≈_ = λ (f , g , _) (f′ , g′ , _) → f A.≈ f′ × g B.≈ g′
      ; id = A.id , B.id , Equiv.trans (cast-cong _ _ F.identity) (Equiv.trans (cast-id _) (Equiv.sym G.identity))
      ; _∘_ = λ { {B = _ , _ , ≈B} (f , g , α) (f′ , g′ , α′)
          → f A.∘ f′
          , g B.∘ g′
          , Equiv.trans
              (cast-cong _ _ F.homomorphism)
              (Equiv.trans
                (Equiv.sym (cast-∘ _ ≈B _ (F.F₁ f′) (F.F₁ f)))
                (Equiv.trans
                  (∘-resp-≈ α α′)
                  (Equiv.sym G.homomorphism))) }
      ; assoc = A.assoc , B.assoc
      ; sym-assoc = A.sym-assoc , B.sym-assoc
      ; identityˡ = A.identityˡ , B.identityˡ
      ; identityʳ = A.identityʳ , B.identityʳ
      ; identity² = A.identity² , B.identity²
      ; equiv = record { IsEquivalence (×-isEquivalence A.equiv B.equiv) }
      ; ∘-resp-≈ = zip A.∘-resp-≈ B.∘-resp-≈
      ; cast = λ { {A , A′ , ≈A} {B , B′ , ≈B} {C , C′ , ≈C} {D , D′ , ≈D} (A≈B , A≈B′) (C≈D , C≈D′) (f , f′ , α)
          → A.cast A≈B C≈D f
          , B.cast A≈B′ C≈D′ f′
          , Equiv.trans
              (cast-cong ≈B ≈D (F.F-cast A≈B C≈D f))
              (Equiv.trans
                (cast-cast
                  (cong F.F₀ A≈B)
                  ≈B
                  (ObjEquiv.trans ≈A (cong G.F₀ A≈B′))
                  (cong F.F₀ C≈D)
                  ≈D
                  (ObjEquiv.trans ≈C (cong G.F₀ C≈D′))
                  (F.F₁ f))
                (Equiv.trans
                  (Equiv.sym
                    (cast-cast
                      ≈A
                      (cong G.F₀ A≈B′)
                      (ObjEquiv.trans ≈A (cong G.F₀ A≈B′))
                      ≈C
                      (cong G.F₀ C≈D′)
                      (ObjEquiv.trans ≈C (cong G.F₀ C≈D′))
                      (F.F₁ f)))
                  (Equiv.trans
                    (cast-cong (cong G.F₀ A≈B′) (cong G.F₀ C≈D′) α)
                    (Equiv.sym (G.F-cast A≈B′ C≈D′ f′))))) }
      ; cast-cong = λ (≈A , ≈A′) (≈B , ≈B′) (≈f , ≈f′) → A.cast-cong ≈A ≈B ≈f , B.cast-cong ≈A′ ≈B′ ≈f′
      ; cast-is-id = λ (≈A , ≈A′) (≈B , ≈B′) (f , f′ , α) → A.cast-is-id ≈A ≈B f , B.cast-is-id ≈A′ ≈B′ f′
      ; cast-cast = λ (A , A′) (B , B′) (C , C′) (D , D′) (E , E′) (F , F′) (f , g , _)
          → A.cast-cast A B C D E F f
          , B.cast-cast A′ B′ C′ D′ E′ F′ g
      ; cast-id = λ (≈A , ≈B) → A.cast-id ≈A , B.cast-id ≈B
      ; cast-∘ = λ (≈A , ≈A′) (≈B , ≈B′) (≈C , ≈C′) (f , f′ , _) (g , g′ , _)
          → A.cast-∘ ≈A ≈B ≈C f g
          , B.cast-∘ ≈A′ ≈B′ ≈C′ f′ g′
      }

  p₁ : Functor P A
  p₁ = record
      { F₀ = record { cong = proj₁ }
      ; F₁ = proj₁
      ; identity = A.Equiv.refl
      ; homomorphism = A.Equiv.refl
      ; F-resp-≈ = proj₁
      ; F-cast = λ _ _ _ → A.Equiv.refl
      }

  p₂ : Functor P B
  p₂ = record
      { F₀ = record { cong = proj₂ }
      ; F₁ = proj₁ ∘f proj₂
      ; identity = B.Equiv.refl
      ; homomorphism = B.Equiv.refl
      ; F-resp-≈ = proj₂
      ; F-cast = λ _ _ _ → B.Equiv.refl
      }

  commute : F ∘F p₁ ≈F G ∘F p₂
  commute = record
      { eq₀ = λ (X , Y , eq) → eq
      ; eq₁ = λ (f , g , α) → α
      }

  universal
      : {X : Category (o ⊔ ≈o) ≈o (ℓ ⊔ e) e}
        {H₁ : Functor X A}
        {H₂ : Functor X B}
      → F ∘F H₁ ≈F G ∘F H₂
      → Functor X P
  universal {X} {H₁} {H₂} α = record
      { F₀ = record
          { to = λ x → H₁.F₀ ⟨$⟩ x , H₂.F₀ ⟨$⟩ x , α.eq₀ x
          ; cong = λ ≈x → cong H₁.F₀ ≈x , cong H₂.F₀ ≈x
          }
      ; F₁ = λ f → H₁.F₁ f , H₂.F₁ f , α.eq₁ f
      ; identity = H₁.identity , H₂.identity
      ; homomorphism = H₁.homomorphism , H₂.homomorphism
      ; F-resp-≈ = < H₁.F-resp-≈ , H₂.F-resp-≈ >
      ; F-cast = λ ≈A ≈B → < H₁.F-cast ≈A ≈B , H₂.F-cast ≈A ≈B >
      }
    where
      module H₁ = Functor H₁
      module H₂ = Functor H₂
      module α = _≈F_ α

  pullback : Pullback (StrictCats (o ⊔ ≈o) ≈o (ℓ ⊔ e) e) F G
  pullback = record
      { P = P
      ; p₁ = p₁
      ; p₂ = p₂
      ; isPullback = record
          { commute = commute
          ; universal = universal
          ; p₁∘universal≈h₁ = λ {h₁ = H₁} → record
              { eq₀ = λ _ → A.ObjEquiv.refl
              ; eq₁ = λ f → A.cast-is-id A.ObjEquiv.refl A.ObjEquiv.refl (F₁ H₁ f)
              }
          ; p₂∘universal≈h₂ = λ {h₂ = H₂} → record
              { eq₀ = λ _ → B.ObjEquiv.refl
              ; eq₁ = λ f → B.cast-is-id B.ObjEquiv.refl B.ObjEquiv.refl (F₁ H₂ f)
              }
          ; unique-diagram = λ ≈F-p₁ ≈F-p₂ → record
              { eq₀ = < eq₀ ≈F-p₁ , eq₀ ≈F-p₂ >
              ; eq₁ = < eq₁ ≈F-p₁ , eq₁ ≈F-p₂ >
              }
          }
      }
    where
      open Functor
      open _≈F_
