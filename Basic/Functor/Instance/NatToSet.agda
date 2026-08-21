{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (0ℓ)

module Basic.Functor.Instance.NatToSet (funext : Extensionality 0ℓ 0ℓ) where

open import Basic using (Functor)
open import Basic.Instance.Nat using (Nat)
open import Basic.Instance.Sets using (Sets)
open import Data.Fin using (Fin)
open import Data.Vec using (lookup)
open import Data.Vec.Properties using (lookup∘tabulate; lookup-map)
open import Function using (id)

Include : Functor Nat (Sets 0ℓ)
Include = record
    { F₀ = Fin
    ; F₁ = lookup
    ; identity = funext (lookup∘tabulate id)
    ; homomorphism = λ {f = f} {g} → funext λ x → lookup-map x (lookup g) f
    }

module Include = Functor Include
