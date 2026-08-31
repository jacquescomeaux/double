{-# OPTIONS --without-K --safe #-}

open import Level using (0ℓ)

module Basic.Functor.Instance.NatToSets.Bad where

open import Basic using (Functor)
open import Basic.Instance.Nat using (Nat)
open import Basic.Instance.Sets using (Sets)
open import Data.Fin using (Fin)
open import Data.Vec using (lookup)

Include : Functor Nat (Sets 0ℓ)
Include = record
    { F₀ = Fin
    ; F₁ = lookup
    ; identity = ?
    ; homomorphism = ?
    }

module Include = Functor Include
