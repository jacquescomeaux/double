{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Level using (0ℓ)

module Basic.EnrichedStyle.Functor.Instance.NatToSets.Bad where

open import Basic.EnrichedStyle using (Functor)
open import Basic.EnrichedStyle.Instance.Nat using (Nat)
open import Basic.EnrichedStyle.Instance.Sets using (Sets)
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
