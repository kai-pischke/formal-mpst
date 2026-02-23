{-# OPTIONS --safe --guardedness #-}

module AssociationExistence (ℓ n : _) where

open import Data.Product using (Σ)
import MergeProjection as MP
import LocalSemanticProperties as LSP

module M = MP ℓ n
module S = LSP ℓ n

open M public using
  ( Global₀
  ; _⊑_
  )

open S public using
  ( safe
  ; liveContext
  )

safe-live⇒associated-global :
  ∀ {Δ₀}
  → safe Δ₀
  → liveContext Δ₀
  → Σ Global₀ (λ G → Δ₀ ⊑ G)
safe-live⇒associated-global sΔ liveΔ = {!!}
