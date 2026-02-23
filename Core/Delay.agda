{-# OPTIONS --safe --guardedness #-}

module Core.Delay where

record ▹ (A : Set) : Set where
  coinductive
  field force : A
open ▹ public

next : ∀ {A : Set} → A → ▹ A
force (next a) = a
