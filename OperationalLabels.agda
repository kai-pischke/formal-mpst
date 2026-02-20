{-# OPTIONS --safe #-}

module OperationalLabels (ℓ n : _) where

open import Data.Product using (_×_)
import SessionBase as SB

module Core = SB ℓ n
open Core public using (Label; Participant; Base; _≢_)

------------------------------------------------------------------------
-- Shared observables / labels for operational semantics
------------------------------------------------------------------------

data Observable : Set where
  obsBase  : Base → Observable
  obsLabel : Label → Observable

infix 6 _!⟨_⟩ _?⟨_⟩
data Action : Set where
  _!⟨_⟩ : Participant → Observable → Action
  _?⟨_⟩ : Participant → Observable → Action

infix 5 _∶_
data TaggedAction : Set where
  _∶_ : Participant → Action → TaggedAction

infix 5 _↝⟨_⟩_
data Interaction : Set where
  _↝⟨_⟩_ : Participant → Observable → Participant → Interaction

-- {r,s} ∩ {p,q} = ∅
DisjointEndpoints : Participant → Participant → Participant → Participant → Set
DisjointEndpoints r s p q =
  (r ≢ p) × (r ≢ q) × (s ≢ p) × (s ≢ q)
