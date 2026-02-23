{-# OPTIONS --safe #-}

module Core.SessionBase (ℓ n : _) where

open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

Label : Set
Label = Fin ℓ

Participant : Set
Participant = Fin n

data Base : Set where
  bool nat int : Base
