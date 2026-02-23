{-# OPTIONS --safe #-}

module Core.BranchTables where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _≟_)
open import Data.Vec as Vec using (Vec; []; _∷_; tabulate; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

lookupB : ∀ {n} {A : Set} → Fin n → Vec (Maybe A) n → Maybe A
lookupB l bs = Vec.lookup bs l

singleton : ∀ {n} {A : Set} → Fin n → A → Vec (Maybe A) n
singleton {n} {A} l x =
  tabulate f
  where
    f : Fin n → Maybe A
    f l' with l' ≟ l
    ... | yes _ = just x
    ... | no  _ = nothing

NonEmpty : ∀ {n} {A : Set} → Vec (Maybe A) n → Set
NonEmpty {n} {A} bs =
  Σ[ l ∈ Fin n ] Σ[ x ∈ A ] (lookupB l bs ≡ just x)

mapMaybe : ∀ {n} {A B : Set} → (A → B) → Vec (Maybe A) n → Vec (Maybe B) n
mapMaybe f []             = []
mapMaybe f (nothing ∷ xs) = nothing ∷ mapMaybe f xs
mapMaybe f (just x  ∷ xs) = just (f x) ∷ mapMaybe f xs
