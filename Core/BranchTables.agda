{-# OPTIONS --safe #-}

module Core.BranchTables where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _≟_)
open import Data.Vec as Vec using (Vec; []; _∷_; tabulate; lookup)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

lookupB : ∀ {n} {A : Set} → Fin n → Vec (Maybe A) n → Maybe A
lookupB l bs = Vec.lookup bs l

singleton-f : ∀ {n} {A : Set} → Fin n → A → Fin n → Maybe A
singleton-f l x l' with l' ≟ l
... | yes _ = just x
... | no  _ = nothing

singleton : ∀ {n} {A : Set} → Fin n → A → Vec (Maybe A) n
singleton l x = tabulate (singleton-f l x)

singleton-same :
  ∀ {n} {A : Set} {l : Fin n} {x : A}
  → lookupB l (singleton l x) ≡ just x
singleton-same {l = l} {x = x}
  rewrite lookup∘tabulate (singleton-f l x) l
  with l ≟ l
... | yes _   = refl
... | no l≢l  = ⊥-elim (l≢l refl)

singleton-other :
  ∀ {n} {A : Set} {l l' : Fin n} {x : A}
  → l' ≢ l
  → lookupB l' (singleton l x) ≡ nothing
singleton-other {l = l} {l' = l'} {x = x} l'≢l
  rewrite lookup∘tabulate (singleton-f l x) l'
  with l' ≟ l
... | yes eq = ⊥-elim (l'≢l eq)
... | no  _  = refl

NonEmpty : ∀ {n} {A : Set} → Vec (Maybe A) n → Set
NonEmpty {n} {A} bs =
  Σ[ l ∈ Fin n ] Σ[ x ∈ A ] (lookupB l bs ≡ just x)

mapMaybe : ∀ {n} {A B : Set} → (A → B) → Vec (Maybe A) n → Vec (Maybe B) n
mapMaybe f []             = []
mapMaybe f (nothing ∷ xs) = nothing ∷ mapMaybe f xs
mapMaybe f (just x  ∷ xs) = just (f x) ∷ mapMaybe f xs
