{-# OPTIONS --safe #-}

module Syntax.ProcessSyntax (ℓ n : _) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Vec using (Vec)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
import Core.BranchTables as BT
import Core.SessionBase as SB

module Core = SB ℓ n
open Core public using (Label; Participant)

------------------------------------------------------------------------
-- Expressions
--
-- v = number of expression variables in scope
------------------------------------------------------------------------

infixr 6 _∨_
infixl 7 _+_
infixl 6 _⊕_
infix  4 _≤_

data Expr : ℕ → Set where
  litTrue  : ∀ {v} → Expr v
  litFalse : ∀ {v} → Expr v
  natLit   : ∀ {v} → ℕ → Expr v
  intLit   : ∀ {v} → ℤ → Expr v
  evar     : ∀ {v} → Fin v → Expr v
  _∨_      : ∀ {v} → Expr v → Expr v → Expr v
  ¬_       : ∀ {v} → Expr v → Expr v
  _+_      : ∀ {v} → Expr v → Expr v → Expr v
  _⊕_      : ∀ {v} → Expr v → Expr v → Expr v
  _≤_      : ∀ {v} → Expr v → Expr v → Expr v

Expr₀ : Set
Expr₀ = Expr 0

------------------------------------------------------------------------
-- Processes
--
-- k = number of process recursion variables in scope
-- v = number of expression variables in scope
------------------------------------------------------------------------

mutual
  -- Label-indexed branch table, sharing the global fixed label universe.
  Branches : ℕ → ℕ → Set
  Branches k v = Vec (Maybe (Process k v)) ℓ

  data Process : ℕ → ℕ → Set where
    inactive : ∀ {k v} → Process k v
    send     : ∀ {k v} → Participant → Expr v → Process k v → Process k v
    recv     : ∀ {k v} → Participant → Process k (suc v) → Process k v
    sel      : ∀ {k v} → Participant → Label → Process k v → Process k v
    bra      : ∀ {k v} → Participant → Branches k v → Process k v
    if_then_else_ : ∀ {k v} → Expr v → Process k v → Process k v → Process k v
    mu       : ∀ {k v} → Process (suc k) v → Process k v
    pvar     : ∀ {k v} → Fin k → Process k v

-- Closed processes (no free process vars and no free expression vars)
Process₀ : Set
Process₀ = Process 0 0

------------------------------------------------------------------------
-- Branch-table utilities
------------------------------------------------------------------------

lookupB : ∀ {k v} → Label → Branches k v → Maybe (Process k v)
lookupB = BT.lookupB

singletonB : ∀ {k v} → Label → Process k v → Branches k v
singletonB = BT.singleton

NonEmptyB : ∀ {k v} → Branches k v → Set
NonEmptyB = BT.NonEmpty

------------------------------------------------------------------------
-- Multiparty sessions
--
-- `SessionMap` is a sparse map (participant -> maybe process).
-- `Session` is the corresponding total map where missing entries are
-- interpreted as `inactive`.
------------------------------------------------------------------------

SessionMap : Set
SessionMap = Participant → Maybe Process₀

emptyMap : SessionMap
emptyMap _ = nothing

singletonMap : Participant → Process₀ → SessionMap
singletonMap p P q with q ≟ p
... | yes _ = just P
... | no  _ = nothing

infixr 5 _∥_
_∥_ : SessionMap → SessionMap → SessionMap
(M ∥ N) p with N p
... | just P  = just P
... | nothing = M p

Session : Set
Session = Participant → Process₀

toTotal : SessionMap → Session
toTotal M p with M p
... | just P  = P
... | nothing = inactive

-- Grammar-level session terms:
--   M ::= p : P | M | M'
data SessionExpr : Set where
  _↦_ : Participant → Process₀ → SessionExpr
  _∣_ : SessionExpr → SessionExpr → SessionExpr

evalMap : SessionExpr → SessionMap
evalMap (p ↦ P) = singletonMap p P
evalMap (M ∣ N) = evalMap M ∥ evalMap N

eval : SessionExpr → Session
eval M = toTotal (evalMap M)
