{-# OPTIONS --safe #-}

module Syntax.GlobalSessionTypes (ℓ n : _) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Core.BranchTables as BT
import Core.SessionBase as SB

module Core = SB ℓ n
open Core public using (Label; Participant; Base; _≢_)

------------------------------------------------------------------------
-- Global session types with μ + de Bruijn recursion vars
--
-- k = number of recursion variables in scope
------------------------------------------------------------------------

mutual
  -- A finite branch table over the shared global label universe.
  Branches : ℕ → Set
  Branches k = Vec (Maybe (Global k)) ℓ

  data Global : ℕ → Set where
    end    : ∀ {k} → Global k

    -- point-to-point payload action: p -> q : <B>; G'
    msg    : ∀ {k} → Participant → Participant → Base → Global k → Global k

    -- labelled branching: p -> q : { l_i : G_i }_{i in I}
    choice : ∀ {k} → Participant → Participant → Branches k → Global k

    -- guarded recursion binder and recursion variable
    mu     : ∀ {k} → Global (suc k) → Global k
    var    : ∀ {k} → Fin k → Global k

-- Closed global types (no free recursion vars)
Global₀ : Set
Global₀ = Global 0

------------------------------------------------------------------------
-- Branch-table utilities
------------------------------------------------------------------------

lookupB : ∀ {k} → Label → Branches k → Maybe (Global k)
lookupB = BT.lookupB

singleton : ∀ {k} → Label → Global k → Branches k
singleton = BT.singleton

NonEmpty : ∀ {k} → Branches k → Set
NonEmpty = BT.NonEmpty

------------------------------------------------------------------------
-- Renaming / substitution for recursion variables (de Bruijn)
------------------------------------------------------------------------

Ren : ℕ → ℕ → Set
Ren k k' = Fin k → Fin k'

Sub : ℕ → ℕ → Set
Sub k k' = Fin k → Global k'

liftRen : ∀ {k k'} → Ren k k' → Ren (suc k) (suc k')
liftRen ρ zero    = zero
liftRen ρ (suc i) = suc (ρ i)

mutual
  renameMaybe : ∀ {k k'} → Ren k k' → Maybe (Global k) → Maybe (Global k')
  renameMaybe ρ nothing  = nothing
  renameMaybe ρ (just g) = just (rename ρ g)

  renameVec : ∀ {k k' m}
            → Ren k k'
            → Vec (Maybe (Global k)) m
            → Vec (Maybe (Global k')) m
  renameVec ρ []       = []
  renameVec ρ (m ∷ bs) = renameMaybe ρ m ∷ renameVec ρ bs

  renameB : ∀ {k k'} → Ren k k' → Branches k → Branches k'
  renameB ρ = renameVec ρ

  rename : ∀ {k k'} → Ren k k' → Global k → Global k'
  rename ρ end              = end
  rename ρ (msg p q b g)    = msg p q b (rename ρ g)
  rename ρ (choice p q bs)  = choice p q (renameB ρ bs)
  rename ρ (mu body)        = mu (rename (liftRen ρ) body)
  rename ρ (var i)          = var (ρ i)

wk : ∀ {k} → Global k → Global (suc k)
wk = rename suc

liftSub : ∀ {k k'} → Sub k k' → Sub (suc k) (suc k')
liftSub σ zero    = var zero
liftSub σ (suc i) = wk (σ i)

mutual
  substMaybe : ∀ {k k'} → Sub k k' → Maybe (Global k) → Maybe (Global k')
  substMaybe σ nothing  = nothing
  substMaybe σ (just g) = just (subst σ g)

  substVec : ∀ {k k' m}
           → Sub k k'
           → Vec (Maybe (Global k)) m
           → Vec (Maybe (Global k')) m
  substVec σ []       = []
  substVec σ (m ∷ bs) = substMaybe σ m ∷ substVec σ bs

  substB : ∀ {k k'} → Sub k k' → Branches k → Branches k'
  substB σ = substVec σ

  subst : ∀ {k k'} → Sub k k' → Global k → Global k'
  subst σ end             = end
  subst σ (msg p q b g)   = msg p q b (subst σ g)
  subst σ (choice p q bs) = choice p q (substB σ bs)
  subst σ (mu body)       = mu (subst (liftSub σ) body)
  subst σ (var i)         = σ i

------------------------------------------------------------------------
-- Unfold μ once
------------------------------------------------------------------------

unfold : ∀ {k} → Global k → Global k
unfold {k} (mu body) =
  subst σ body
  where
    σ : Sub (suc k) k
    σ zero    = mu body
    σ (suc i) = var i
unfold g = g
