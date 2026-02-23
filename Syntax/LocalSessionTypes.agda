{-# OPTIONS --safe #-}

module Syntax.LocalSessionTypes (ℓ n : _) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
import Core.BranchTables as BT
import Core.SessionBase as SB

module Core = SB ℓ n
open Core public using (Label; Participant; Base; _≢_)

------------------------------------------------------------------------
-- Local session types with μ + de Bruijn recursion vars
--
-- k = number of recursion variables in scope
------------------------------------------------------------------------

mutual
  -- A finite “branch table”: for each label, either no branch, or a continuation.
  Branches : ℕ → Set
  Branches k = Vec (Maybe (Local k)) ℓ

  data Local : ℕ → Set where
    end  : ∀ {k} → Local k

    -- payload actions (like p!⟨B⟩;T and p?⟨B⟩;T)
    send : ∀ {k} → Participant → Base → Local k → Local k
    recv : ∀ {k} → Participant → Base → Local k → Local k

    -- labelled choice (like p ⊕ {li : Ti} and p & {li : Ti})
    sel  : ∀ {k} → Participant → Branches k → Local k
    bra  : ∀ {k} → Participant → Branches k → Local k

    -- guarded recursion binder and recursion variable
    mu   : ∀ {k} → Local (suc k) → Local k
    var  : ∀ {k} → Fin k → Local k

-- Closed local types (no free recursion vars)
Local₀ : Set
Local₀ = Local 0

------------------------------------------------------------------------
-- Contexts (participant-indexed local environments)
------------------------------------------------------------------------

-- Sparse map view (participants not present are mapped to `nothing`).
ContextMap : Set
ContextMap = Participant → Maybe Local₀

emptyContextMap : ContextMap
emptyContextMap _ = nothing

singletonContextMap : Participant → Local₀ → ContextMap
singletonContextMap p T q with q ≟ p
... | yes _ = just T
... | no  _ = nothing

infixr 5 _∙Δ_
_∙Δ_ : ContextMap → ContextMap → ContextMap
(Δ₁ ∙Δ Δ₂) p with Δ₂ p
... | just T  = just T
... | nothing = Δ₁ p

-- Total map view (default local type for absent participants is `end`).
Context : Set
Context = Participant → Local₀

-- Conventional notation: contexts are written as capital Delta.
Δ : Set
Δ = Context

toContext : ContextMap → Context
toContext Δm p with Δm p
... | just T  = T
... | nothing = end

emptyΔ : Δ
emptyΔ = toContext emptyContextMap

singletonΔ : Participant → Local₀ → Δ
singletonΔ p T = toContext (singletonContextMap p T)

updateΔ : Participant → Local₀ → Δ → Δ
updateΔ p T Δ₀ q with q ≟ p
... | yes _ = T
... | no  _ = Δ₀ q

------------------------------------------------------------------------
-- Branch-table utilities (label comparison becomes just lookup)
------------------------------------------------------------------------

lookupB : ∀ {k} → Label → Branches k → Maybe (Local k)
lookupB = BT.lookupB

-- A singleton branch table: only label l is present.
singleton : ∀ {k} → Label → Local k → Branches k
singleton = BT.singleton

-- “Non-empty choice” as a predicate (keep it in WF, don’t bake into syntax)
NonEmpty : ∀ {k} → Branches k → Set
NonEmpty = BT.NonEmpty

------------------------------------------------------------------------
-- Renaming / substitution for recursion variables (de Bruijn)
-- (This is the workhorse that makes unfolding and later proofs easier.)
------------------------------------------------------------------------

Ren : ℕ → ℕ → Set
Ren k k' = Fin k → Fin k'

Sub : ℕ → ℕ → Set
Sub k k' = Fin k → Local k'

liftRen : ∀ {k k'} → Ren k k' → Ren (suc k) (suc k')
liftRen ρ zero    = zero
liftRen ρ (suc i) = suc (ρ i)

mutual
  renameMaybe : ∀ {k k'} → Ren k k' → Maybe (Local k) → Maybe (Local k')
  renameMaybe ρ nothing  = nothing
  renameMaybe ρ (just t) = just (rename ρ t)

  renameVec : ∀ {k k' m}
            → Ren k k'
            → Vec (Maybe (Local k)) m
            → Vec (Maybe (Local k')) m
  renameVec ρ []       = []
  renameVec ρ (m ∷ bs) = renameMaybe ρ m ∷ renameVec ρ bs

  renameB : ∀ {k k'} → Ren k k' → Branches k → Branches k'
  renameB ρ = renameVec ρ

  rename : ∀ {k k'} → Ren k k' → Local k → Local k'
  rename ρ end           = end
  rename ρ (send p b t)  = send p b (rename ρ t)
  rename ρ (recv p b t)  = recv p b (rename ρ t)
  rename ρ (sel p bs)    = sel p (renameB ρ bs)
  rename ρ (bra p bs)    = bra p (renameB ρ bs)
  rename ρ (mu body)     = mu (rename (liftRen ρ) body)
  rename ρ (var i)       = var (ρ i)

wk : ∀ {k} → Local k → Local (suc k)
wk = rename suc

liftSub : ∀ {k k'} → Sub k k' → Sub (suc k) (suc k')
liftSub σ zero    = var zero
liftSub σ (suc i) = wk (σ i)

mutual
  substMaybe : ∀ {k k'} → Sub k k' → Maybe (Local k) → Maybe (Local k')
  substMaybe σ nothing  = nothing
  substMaybe σ (just t) = just (subst σ t)

  substVec : ∀ {k k' m}
           → Sub k k'
           → Vec (Maybe (Local k)) m
           → Vec (Maybe (Local k')) m
  substVec σ []       = []
  substVec σ (m ∷ bs) = substMaybe σ m ∷ substVec σ bs

  substB : ∀ {k k'} → Sub k k' → Branches k → Branches k'
  substB σ = substVec σ

  subst : ∀ {k k'} → Sub k k' → Local k → Local k'
  subst σ end           = end
  subst σ (send p b t)  = send p b (subst σ t)
  subst σ (recv p b t)  = recv p b (subst σ t)
  subst σ (sel p bs)    = sel p (substB σ bs)
  subst σ (bra p bs)    = bra p (substB σ bs)
  subst σ (mu body)     = mu (subst (liftSub σ) body)
  subst σ (var i)       = σ i

------------------------------------------------------------------------
-- Unfold μ once (paper’s unfold(T))
------------------------------------------------------------------------

unfold : ∀ {k} → Local k → Local k
unfold {k} (mu body) =
  subst σ body
  where
    σ : Sub (suc k) k
    σ zero    = mu body          -- replace bound recursion var by μ-body itself
    σ (suc i) = var i            -- outer vars shift down
unfold t = t
