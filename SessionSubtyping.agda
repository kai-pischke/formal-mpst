{-# OPTIONS --safe --guardedness #-}

module SessionSubtyping (ℓ n : _) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
import LocalSessionTypes as LTS
import WellFormedLocalTypes as WF

module L = LTS ℓ n
module W = WF ℓ n

open W public using (wf)
open L public using
  ( Label
  ; Participant
  ; Base
  ; Δ
  ; Branches
  ; Local
  ; Local₀
  ; end
  ; send
  ; recv
  ; sel
  ; bra
  ; mu
  ; var
  ; lookupB
  ; unfold
  )

------------------------------------------------------------------------
-- A small delay modality to keep guardedness happy under Step
------------------------------------------------------------------------

record ▹ (A : Set) : Set where
  coinductive
  field force : A
open ▹ public

next : ∀ {A : Set} → A → ▹ A
force (next a) = a

------------------------------------------------------------------------
-- Choice side-conditions, pointwise by label (no I ⊆ J proofs)
------------------------------------------------------------------------

data SelM {k : ℕ}
         (R : Local k → Local k → Set)
         : Maybe (Local k) → Maybe (Local k) → Set where
  sel-none : ∀ {mb} → SelM R nothing mb
  sel-just : ∀ {t u} → R t u → SelM R (just t) (just u)

data BraM {k : ℕ}
         (R : Local k → Local k → Set)
         : Maybe (Local k) → Maybe (Local k) → Set where
  bra-none : ∀ {ma} → BraM R ma nothing
  bra-just : ∀ {t u} → R t u → BraM R (just t) (just u)

SelDom≤ : ∀ {k} → (Local k → Local k → Set) → Branches k → Branches k → Set
SelDom≤ R bs bs' = ∀ l → SelM R (lookupB l bs) (lookupB l bs')

BraDom≤ : ∀ {k} → (Local k → Local k → Set) → Branches k → Branches k → Set
BraDom≤ R bs bs' = ∀ l → BraM R (lookupB l bs) (lookupB l bs')

------------------------------------------------------------------------
-- One-step rules (S1–S7) parameterised by recursive relation R
------------------------------------------------------------------------

data Step {k : ℕ}
          (R : Local k → Local k → Set)
          : Local k → Local k → Set where

  s-end : Step R end end
  s-var : ∀ {i} → Step R (var i) (var i)

  -- [S1] send
  s-send : ∀ {p b T U} → R T U → Step R (send p b T) (send p b U)

  -- [S2] recv
  s-recv : ∀ {p b T U} → R T U → Step R (recv p b T) (recv p b U)

  -- [S3] selection: left labels ⊆ right labels, pointwise
  s-sel : ∀ {p bs bs'} → SelDom≤ R bs bs' → Step R (sel p bs) (sel p bs')

  -- [S4] branching: right labels ⊆ left labels, pointwise
  s-bra : ∀ {p bs bs'} → BraDom≤ R bs bs' → Step R (bra p bs) (bra p bs')

  -- [S5] unfold on the left
  s-muL : ∀ {body U} → R (unfold (mu body)) U → Step R (mu body) U

  -- [S6] unfold on the right
  s-muR : ∀ {T body'} → R T (unfold (mu body')) → Step R T (mu body')

------------------------------------------------------------------------
-- Coinductive subtyping: greatest fixed point of Step
------------------------------------------------------------------------

infix 4 _≤_
record _≤_ (T U : Local₀) : Set where
  coinductive
  field
    wf-left  : wf T
    wf-right : wf U
    out      : Step (λ X Y → ▹ (X ≤ Y)) T U
open _≤_ public

roll : ∀ {T U : Local₀}
     → wf T
     → wf U
     → Step (λ X Y → ▹ (X ≤ Y)) T U
     → T ≤ U
wf-left  (roll wT wU s) = wT
wf-right (roll wT wU s) = wU
out      (roll wT wU s) = s

------------------------------------------------------------------------
-- Context subtyping (pointwise local subtyping)
------------------------------------------------------------------------

infix 4 _≤Δ_
_≤Δ_ : Δ → Δ → Set
Δ₀ ≤Δ Δ₁ = ∀ p → Δ₀ p ≤ Δ₁ p
