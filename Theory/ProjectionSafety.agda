{-# OPTIONS --safe --guardedness #-}

module Theory.ProjectionSafety (ℓ n : _) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Fin using (_≟_) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import Theory.MergeProjection as MP
import Theory.ProjectionProperties as PP
import Theory.LocalSemanticProperties as LSP
import Semantics.LocalOperationalSemantics as LOS
import Semantics.GlobalOperationalSemantics as GOS
import Subtyping.SessionSubtyping as SS
import Subtyping.SessionSubtypingProperties as SSP
import Syntax.WellFormedLocalTypes as WFLT
import Syntax.WellFormedGlobalTypes as WFGT

module M    = MP ℓ n
module P    = PP ℓ n
module S    = LSP ℓ n
module L    = LOS ℓ n
module G    = GOS ℓ n
module Sub  = SS ℓ n
module SubP = SSP ℓ n
module WFL  = WFLT ℓ n
module WFG  = WFGT ℓ n

------------------------------------------------------------------------
-- Re-exports from MergeProjection
------------------------------------------------------------------------

open M using
  ( Global₀
  ; Local₀
  ; Δ
  ; Participant
  ; Label
  ; Base
  ; _≢_
  ; _Π_
  ; MergeStep
  ; MergeSet
  ; lookupM
  ; _↾[_]_
  ; _↾_
  ; _⊑_
  ; ProjStep
  ; out↾
  ; wf-global
  ; wf-local
  ; BranchProj
  ; PR1
  ; PR2
  ; PR3
  ; PR4
  ; PR5
  ; PR6
  ; PR7
  ; PR8
  ; PR9
  ; M1
  ; M2
  ; M3
  ; M4
  ; M5
  ; M6
  ; send
  ; recv
  ; sel
  ; bra
  ; mu
  ; end
  ; msg
  ; choice
  ; gend
  ; gmu
  ; unfoldG
  ; ▹
  ; force
  ; next
  ; _≤Δ_
  ; roll↾
  ; wf-merged
  ; wf-set
  ; outΠ
  ; rollΠ
  )

------------------------------------------------------------------------
-- Re-exports from ProjectionProperties
------------------------------------------------------------------------

open P using
  ( safe
  ; SafeState
  ; rtc-refl
  ; ⊑-down-≤
  ; safe→SafeState
  ; updateΔ-other
  ; updateΔ₂-at-q
  ; updateΔ₂-at-p
  ; updateΔ₂-other
  ; sync-endpoints-distinct
  )

------------------------------------------------------------------------
-- Re-exports from LocalSemanticProperties
------------------------------------------------------------------------

open S using
  ( safeStateDownward
  ; stepSim≤
  ; rtc-step
  )

------------------------------------------------------------------------
-- Re-exports from SessionSubtypingProperties
------------------------------------------------------------------------

open SubP using
  ( ≤-refl
  ; ≤-refl-ctx
  ; ≤-trans
  ; ≤-trans-ctx
  )

------------------------------------------------------------------------
-- Re-exports from LocalOperationalSemantics
------------------------------------------------------------------------

open L using
  ( Observable
  ; Interaction
  ; _!⟨_⟩
  ; _?⟨_⟩
  ; _↝⟨_⟩_
  ; _-[_]→ₗ_
  ; updateΔ
  ; LR1
  ; LR2
  ; LR3
  ; LR5
  ; LTag
  ; LEnv
  ; CanSync₂
  )

------------------------------------------------------------------------
-- Re-exports from GlobalOperationalSemantics
------------------------------------------------------------------------

open G using
  ( _-[_]→ᵍ_
  ; GR1
  ; GR2
  ; GR3
  ; GR4
  ; GR5
  ; _→ᵍ*_
  )

------------------------------------------------------------------------
-- Re-exports from SessionSubtyping
------------------------------------------------------------------------

open Sub using
  ( _≤_
  ; wf-left
  ; wf-right
  ; out
  ; Step
  ; s-end
  ; s-send
  ; s-recv
  ; s-sel
  ; s-bra
  ; s-muL
  ; s-muR
  )

------------------------------------------------------------------------
-- Re-exports from WellFormedLocalTypes
------------------------------------------------------------------------

open WFL using (wfΔ)
  renaming (wf to wfL)

------------------------------------------------------------------------
-- Re-exports from WellFormedGlobalTypes
------------------------------------------------------------------------

open WFG using ()
  renaming (wf to wfG)

------------------------------------------------------------------------
-- Lemma stubs (to be filled in by later tasks)
--
--   merge-≤-branch     : …
--   safeState-from-↾   : …
--   sim-↾              : …
--   safe-from-↾        : …
------------------------------------------------------------------------
