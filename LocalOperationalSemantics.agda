{-# OPTIONS --safe --guardedness #-}

module LocalOperationalSemantics (ℓ n : _) where

open import Data.Maybe using (just)
open import Data.Product using (Σ; proj₁; proj₂; _×_) renaming (_,_ to _,Σ_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import LocalSessionTypes as LTS
import OperationalLabels as OL
import TransitionClosure as TC

module L = LTS ℓ n
module O = OL ℓ n
open L public using
  ( Label
  ; Participant
  ; Base
  ; Local
  ; Local₀
  ; end
  ; send
  ; recv
  ; sel
  ; bra
  ; mu
  ; Branches
  ; lookupB
  ; unfold
  ; Δ
  ; updateΔ
  )
open O public using
  ( Observable
  ; obsBase
  ; obsLabel
  ; Action
  ; _!⟨_⟩
  ; _?⟨_⟩
  ; TaggedAction
  ; _∶_
  ; Interaction
  ; _↝⟨_⟩_
  )
open TC public using (RTC; rtc-refl; rtc-step; rtc-single)

-- Local-type transitions
------------------------------------------------------------------------

infix 3 _-[_]→ₗ_
data _-[_]→ₗ_ : Local₀ → Action → Local₀ → Set where
  LR1 :
    ∀ {p b T}
    → send p b T -[ p !⟨ obsBase b ⟩ ]→ₗ T

  LR2 :
    ∀ {p b T}
    → recv p b T -[ p ?⟨ obsBase b ⟩ ]→ₗ T

  LR3 :
    ∀ {p bs l T}
    → lookupB l bs ≡ just T
    → sel p bs -[ p !⟨ obsLabel l ⟩ ]→ₗ T

  LR4 :
    ∀ {p bs l T}
    → lookupB l bs ≡ just T
    → bra p bs -[ p ?⟨ obsLabel l ⟩ ]→ₗ T

  LR5 :
    ∀ {body ζ T'}
    → unfold (mu body) -[ ζ ]→ₗ T'
    → mu body -[ ζ ]→ₗ T'

------------------------------------------------------------------------
-- One-sided context reductions
------------------------------------------------------------------------

infix 3 _-[_]→₁_
data _-[_]→₁_ : Δ → TaggedAction → Δ → Set where
  LTag :
    ∀ {Δ₀ p ζ T'}
    → Δ₀ p -[ ζ ]→ₗ T'
    → Δ₀ -[ p ∶ ζ ]→₁ updateΔ p T' Δ₀

------------------------------------------------------------------------
-- Two-sided synchronous reductions
------------------------------------------------------------------------

infix 3 _-[_]→₂_
data _-[_]→₂_ : Δ → Interaction → Δ → Set where
  LEnv :
    ∀ {Δ₀ p q U Tp' Tq'}
    → Δ₀ -[ p ∶ (q !⟨ U ⟩) ]→₁ updateΔ p Tp' Δ₀
    → Δ₀ -[ q ∶ (p ?⟨ U ⟩) ]→₁ updateΔ q Tq' Δ₀
    → Δ₀ -[ p ↝⟨ U ⟩ q ]→₂ updateΔ q Tq' (updateΔ p Tp' Δ₀)

------------------------------------------------------------------------
-- Helper relations (existentially quantified labels/actions)
--
-- If the relation does not expose a label/action argument, it means:
-- "there exists one for which the step holds".
------------------------------------------------------------------------

infix 3 _→ₗ_ _→₁_ _→₂_ _-[_]!→ₗ_ _-[_]?→ₗ_ _-[_,_]!→₁_ _-[_,_]?→₁_ _-[_,_]→₂_

_→ₗ_ : Local₀ → Local₀ → Set
T →ₗ T' = Σ Action (λ ζ → T -[ ζ ]→ₗ T')

_→₁_ : Δ → Δ → Set
Δ₀ →₁ Δ₁ = Σ TaggedAction (λ α → Δ₀ -[ α ]→₁ Δ₁)

_→₂_ : Δ → Δ → Set
Δ₀ →₂ Δ₁ = Σ Interaction (λ ι → Δ₀ -[ ι ]→₂ Δ₁)

_-[_]!→ₗ_ : Local₀ → Participant → Local₀ → Set
T -[ p ]!→ₗ T' = Σ Observable (λ U → T -[ p !⟨ U ⟩ ]→ₗ T')

_-[_]?→ₗ_ : Local₀ → Participant → Local₀ → Set
T -[ p ]?→ₗ T' = Σ Observable (λ U → T -[ p ?⟨ U ⟩ ]→ₗ T')

_-[_,_]!→₁_ : Δ → Participant → Participant → Δ → Set
Δ₀ -[ p , q ]!→₁ Δ₁ = Σ Observable (λ U → Δ₀ -[ p ∶ (q !⟨ U ⟩) ]→₁ Δ₁)

_-[_,_]?→₁_ : Δ → Participant → Participant → Δ → Set
Δ₀ -[ p , q ]?→₁ Δ₁ = Σ Observable (λ U → Δ₀ -[ p ∶ (q ?⟨ U ⟩) ]→₁ Δ₁)

_-[_,_]→₂_ : Δ → Participant → Participant → Δ → Set
Δ₀ -[ p , q ]→₂ Δ₁ = Σ Observable (λ U → Δ₀ -[ p ↝⟨ U ⟩ q ]→₂ Δ₁)

-- Reflexive-transitive closure of unlabeled two-sided context reductions.
infix 3 _→₂*_
_→₂*_ : Δ → Δ → Set
Δ₀ →₂* Δ₁ = RTC _→₂_ Δ₀ Δ₁

------------------------------------------------------------------------
-- Deadlock freedom for contexts
------------------------------------------------------------------------

CanStep₂ : Δ → Set
CanStep₂ Δ₀ = Σ Δ (λ Δ₁ → Δ₀ →₂ Δ₁)

Stuck₂ : Δ → Set
Stuck₂ Δ₀ = ¬ CanStep₂ Δ₀

Terminal₂ : Δ → Set
Terminal₂ Δ₀ = ∀ p → unfold (Δ₀ p) ≡ end

deadlockFree : Δ → Set
deadlockFree Δ₀ =
  ∀ {Δ₁}
  → Δ₀ →₂* Δ₁
  → Stuck₂ Δ₁
  → Terminal₂ Δ₁

------------------------------------------------------------------------
-- Safety for contexts
------------------------------------------------------------------------

CanSync₂ : Δ → Participant → Participant → Observable → Set
CanSync₂ Δ₀ p q U = Σ Δ (λ Δ₁ → Δ₀ -[ p ↝⟨ U ⟩ q ]→₂ Δ₁)

SafeState : Δ → Set
SafeState Δ₀ =
  ∀ {p q U U' Δp Δq}
  → Δ₀ -[ p ∶ (q !⟨ U ⟩) ]→₁ Δp
  → Δ₀ -[ q ∶ (p ?⟨ U' ⟩) ]→₁ Δq
  → CanSync₂ Δ₀ p q U

safe : Δ → Set
safe Δ₀ =
  ∀ {Δ₁}
  → Δ₀ →₂* Δ₁
  → SafeState Δ₁

-- Coinductive traces and fairness for unlabeled →₂
------------------------------------------------------------------------

mutual
  data TraceView : Δ → Set where
    tstop : ∀ {Δ₀} → Stuck₂ Δ₀ → TraceView Δ₀
    tstep : ∀ {Δ₀ Δ₁} → Δ₀ →₂ Δ₁ → Trace Δ₁ → TraceView Δ₀

  -- Maximal traces: either terminate in a stuck state, or continue forever.
  record Trace (Δ₀ : Δ) : Set where
    coinductive
    field unfoldᵗ : TraceView Δ₀
open Trace public

-- Fair traces (scheduling fairness for participant pairs)
------------------------------------------------------------------------

CanPair₂ : Δ → Participant → Participant → Set
CanPair₂ Δ₀ p q = Σ Δ (λ Δ₁ → Δ₀ -[ p , q ]→₂ Δ₁)

forgetPair₂ : ∀ {Δ₀ p q Δ₁} → Δ₀ -[ p , q ]→₂ Δ₁ → Δ₀ →₂ Δ₁
forgetPair₂ {p = p} {q = q} r = (p ↝⟨ proj₁ r ⟩ q ,Σ proj₂ r)

mutual
  -- Eventually (along the trace) we see an actual on-trace p,q communication.
  data EventuallyPairV (p q : Participant) : ∀ {Δ₀} → TraceView Δ₀ → Set where
    ev-here :
      ∀ {Δ₀ Δ₁ τ}
      → (r : Δ₀ -[ p , q ]→₂ Δ₁)
      → EventuallyPairV p q (tstep (forgetPair₂ r) τ)
    ev-next :
      ∀ {Δ₀ Δ₁ r τ}
      → EventuallyPair p q τ
      → EventuallyPairV p q (tstep {Δ₀} {Δ₁} r τ)

  EventuallyPair : Participant → Participant → ∀ {Δ₀} → Trace Δ₀ → Set
  EventuallyPair p q τ = EventuallyPairV p q (unfoldᵗ τ)

FairHere : ∀ {Δ₀} → Trace Δ₀ → Set
FairHere {Δ₀} τ =
  ∀ p q
  → CanPair₂ Δ₀ p q
  → EventuallyPair p q τ

mutual
  -- Coinductively require `FairHere` at every point on the trace.
  record Fair {Δ₀ : Δ} (τ : Trace Δ₀) : Set where
    coinductive
    field
      fair-here : FairHere τ
      fair-next : FairV (unfoldᵗ τ)

  data FairV : ∀ {Δ₀} → TraceView Δ₀ → Set where
    fair-stop : ∀ {Δ₀ s} → FairV (tstop {Δ₀} s)
    fair-step : ∀ {Δ₀ Δ₁ r τ} → Fair τ → FairV (tstep {Δ₀} {Δ₁} r τ)
open Fair public

------------------------------------------------------------------------
-- Live traces (recurrence of one-sided capabilities)
------------------------------------------------------------------------

CanSend₁ : Δ → Participant → Participant → Set
CanSend₁ Δ₀ p q = Σ Δ (λ Δ₁ → Δ₀ -[ p , q ]!→₁ Δ₁)

CanRecv₁ : Δ → Participant → Participant → Set
CanRecv₁ Δ₀ p q = Σ Δ (λ Δ₁ → Δ₀ -[ p , q ]?→₁ Δ₁)

mutual
  -- Eventuality along a trace: witness may hold now or at a later state.
  data Eventually₁V (R : Δ → Set) : ∀ {Δ₀} → TraceView Δ₀ → Set where
    ev₁-now-stop :
      ∀ {Δ₀ s}
      → R Δ₀
      → Eventually₁V R (tstop {Δ₀} s)
    ev₁-now-step :
      ∀ {Δ₀ Δ₁ r τ}
      → R Δ₀
      → Eventually₁V R (tstep {Δ₀} {Δ₁} r τ)
    ev₁-next :
      ∀ {Δ₀ Δ₁ r τ}
      → Eventually₁ R τ
      → Eventually₁V R (tstep {Δ₀} {Δ₁} r τ)

  Eventually₁ : (Δ → Set) → ∀ {Δ₀} → Trace Δ₀ → Set
  Eventually₁ R τ = Eventually₁V R (unfoldᵗ τ)

EventuallySend : Participant → Participant → ∀ {Δ₀} → Trace Δ₀ → Set
EventuallySend p q = Eventually₁ (λ Δ₁ → CanSend₁ Δ₁ p q)

EventuallyRecv : Participant → Participant → ∀ {Δ₀} → Trace Δ₀ → Set
EventuallyRecv p q = Eventually₁ (λ Δ₁ → CanRecv₁ Δ₁ p q)

record LiveHere {Δ₀ : Δ} (τ : Trace Δ₀) : Set where
  field
    send-live :
      ∀ p q
      → CanSend₁ Δ₀ p q
      → EventuallySend p q τ
    recv-live :
      ∀ p q
      → CanRecv₁ Δ₀ p q
      → EventuallyRecv p q τ
open LiveHere public

mutual
  -- Liveness holds at every point of the trace.
  record Live {Δ₀ : Δ} (τ : Trace Δ₀) : Set where
    coinductive
    field
      live-here : LiveHere τ
      live-next : LiveV (unfoldᵗ τ)

  data LiveV : ∀ {Δ₀} → TraceView Δ₀ → Set where
    live-stop : ∀ {Δ₀ s} → LiveV (tstop {Δ₀} s)
    live-step : ∀ {Δ₀ Δ₁ r τ} → Live τ → LiveV (tstep {Δ₀} {Δ₁} r τ)
open Live public

-- A context is live when every fair trace starting from it is live.
liveContext : Δ → Set
liveContext Δ₀ = ∀ (τ : Trace Δ₀) → Fair τ → Live τ
