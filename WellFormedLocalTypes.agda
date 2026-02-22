{-# OPTIONS --safe --guardedness #-}

module WellFormedLocalTypes (ℓ n : _) where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (suc)
open import Data.Fin using (Fin; _≟_)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import LocalSessionTypes as LTS
import LocalOperationalSemantics as LOS

module L = LTS ℓ n
module S = LOS ℓ n

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
  ; var
  ; Branches
  ; lookupB
  ; NonEmpty
  ; unfold
  ; Δ
  ; updateΔ
  )

open S public using
  ( Observable
  ; Action
  ; TaggedAction
  ; _∶_
  ; Interaction
  ; _-[_]→ₗ_
  ; _-[_]→₁_
  ; _-[_]→₂_
  ; LR1
  ; LR2
  ; LR3
  ; LR4
  ; LR5
  ; LTag
  ; LEnv
  )

-- Guarded recursion
------------------------------------------------------------------------

mutual
  GuardedBranches : ∀ {k} → Bool → Branches k → Set
  GuardedBranches g bs =
    ∀ {l t} → lookupB l bs ≡ just t → GuardedFrom g t

  data GuardedFrom : ∀ {k} → Bool → Local k → Set where
    g-end  : ∀ {k g} → GuardedFrom {k} g (end {k})
    g-send :
      ∀ {k g} {p : Participant} {B : Base} {t : Local k}
      → GuardedFrom {k} true t
      → GuardedFrom {k} g (send {k} p B t)
    g-recv :
      ∀ {k g} {p : Participant} {B : Base} {t : Local k}
      → GuardedFrom {k} true t
      → GuardedFrom {k} g (recv {k} p B t)
    g-sel  :
      ∀ {k g} {p : Participant} {bs : Branches k}
      → GuardedBranches true bs
      → GuardedFrom {k} g (sel {k} p bs)
    g-bra  :
      ∀ {k g} {p : Participant} {bs : Branches k}
      → GuardedBranches true bs
      → GuardedFrom {k} g (bra {k} p bs)
    g-mu   :
      ∀ {k g} {body : Local (suc k)}
      → GuardedFrom {suc k} false body
      → GuardedFrom {k} g (mu {k} body)
    g-var  :
      ∀ {k} {i : Fin k}
      → GuardedFrom {k} true (var {k} i)

Guarded : ∀ {k} → Local k → Set
Guarded = GuardedFrom false

-- Well-formed closed local types
-- 1) recursion is guarded
-- 2) every selection/branching has at least one label
------------------------------------------------------------------------

mutual
  wfBranches : Branches 0 → Set
  wfBranches bs =
    ∀ {l t} → lookupB l bs ≡ just t → wf t

  data wf : Local₀ → Set where
    wf-end  : wf end
    wf-send : ∀ {p B t} → wf t → wf (send p B t)
    wf-recv : ∀ {p B t} → wf t → wf (recv p B t)
    wf-sel  : ∀ {p bs} → NonEmpty bs → wfBranches bs → wf (sel p bs)
    wf-bra  : ∀ {p bs} → NonEmpty bs → wfBranches bs → wf (bra p bs)
    wf-mu   : ∀ {body} → Guarded body → wf (unfold (mu body)) → wf (mu body)

------------------------------------------------------------------------
-- Projections showing what wf enforces
------------------------------------------------------------------------

wf-guarded : ∀ {body} → wf (mu body) → Guarded body
wf-guarded (wf-mu g _) = g

wf-nonempty-sel : ∀ {p bs} → wf (sel p bs) → NonEmpty bs
wf-nonempty-sel (wf-sel ne _) = ne

wf-nonempty-bra : ∀ {p bs} → wf (bra p bs) → NonEmpty bs
wf-nonempty-bra (wf-bra ne _) = ne

------------------------------------------------------------------------
-- Preservation by semantics
------------------------------------------------------------------------

wf-pres-→ₗ : ∀ {T ζ T'} → wf T → T -[ ζ ]→ₗ T' → wf T'
wf-pres-→ₗ (wf-send wT) LR1 = wT
wf-pres-→ₗ (wf-recv wT) LR2 = wT
wf-pres-→ₗ (wf-sel _ wbs) (LR3 hit) = wbs hit
wf-pres-→ₗ (wf-bra _ wbs) (LR4 hit) = wbs hit
wf-pres-→ₗ (wf-mu _ wunf) (LR5 step) = wf-pres-→ₗ wunf step

wfΔ : Δ → Set
wfΔ Δ₀ = ∀ p → wf (Δ₀ p)

wf-pres-→₁ : ∀ {Δ₀ α Δ₁} → wfΔ Δ₀ → Δ₀ -[ α ]→₁ Δ₁ → wfΔ Δ₁
wf-pres-→₁ wΔ (LTag {Δ₀} {p} {ζ} {T'} step) r with r ≟ p
... | yes _ = wf-pres-→ₗ (wΔ p) step
... | no  _ = wΔ r

updateΔ-self : ∀ {Δ₀ p T} → updateΔ p T Δ₀ p ≡ T
updateΔ-self {Δ₀} {p} {T} with p ≟ p
... | yes _   = refl
... | no p≢p  = ⊥-elim (p≢p refl)

wf-target-→₁ : ∀ {Δ₀ p ζ T'} → wfΔ Δ₀ → Δ₀ -[ p ∶ ζ ]→₁ updateΔ p T' Δ₀ → wf T'
wf-target-→₁ {Δ₀} {p} {ζ} {T'} wΔ red =
  subst wf (updateΔ-self {Δ₀} {p} {T'}) (wf-pres-→₁ wΔ red p)

-- Fully unfold leading μ using well-formedness evidence.
-- This is total because wf-mu provides a strictly smaller wf witness
-- on unfold(mu body).
unfold* : ∀ {T : Local₀} → wf T → Local₀
unfold* {T = end}            wf-end            = end
unfold* {T = send p B t}     (wf-send _)       = send p B t
unfold* {T = recv p B t}     (wf-recv _)       = recv p B t
unfold* {T = sel p bs}       (wf-sel _ _)      = sel p bs
unfold* {T = bra p bs}       (wf-bra _ _)      = bra p bs
unfold* {T = mu body}        (wf-mu _ wunfold) = unfold* wunfold

wf-pres-→₂ : ∀ {Δ₀ ι Δ₁} → wfΔ Δ₀ → Δ₀ -[ ι ]→₂ Δ₁ → wfΔ Δ₁
wf-pres-→₂ wΔ (LEnv {Δ₀} {p} {q} {U} {Tp'} {Tq'} pRed qRed) r with r ≟ q
... | yes _ = wf-target-→₁ wΔ qRed
... | no  _ = wf-pres-→₁ wΔ pRed r
