{-# OPTIONS --safe --guardedness #-}

module Theory.WellFormedGlobalTypes (ℓ n : _) where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (suc)
open import Data.Fin using (Fin)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Syntax.GlobalSessionTypes as GTS

module G = GTS ℓ n

open G public using
  ( Label
  ; Participant
  ; Base
  ; _≢_
  ; Global
  ; Global₀
  ; end
  ; msg
  ; choice
  ; mu
  ; var
  ; Branches
  ; lookupB
  ; NonEmpty
  ; unfold
  )

-- Guarded recursion
------------------------------------------------------------------------

mutual
  GuardedBranches : ∀ {k} → Bool → Branches k → Set
  GuardedBranches g bs =
    ∀ {l g'} → lookupB l bs ≡ just g' → GuardedFrom g g'

  data GuardedFrom : ∀ {k} → Bool → Global k → Set where
    g-end :
      ∀ {k g}
      → GuardedFrom {k} g end

    g-msg :
      ∀ {k g} {p q : Participant} {b : Base} {g' : Global k}
      → GuardedFrom {k} true g'
      → GuardedFrom {k} g (msg p q b g')

    g-choice :
      ∀ {k g} {p q : Participant} {bs : Branches k}
      → GuardedBranches true bs
      → GuardedFrom {k} g (choice p q bs)

    g-mu :
      ∀ {k g} {body : Global (suc k)}
      → GuardedFrom {suc k} false body
      → GuardedFrom {k} g (mu body)

    g-var :
      ∀ {k} {i : Fin k}
      → GuardedFrom {k} true (var i)

Guarded : ∀ {k} → Global k → Set
Guarded = GuardedFrom false

-- Well-formed closed global types
-- 1) recursion is guarded
-- 2) every choice has at least one label
-- 3) no self communication p -> p
------------------------------------------------------------------------

mutual
  wfBranches : Branches 0 → Set
  wfBranches bs =
    ∀ {l g'} → lookupB l bs ≡ just g' → wf g'

  data wf : Global₀ → Set where
    wf-end :
      wf end

    wf-msg :
      ∀ {p q b g'}
      → p ≢ q
      → wf g'
      → wf (msg p q b g')

    wf-choice :
      ∀ {p q bs}
      → p ≢ q
      → NonEmpty bs
      → wfBranches bs
      → wf (choice p q bs)

    wf-mu :
      ∀ {body}
      → Guarded body
      → wf (unfold (mu body))
      → wf (mu body)

-- Projections
------------------------------------------------------------------------

wf-no-self-msg : ∀ {p q b g'} → wf (msg p q b g') → p ≢ q
wf-no-self-msg (wf-msg p≢q _) = p≢q

wf-no-self-choice : ∀ {p q bs} → wf (choice p q bs) → p ≢ q
wf-no-self-choice (wf-choice p≢q _ _) = p≢q

wf-guarded : ∀ {body} → wf (mu body) → Guarded body
wf-guarded (wf-mu g _) = g

wf-nonempty-choice : ∀ {p q bs} → wf (choice p q bs) → NonEmpty bs
wf-nonempty-choice (wf-choice _ ne _) = ne

-- Fully unfold leading μ using well-formedness evidence.
-- This is total because wf-mu provides a strictly smaller wf witness
-- on unfold(mu body).
unfold* : ∀ {G : Global₀} → wf G → Global₀
unfold* {G = end}              wf-end              = end
unfold* {G = msg p q b g'}     (wf-msg _ _)        = msg p q b g'
unfold* {G = choice p q bs}    (wf-choice _ _ _)   = choice p q bs
unfold* {G = mu body}          (wf-mu _ wunfolded) = unfold* wunfolded
