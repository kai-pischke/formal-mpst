{-# OPTIONS --safe --guardedness #-}

module Theory.SessionSubtypingProperties (ℓ n : _) where

open import Data.Maybe using (Maybe; just; nothing)
import Theory.SessionSubtyping as ST
import Theory.WellFormedLocalTypes as WF

module S = ST ℓ n
module W = WF ℓ n

open S public using
  ( Local
  ; Branches
  ; lookupB
  ; _≤_
  ; _≤Δ_
  ; wf-left
  ; wf-right
  ; out
  ; ▹
  ; force
  ; next
  ; Step
  ; s-end
  ; s-send
  ; s-recv
  ; s-sel
  ; s-bra
  ; s-muL
  ; s-muR
  ; SelDom≤
  ; BraDom≤
  ; SelM
  ; BraM
  ; sel-none
  ; sel-just
  ; bra-none
  ; bra-just
  )

open W public using
  ( Participant
  ; Local₀
  ; Δ
  ; send
  ; recv
  ; sel
  ; bra
  ; mu
  ; end
  ; wf
  ; wfΔ
  ; wfBranches
  ; wf-end
  ; wf-send
  ; wf-recv
  ; wf-sel
  ; wf-bra
  ; wf-mu
  )

private
  R : Local 0 → Local 0 → Set
  R X Y = ▹ (X ≤ Y)

------------------------------------------------------------------------
-- Reflexivity.
------------------------------------------------------------------------

mutual
  ≤-refl : ∀ {T : Local₀} → wf T → T ≤ T
  wf-left (≤-refl wT) = wT
  wf-right (≤-refl wT) = wT
  out (≤-refl wf-end) = s-end
  out (≤-refl (wf-send wT)) = s-send (next (≤-refl wT))
  out (≤-refl (wf-recv wT)) = s-recv (next (≤-refl wT))
  out (≤-refl (wf-sel {bs = bs} _ wbs)) = s-sel (SelRefl {bs = bs} wbs)
  out (≤-refl (wf-bra {bs = bs} _ wbs)) = s-bra (BraRefl {bs = bs} wbs)
  out (≤-refl wμ@(wf-mu _ _)) = s-muL (next (≤-unfold≤mu wμ))

  ≤-unfold≤mu : ∀ {body} → wf (mu body) → S.unfold (mu body) ≤ mu body
  wf-left (≤-unfold≤mu (wf-mu _ wunf)) = wunf
  wf-right (≤-unfold≤mu wμ) = wμ
  out (≤-unfold≤mu (wf-mu _ wunf)) = s-muR (next (≤-refl wunf))

  SelRefl :
    ∀ {bs : Branches 0}
    → wfBranches bs
    → SelDom≤ R bs bs
  SelRefl {bs} wbs l with lookupB l bs in eq
  ... | nothing = sel-none
  ... | just t = sel-just (next (≤-refl (wbs eq)))

  BraRefl :
    ∀ {bs : Branches 0}
    → wfBranches bs
    → BraDom≤ R bs bs
  BraRefl {bs} wbs l with lookupB l bs in eq
  ... | nothing = bra-none
  ... | just t = bra-just (next (≤-refl (wbs eq)))

------------------------------------------------------------------------
-- Transitivity.
------------------------------------------------------------------------

data Comp : Local₀ → Local₀ → Set where
  comp : ∀ {T U V : Local₀} → T ≤ U → U ≤ V → Comp T V

private
  RC : Local 0 → Local 0 → Set
  RC X Y = ▹ (Comp X Y)

comp-wf-left : ∀ {T V} → Comp T V → wf T
comp-wf-left (comp tu uv) = wf-left tu

comp-wf-right : ∀ {T V} → Comp T V → wf V
comp-wf-right (comp tu uv) = wf-right uv

sel-compose :
  ∀ {a b c : Maybe Local₀}
  → SelM R a b
  → SelM R b c
  → SelM RC a c
sel-compose sel-none _ = sel-none
sel-compose (sel-just r₁) (sel-just r₂) =
  sel-just (next (comp (force r₁) (force r₂)))

bra-compose :
  ∀ {a b c : Maybe Local₀}
  → BraM R a b
  → BraM R b c
  → BraM RC a c
bra-compose _ bra-none = bra-none
bra-compose (bra-just r₁) (bra-just r₂) =
  bra-just (next (comp (force r₁) (force r₂)))

comp-step-wf :
  ∀ {T U V : Local₀}
  → wf U
  → T ≤ U
  → U ≤ V
  → Step RC T V
comp-step-wf wU tu uv with out tu | out uv
... | s-muL tU | uV = s-muL (next (comp (force tU) uv))
... | tU | s-muR uV = s-muR (next (comp tu (force uV)))
... | s-end | s-end = s-end
... | s-send tU | s-send uV = s-send (next (comp (force tU) (force uV)))
... | s-recv tU | s-recv uV = s-recv (next (comp (force tU) (force uV)))
... | s-sel tU | s-sel uV = s-sel (λ l → sel-compose (tU l) (uV l))
... | s-bra tU | s-bra uV = s-bra (λ l → bra-compose (tU l) (uV l))
... | s-muR tU | s-muL uV with wU
... | wf-mu _ wunf = comp-step-wf wunf (force tU) (force uV)

comp-step : ∀ {T V : Local₀} → Comp T V → Step RC T V
comp-step (comp tu uv) = comp-step-wf (wf-right tu) tu uv

≤-from-comp : ∀ {T V : Local₀} → Comp T V → T ≤ V
wf-left (≤-from-comp c) = comp-wf-left c
wf-right (≤-from-comp c) = comp-wf-right c
out (≤-from-comp c) with comp-step c
... | s-end = s-end
... | s-send r = s-send (record { force = ≤-from-comp (force r) })
... | s-recv r = s-recv (record { force = ≤-from-comp (force r) })
... | s-sel rs = s-sel (λ l → mapSel (rs l))
  where
    mapSel : ∀ {a b : Maybe Local₀} → SelM RC a b → SelM R a b
    mapSel sel-none = sel-none
    mapSel (sel-just r) = sel-just (record { force = ≤-from-comp (force r) })
... | s-bra rs = s-bra (λ l → mapBra (rs l))
  where
    mapBra : ∀ {a b : Maybe Local₀} → BraM RC a b → BraM R a b
    mapBra bra-none = bra-none
    mapBra (bra-just r) = bra-just (record { force = ≤-from-comp (force r) })
... | s-muL r = s-muL (record { force = ≤-from-comp (force r) })
... | s-muR r = s-muR (record { force = ≤-from-comp (force r) })

≤-trans : ∀ {T U V : Local₀} → T ≤ U → U ≤ V → T ≤ V
≤-trans tu uv = ≤-from-comp (comp tu uv)

------------------------------------------------------------------------
-- Context-level corollaries.
------------------------------------------------------------------------

≤-refl-ctx : ∀ {Δ₀} → wfΔ Δ₀ → (p : Participant) → Δ₀ p ≤ Δ₀ p
≤-refl-ctx wfΔ₀ p = ≤-refl (wfΔ₀ p)

≤-trans-ctx :
  ∀ {Δ₀ Δ₁ Δ₂ : Δ}
  → Δ₀ ≤Δ Δ₁
  → Δ₁ ≤Δ Δ₂
  → Δ₀ ≤Δ Δ₂
≤-trans-ctx Δ₀≤Δ₁ Δ₁≤Δ₂ p = ≤-trans (Δ₀≤Δ₁ p) (Δ₁≤Δ₂ p)
