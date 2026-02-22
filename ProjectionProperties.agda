{-# OPTIONS --safe --guardedness #-}

module ProjectionProperties (ℓ n : _) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (_≟_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import MergeProjection as MP
import LocalSemanticProperties as LSP
import LocalOperationalSemantics as LOS
import GlobalOperationalSemantics as GOS
import SessionSubtypingProperties as SSP

module M = MP ℓ n
module S = LSP ℓ n
module L = LOS ℓ n
module G = GOS ℓ n
module SubP = SSP ℓ n

open M public using
  ( Global₀
  ; Δ
  ; Local₀
  ; Label
  ; Base
  ; msg
  ; choice
  ; gmu
  ; unfoldG
  ; send
  ; recv
  ; sel
  ; bra
  ; mu
  ; end
  ; lookupGB
  ; lookupM
  ; Participant
  ; _≢_
  ; roll↾
  ; out↾
  ; force
  ; next
  ; ProjStep
  ; PR1
  ; PR2
  ; PR3
  ; PR4
  ; PR5
  ; PR6
  ; PR7
  ; PR8
  ; PR9
  ; BranchProj
  ; _↾[_]_
  ; _↾_
  ; _⊑_
  )

open S public using
  ( safe
  ; SafeState
  ; safe-downward-≤
  ; stepSim≤-pair
  ; rtc-refl
  ; _≤Δ_
  ; tag-step-target
  )

open SubP using (_≤_; ≤-trans-ctx)

open L using
  ( Observable
  ; obsBase
  ; obsLabel
  ; _!⟨_⟩
  ; _?⟨_⟩
  ; _↝⟨_⟩_
  ; LEnv
  ; LTag
  ; _-[_]→₂_
  ; _-[_]→₁_
  ; _-[_]→ₗ_
  ; updateΔ
  ; LR1
  ; LR2
  ; LR3
  ; LR4
  ; LR5
  )

open G using
  ( DisjointEndpoints
  ; GR1
  ; GR2
  ; GR3
  ; GR4
  ; GR5
  ; GM-none
  ; GM-step
  ; GB-[]
  ; GB-∷
  ; _-[_]→ᵍ_
  ; _-[_]→ᵐ_
  ; _-[_]→ᵇ_
  )

updateΔ-self :
  ∀ {Δ₀ : Δ} {p : Participant} {T : Local₀}
  → updateΔ p T Δ₀ p ≡ T
updateΔ-self {p = p} with p ≟ p
... | yes _ = refl
... | no p≢p = ⊥-elim (p≢p refl)

updateΔ-other :
  ∀ {Δ₀ : Δ} {p r : Participant} {T : Local₀}
  → r ≢ p
  → updateΔ p T Δ₀ r ≡ Δ₀ r
updateΔ-other {p = p} {r = r} r≢p with r ≟ p
... | yes eq = ⊥-elim (r≢p eq)
... | no _ = refl

updateΔ₂-at-q :
  ∀ {Δ₀ : Δ} {p q : Participant} {Tp Tq : Local₀}
  → updateΔ q Tq (updateΔ p Tp Δ₀) q ≡ Tq
updateΔ₂-at-q {Δ₀} {p} {q} {Tp} {Tq} =
  updateΔ-self {Δ₀ = updateΔ p Tp Δ₀} {p = q} {T = Tq}

updateΔ₂-at-p :
  ∀ {Δ₀ : Δ} {p q : Participant} {Tp Tq : Local₀}
  → p ≢ q
  → updateΔ q Tq (updateΔ p Tp Δ₀) p ≡ Tp
updateΔ₂-at-p {Δ₀} {p} {q} {Tp} {Tq} p≢q =
  trans (updateΔ-other {Δ₀ = updateΔ p Tp Δ₀} {p = q} {r = p} p≢q)
        (updateΔ-self {Δ₀ = Δ₀} {p = p} {T = Tp})

updateΔ₂-other :
  ∀ {Δ₀ : Δ} {p q r : Participant} {Tp Tq : Local₀}
  → r ≢ p
  → r ≢ q
  → updateΔ q Tq (updateΔ p Tp Δ₀) r ≡ Δ₀ r
updateΔ₂-other {Δ₀} {p} {q} {r} {Tp} {Tq} r≢p r≢q =
  trans (updateΔ-other {Δ₀ = updateΔ p Tp Δ₀} {p = q} {r = r} r≢q)
        (updateΔ-other {Δ₀ = Δ₀} {p = p} {r = r} r≢p)

-- Main projection-safety theorem (left unproved for now).
projection-safe :
  ∀ {G : Global₀} {Δ₀ : Δ}
  → G ↾ Δ₀
  → safe Δ₀
projection-safe G↾Δ = {!!}

safe→SafeState :
  ∀ {Δ₀ : Δ}
  → safe Δ₀
  → SafeState Δ₀
safe→SafeState sΔ = sΔ rtc-refl

⊑-down-≤ :
  ∀ {Δ₀ Δ₁ : Δ} {G : Global₀}
  → Δ₀ ≤Δ Δ₁
  → Δ₁ ⊑ G
  → Δ₀ ⊑ G
⊑-down-≤ Δ₀≤Δ₁ (Δ' , (G↾Δ' , Δ₁≤Δ')) =
  Δ' , (G↾Δ' , ≤-trans-ctx Δ₀≤Δ₁ Δ₁≤Δ')

-- Helper 1 (to implement):
-- starting from an exact projection context step, produce
-- a matching global step and association for the target context.
proj-pres-step-from-↾ :
  ∀ {G : Global₀} {Δ₀ Δ₁ : Δ} {src dst : Participant} {Obs : Observable}
  → G ↾ Δ₀
  → Δ₀ -[ src ↝⟨ Obs ⟩ dst ]→₂ Δ₁
  → Σ Global₀ (λ G' → (G -[ src ↝⟨ Obs ⟩ dst ]→ᵍ G') × (Δ₁ ⊑ G'))
proj-pres-step-from-↾ G↾Δ₀ step = {!!}

-- Helper 2 (to implement):
-- transport projection of an uninvolved participant across one global step,
-- up to local subtyping.
proj-uninvolved-step-≤ :
  ∀ {G G' : Global₀} {src dst r : Participant} {Obs : Observable}
  {Tr : Local₀}
  → r ≢ src
  → r ≢ dst
  → G -[ src ↝⟨ Obs ⟩ dst ]→ᵍ G'
  → G ↾[ r ] Tr
  → Σ Local₀ (λ Tr' → (G' ↾[ r ] Tr') × (Tr ≤ Tr'))
proj-uninvolved-step-≤ r≢src r≢dst G→G' G↾r = {!!}

proj-pres-step :
  ∀ {G : Global₀} {Δ₀ Δ₁ : Δ} {src dst : Participant} {Obs : Observable}
  → Δ₀ ⊑ G
  → Δ₀ -[ src ↝⟨ Obs ⟩ dst ]→₂ Δ₁
  → Σ Global₀ (λ G' → (G -[ src ↝⟨ Obs ⟩ dst ]→ᵍ G') × (Δ₁ ⊑ G'))
proj-pres-step {G} {Δ₀} {Δ₁} {src} {dst} {Obs} (Δproj , (G↾Δproj , Δ₀≤Δproj)) step₀
  with stepSim≤-pair Δ₀≤Δproj
         (safe→SafeState (projection-safe G↾Δproj))
         step₀
... | Δproj' , (stepproj , Δ₁≤Δproj')
  with proj-pres-step-from-↾ G↾Δproj stepproj
... | G' , (G→G' , Δproj'⊑G') =
  G' , (G→G' , ⊑-down-≤ Δ₁≤Δproj' Δproj'⊑G')

-- Corollary using context-subtyping downward closure of safety.
⊑-safe :
  ∀ {G : Global₀} {Δ₀ : Δ}
  → Δ₀ ⊑ G
  → safe Δ₀
⊑-safe (Δ' , (G↾Δ' , Δ₀≤Δ')) =
  safe-downward-≤ Δ₀≤Δ' (projection-safe G↾Δ')
