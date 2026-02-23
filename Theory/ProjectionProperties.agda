{-# OPTIONS --safe --guardedness #-}

module Theory.ProjectionProperties (ℓ n : _) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Fin using (_≟_) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup; tabulate)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import Theory.MergeProjection as MP
import Theory.LocalSemanticProperties as LSP
import Semantics.LocalOperationalSemantics as LOS
import Semantics.GlobalOperationalSemantics as GOS
import Subtyping.SessionSubtypingProperties as SSP
import Syntax.WellFormedLocalTypes as WFLT

module M = MP ℓ n
module S = LSP ℓ n
module L = LOS ℓ n
module G = GOS ℓ n
module SubP = SSP ℓ n
module WFL = WFLT ℓ n

open M public using
  ( Global₀
  ; Δ
  ; Local₀
  ; Label
  ; Base
  ; send
  ; recv
  ; lookupM
  ; SendHeads
  ; RecvHeads
  ; send-none
  ; send-hit
  ; recv-none
  ; recv-hit
  ; Participant
  ; _≢_
  ; _⊑_
  )

open S public using
  ( safe
  ; SafeState
  ; rtc-refl
  ; _≤Δ_
  )

open SubP using (≤-trans-ctx)

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
  )

open G using
  ( GM-none
  ; GM-step
  ; GB-[]
  ; GB-∷
  ; _-[_]→ᵐ_
  ; _-[_]→ᵇ_
  )

open WFL using (updateΔ-self)

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

send-not-recv :
  ∀ {T : Local₀} {p : Participant} {Obs : Observable} {T₁ T₂ : Local₀}
  → T -[ p !⟨ Obs ⟩ ]→ₗ T₁
  → T -[ p ?⟨ Obs ⟩ ]→ₗ T₂
  → ⊥
send-not-recv LR1 ()
send-not-recv (LR3 _) ()
send-not-recv (LR5 s₁) (LR5 s₂) = send-not-recv s₁ s₂

gm-target-none→source-none :
  ∀ {ι : Interaction} {mG : Maybe Global₀}
  → mG -[ ι ]→ᵐ nothing
  → mG ≡ nothing
gm-target-none→source-none GM-none = refl

gm-source-just→target-just :
  ∀ {ι : Interaction} {G₀ : Global₀} {mG' : Maybe Global₀}
  → just G₀ -[ ι ]→ᵐ mG'
  → Σ Global₀ (λ G' → mG' ≡ just G')
gm-source-just→target-just (GM-step _) = _ , refl

send-head-none :
  ∀ {q : Participant} {b : Base} {M K : M.MergeSet} {l : Label}
  → SendHeads q b M K
  → lookupM l M ≡ nothing
  → lookupM l K ≡ nothing
send-head-none {q} {b} {M} {K} {l} SH hit =
  send-none-out (subst (λ x → M.SendEntry q b x (lookupM l K)) hit (SH l))
  where
    send-none-out :
      ∀ {X : Maybe Local₀}
      → M.SendEntry q b nothing X
      → X ≡ nothing
    send-none-out send-none = refl

recv-head-none :
  ∀ {q : Participant} {b : Base} {M K : M.MergeSet} {l : Label}
  → RecvHeads q b M K
  → lookupM l M ≡ nothing
  → lookupM l K ≡ nothing
recv-head-none {q} {b} {M} {K} {l} RH hit =
  recv-none-out (subst (λ x → M.RecvEntry q b x (lookupM l K)) hit (RH l))
  where
    recv-none-out :
      ∀ {X : Maybe Local₀}
      → M.RecvEntry q b nothing X
      → X ≡ nothing
    recv-none-out recv-none = refl

send-head-just :
  ∀ {q : Participant} {b : Base} {M K : M.MergeSet} {l : Label} {Ti : Local₀}
  → SendHeads q b M K
  → lookupM l M ≡ just Ti
  → Σ Local₀ (λ T → (Ti ≡ send q b T) × (lookupM l K ≡ just T))
send-head-just {q} {b} {M} {K} {l} {Ti} SH hit =
  send-just-out (subst (λ x → M.SendEntry q b x (lookupM l K)) hit (SH l))
  where
    send-just-out :
      ∀ {X : Maybe Local₀}
      → M.SendEntry q b (just Ti) X
      → Σ Local₀ (λ T → (Ti ≡ send q b T) × (X ≡ just T))
    send-just-out (send-hit {T}) = T , (refl , refl)

recv-head-just :
  ∀ {q : Participant} {b : Base} {M K : M.MergeSet} {l : Label} {Ti : Local₀}
  → RecvHeads q b M K
  → lookupM l M ≡ just Ti
  → Σ Local₀ (λ T → (Ti ≡ recv q b T) × (lookupM l K ≡ just T))
recv-head-just {q} {b} {M} {K} {l} {Ti} RH hit =
  recv-just-out (subst (λ x → M.RecvEntry q b x (lookupM l K)) hit (RH l))
  where
    recv-just-out :
      ∀ {X : Maybe Local₀}
      → M.RecvEntry q b (just Ti) X
      → Σ Local₀ (λ T → (Ti ≡ recv q b T) × (X ≡ just T))
    recv-just-out (recv-hit {T}) = T , (refl , refl)

branch-step-from-pointwise :
  ∀ {m} {bs bs' : Vec (Maybe Global₀) m} {ι : Interaction}
  → (∀ i → lookup bs i -[ ι ]→ᵐ lookup bs' i)
  → bs -[ ι ]→ᵇ bs'
branch-step-from-pointwise {m = zero} {bs = []} {bs' = []} f = GB-[]
branch-step-from-pointwise {m = suc m} {bs = x ∷ xs} {bs' = y ∷ ys} f =
  GB-∷ (f fzero)
       (branch-step-from-pointwise {m = m} {bs = xs} {bs' = ys}
         (λ i → f (fsuc i)))

branch-step-to-tabulate :
  ∀ {m} {bs : Vec (Maybe Global₀) m} {ι : Interaction}
  → (f : Data.Fin.Fin m → Maybe Global₀)
  → (∀ i → lookup bs i -[ ι ]→ᵐ f i)
  → bs -[ ι ]→ᵇ tabulate f
branch-step-to-tabulate {m = zero} {bs = []} f step = GB-[]
branch-step-to-tabulate {m = suc m} {bs = x ∷ xs} f step =
  GB-∷ (step fzero)
       (branch-step-to-tabulate {m = m} {bs = xs}
         (λ i → f (fsuc i))
         (λ i → step (fsuc i)))

sync-endpoints-distinct :
  ∀ {Δ₀ : Δ} {src dst : Participant} {Obs : Observable} {Ts' Td' : Local₀}
  → Δ₀ src -[ dst !⟨ Obs ⟩ ]→ₗ Ts'
  → Δ₀ dst -[ src ?⟨ Obs ⟩ ]→ₗ Td'
  → src ≢ dst
sync-endpoints-distinct {Δ₀} {src} {dst} {Obs} {Ts'} {Td'} pStep qStep eq =
  send-not-recv
    (subst (λ x → Δ₀ src -[ x !⟨ Obs ⟩ ]→ₗ Ts') (sym eq) pStep)
    (subst (λ x → Δ₀ x -[ src ?⟨ Obs ⟩ ]→ₗ Td') (sym eq) qStep)

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
