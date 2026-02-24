{-# OPTIONS --safe --guardedness #-}

module Theory.ProjectionSafety (ℓ n : _) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (_≟_) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Data.Vec.Properties using (lookup∘tabulate)
import Core.BranchTables as BT
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
  ; lookupGB
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
  ; M7
  ; unfold
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
  ; SendEntry
  ; send-none
  ; send-hit
  ; RecvEntry
  ; recv-none
  ; recv-hit
  ; SelEntry
  ; BraEntry
  ; SendHeads
  ; RecvHeads
  ; SelHeads
  ; BraHeads
  ; UnfoldOne
  ; unfold-one
  ; singletonL
  ; lookup-updateM-same
  ; lookup-updateM-other
  ; LabelwiseMerge
  ; MergeLabel
  ; ml-none
  ; ml-just
  ; SelDomainCommon
  ; BraDomainUnion
  ; collectLabel
  ; collectLabel-just
  ; collectLabel-nothing
  ; BranchSet
  ; lookupS
  ; AllJustAt
  ; AllNoneAt
  ; AnyJustAt
  ; wfMergeSet
  )
  renaming
  ( sel-none to msel-none
  ; sel-hit  to msel-hit
  ; bra-none to mbra-none
  ; bra-hit  to mbra-hit
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
  ; send-step-up-≤ₗ
  ; recv-step-up-any-≤ₗ
  ; recv-step-down-≤ₗ
  )

------------------------------------------------------------------------
-- Re-exports from SessionSubtypingProperties
------------------------------------------------------------------------

open SubP using
  ( ≤-refl
  ; ≤-refl-ctx
  ; ≤-trans
  ; ≤-trans-ctx
  ; SelM
  ; BraM
  ; SelDom≤
  ; BraDom≤
  )
  renaming
  ( sel-none to ssel-none
  ; sel-just to ssel-just
  ; bra-none to sbra-none
  ; bra-just to sbra-just
  )

------------------------------------------------------------------------
-- Re-exports from LocalOperationalSemantics
------------------------------------------------------------------------

open L using
  ( Observable
  ; Interaction
  ; obsBase
  ; obsLabel
  ; _!⟨_⟩
  ; _?⟨_⟩
  ; _↝⟨_⟩_
  ; _-[_]→ₗ_
  ; _-[_]→₂_
  ; _→₂_
  ; _→₂*_
  ; updateΔ
  ; LR1
  ; LR2
  ; LR3
  ; LR4
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

open WFG using
  ( wf-no-self-msg
  ; wf-no-self-choice
  )
  renaming (wf to wfG)

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

just-injective : ∀ {A : Set} {x y : A} → _≡_ {_} {Maybe A} (just x) (just y) → x ≡ y
just-injective refl = refl

------------------------------------------------------------------------
-- Planned merge/subtyping bridge (used by PR6)
--
-- Strategy: Comp pattern (like ≤-trans).
--   1. MBranch packages (M Π T) + (lookupM l M ≡ just Tₗ)
--   2. mb-step is purely inductive (fuel decreases on M2/l≠l₀)
--      and produces Step RM T Tₗ where RM X Y = ▹ (MBranch X Y)
--   3. ≤-from-mb is purely coinductive (all recursive calls guarded)
------------------------------------------------------------------------

private
  -- Helper: extract continuation from SendEntry
  sendHit-inv :
    ∀ {q : Participant} {b : Base} {a1 a2 : Maybe Local₀} {Tₗ : Local₀}
    → SendEntry q b a1 a2
    → a1 ≡ just Tₗ
    → Σ Local₀ (λ Tc → (Tₗ ≡ send q b Tc) × (a2 ≡ just Tc))
  sendHit-inv send-hit refl = _ , refl , refl

  -- Helper: extract continuation from RecvEntry
  recvHit-inv :
    ∀ {q : Participant} {b : Base} {a1 a2 : Maybe Local₀} {Tₗ : Local₀}
    → RecvEntry q b a1 a2
    → a1 ≡ just Tₗ
    → Σ Local₀ (λ Tc → (Tₗ ≡ recv q b Tc) × (a2 ≡ just Tc))
  recvHit-inv recv-hit refl = _ , refl , refl

  -- Helper: extract branch table from SelEntry
  selHit-inv :
    ∀ {q : Participant} {a1 : Maybe Local₀} {a2 : Maybe MergeSet} {Tₗ : Local₀}
    → SelEntry q a1 a2
    → a1 ≡ just Tₗ
    → Σ MergeSet (λ bsₗ → (Tₗ ≡ sel q bsₗ) × (a2 ≡ just bsₗ))
  selHit-inv msel-hit refl = _ , refl , refl

  -- Helper: extract branch table from BraEntry
  braHit-inv :
    ∀ {q : Participant} {a1 : Maybe Local₀} {a2 : Maybe MergeSet} {Tₗ : Local₀}
    → BraEntry q a1 a2
    → a1 ≡ just Tₗ
    → Σ MergeSet (λ bsₗ → (Tₗ ≡ bra q bsₗ) × (a2 ≡ just bsₗ))
  braHit-inv mbra-hit refl = _ , refl , refl

  -- Helper: singleton lookup gives the stored value
  singleton-inv :
    ∀ {l l₀ : Label} {Tₗ : Local₀}
    → lookupM l (singletonL l₀ end) ≡ just Tₗ
    → Tₗ ≡ end
  singleton-inv {l} {l₀} {Tₗ} hit with l ≟ l₀
  ... | yes refl = just-injective (trans (sym hit) (BT.singleton-same {n = ℓ} {l = l} {x = end}))
  ... | no l≢l₀ = ⊥-elim (just≢nothing (trans (sym hit) (BT.singleton-other {n = ℓ} {l = l₀} {x = end} l≢l₀)))

-- Intermediate data type packaging merge proof + branch lookup
data MBranch : Local₀ → Local₀ → Set where
  mb : ∀ {M : MergeSet} {T : Local₀} {l : Label} {Tₗ : Local₀}
     → M Π T → lookupM l M ≡ just Tₗ → MBranch T Tₗ

private
  RM : Local₀ → Local₀ → Set
  RM X Y = ▹ (MBranch X Y)

mb-wf-left : ∀ {T Tₗ} → MBranch T Tₗ → Sub.wf T
mb-wf-left (mb mΠT _) = wf-merged mΠT

mb-wf-right : ∀ {T Tₗ} → MBranch T Tₗ → Sub.wf Tₗ
mb-wf-right (mb mΠT hit) = wf-set mΠT hit

-- Purely inductive: fuel decreases on M2/l≠l₀, all other branches just package data
mb-step :
  ℕ → ∀ {T Tₗ : Local₀} → MBranch T Tₗ → Step RM T Tₗ

mb-step (suc fuel) (mb {l = l} mΠT hit) with outΠ mΠT

-- M1: singleton end → s-end
mb-step (suc fuel) (mb {l = l} mΠT hit) | M1 {l = l₀} =
  subst (Step _ end) (sym (singleton-inv hit)) s-end

-- M2: unfold one entry in merge set
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M2 (unfold-one {l = l₀} {body = body} eq) sub with l ≟ l₀
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M2 (unfold-one {body = body} eq) sub | yes refl
  rewrite just-injective (trans (sym hit) eq) =
  s-muR (next (mb (force sub) lookup-updateM-same))
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M2 (unfold-one eq) sub | no l≠l₀ =
  mb-step fuel (mb (force sub) (trans (lookup-updateM-other l≠l₀) hit))

-- M3: all entries are send q b _, merged is send q b T'
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M3 {K = K} {q = q} {b = b} {T = T'} heads sub
  with sendHit-inv (heads l) hit
... | Tc , eq , hitK =
  subst (Step _ (send q b T')) (sym eq)
    (s-send (next (mb (force sub) hitK)))

-- M4: all entries are recv q b _, merged is recv q b T'
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M4 {K = K} {q = q} {b = b} {T = T'} heads sub
  with recvHit-inv (heads l) hit
... | Tc , eq , hitK =
  subst (Step _ (recv q b T')) (sym eq)
    (s-recv (next (mb (force sub) hitK)))

-- M5: selection (intersection of domains)
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M5 {S = S} {q = q} {bs = bs} heads dom lm
  with selHit-inv (heads l) hit
... | bsₗ , eq , hitS =
  subst (Step _ (sel q bs)) (sym eq) (s-sel sel-dom)
  where
    bsJust→allJust = proj₁ (proj₂ (proj₂ dom))

    sel-dom : SelDom≤ RM bs bsₗ
    sel-dom l' with lookupM l' bs in eqBs | lm l'
    ... | nothing | _  = ssel-none
    ... | just T' | ml-just delaySub =
      let allJ    = bsJust→allJust eqBs
          T'ₗ-pf  = allJ hitS
          T'ₗ     = proj₁ T'ₗ-pf
          hitBsₗ  = proj₂ T'ₗ-pf
          clHit   = trans (collectLabel-just {l = l'} {l₀ = l} {S = S} hitS) hitBsₗ
      in subst (SelM RM (just T')) (sym hitBsₗ)
           (ssel-just (next (mb (force delaySub) clHit)))

-- M6: branching (union of domains)
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M6 {S = S} {q = q} {bs = bs} heads dom lm
  with braHit-inv (heads l) hit
... | bsₗ , eq , hitS =
  subst (Step _ (bra q bs)) (sym eq) (s-bra bra-dom)
  where
    anyJust→bsJust = proj₁ dom
    bsNone→allNone = proj₂ (proj₂ (proj₂ dom))

    bra-dom : BraDom≤ RM bs bsₗ
    bra-dom l' with lookupM l' bsₗ in eqBsₗ
    ... | nothing = sbra-none
    ... | just T'ₗ with lookupM l' bs in eqBs | lm l'
    ...   | nothing | _ =
      let allN = bsNone→allNone l' eqBs
      in ⊥-elim (just≢nothing (trans (sym eqBsₗ) (allN hitS)))
    ...   | just T' | ml-just delaySub =
      sbra-just (next (mb (force delaySub) (trans (collectLabel-just {l = l'} {l₀ = l} {S = S} hitS) eqBsₗ)))

-- M7: unfold merged type (mu body → unfold (mu body))
mb-step (suc fuel) (mb {l = l} mΠT hit)
  | M7 {body = body} sub =
  s-muL (next (mb (force sub) hit))

-- Zero fuel: M2/l≠l₀ should be impossible (all mus unfolded)
mb-step zero m = {!!}

-- Purely coinductive: converts MBranch to ≤
≤-from-mb : ∀ {T Tₗ : Local₀} → MBranch T Tₗ → T ≤ Tₗ
wf-left  (≤-from-mb m) = mb-wf-left m
wf-right (≤-from-mb m) = mb-wf-right m
out (≤-from-mb m) with mb-step ℓ m
... | s-end = s-end
... | s-send r = s-send (record { force = ≤-from-mb (force r) })
... | s-recv r = s-recv (record { force = ≤-from-mb (force r) })
... | s-sel rs = s-sel (λ l → mapSel (rs l))
  where
    mapSel : ∀ {a b : Maybe Local₀} → SelM RM a b → SelM (λ X Y → ▹ (X ≤ Y)) a b
    mapSel ssel-none = ssel-none
    mapSel (ssel-just r) = ssel-just (record { force = ≤-from-mb (force r) })
... | s-bra rs = s-bra (λ l → mapBra (rs l))
  where
    mapBra : ∀ {a b : Maybe Local₀} → BraM RM a b → BraM (λ X Y → ▹ (X ≤ Y)) a b
    mapBra sbra-none = sbra-none
    mapBra (sbra-just r) = sbra-just (record { force = ≤-from-mb (force r) })
... | s-muL r = s-muL (record { force = ≤-from-mb (force r) })
... | s-muR r = s-muR (record { force = ≤-from-mb (force r) })

merge-≤-branch :
  ∀ {Mset : MergeSet} {T : Local₀} {l : Label} {Tₗ : Local₀}
  → Mset Π T
  → lookupM l Mset ≡ just Tₗ
  → T ≤ Tₗ
merge-≤-branch mΠT hit = ≤-from-mb (mb mΠT hit)

CanSync₂-from-local :
  ∀ {Δ₀ : Δ} {p q : Participant} {U : Observable} {Tp' Tq' : Local₀}
  → Δ₀ p -[ q !⟨ U ⟩ ]→ₗ Tp'
  → Δ₀ q -[ p ?⟨ U ⟩ ]→ₗ Tq'
  → CanSync₂ Δ₀ p q U
CanSync₂-from-local {Δ₀} {p} {q} {U} pStep qStep =
  _ , LEnv (LTag pStep) (LTag qStep)

global-branch-hit :
  ∀ {p : Participant} {bs : G.Branches 0} {lbs : MergeSet}
    {l : Label} {T : Local₀}
  → BranchProj p bs lbs
  → lookupM l lbs ≡ just T
  → Σ Global₀ (λ Gi → lookupGB l bs ≡ just Gi)
global-branch-hit {bs = bs} {l = l} bp lHit with lookupGB l bs in eq
... | nothing = ⊥-elim (just≢nothing (trans (sym lHit) (proj₂ bp l eq)))
... | just Gi = Gi , refl

recv-from-msg-dst :
  ∀ {p q : Participant} {b : Base} {G' : Global₀}
    {Tq : Local₀} {U' : Observable} {Tq' : Local₀}
  → msg p q b G' ↾[ q ] Tq
  → Tq -[ p ?⟨ U' ⟩ ]→ₗ Tq'
  → Σ Local₀ (λ Tq'' → Tq -[ p ?⟨ obsBase b ⟩ ]→ₗ Tq'')
recv-from-msg-dst {p = p} {q = q} {b = b} qProj LR2 with out↾ qProj
... | PR2 {T = Tq''} sub = Tq'' , LR2
... | PR3 _ q≢q _ = ⊥-elim (q≢q refl)
recv-from-msg-dst qProj (LR5 step) with out↾ qProj
... | PR8 sub =
  let rec = recv-from-msg-dst (force sub) step in
  proj₁ rec , LR5 (proj₂ rec)
... | PR3 _ q≢q _ = ⊥-elim (q≢q refl)
recv-from-msg-dst qProj (LR4 hit) with out↾ qProj
... | PR3 _ q≢q _ = ⊥-elim (q≢q refl)

recv-from-choice-dst :
  ∀ {p q : Participant} {bs : G.Branches 0} {l : Label} {Gi : Global₀}
    {Tq : Local₀} {U' : Observable} {Tq' : Local₀}
  → lookupGB l bs ≡ just Gi
  → choice p q bs ↾[ q ] Tq
  → Tq -[ p ?⟨ U' ⟩ ]→ₗ Tq'
  → Σ Local₀ (λ Tq'' → Tq -[ p ?⟨ obsLabel l ⟩ ]→ₗ Tq'')
recv-from-choice-dst {p = p} {q = q} hitG qProj (LR4 hit) with out↾ qProj
... | PR5 {lbs = lbs} bp =
  let rec = proj₁ bp hitG in
  proj₁ rec , LR4 (proj₁ (proj₂ rec))
... | PR6 _ q≢q _ _ = ⊥-elim (q≢q refl)
recv-from-choice-dst hitG qProj (LR5 step) with out↾ qProj
... | PR8 sub =
  let rec = recv-from-choice-dst hitG (force sub) step in
  proj₁ rec , LR5 (proj₂ rec)
... | PR6 _ q≢q _ _ = ⊥-elim (q≢q refl)
recv-from-choice-dst {q = q} hitG qProj LR2 with out↾ qProj
... | PR6 _ q≢q _ _ = ⊥-elim (q≢q refl)

sync-from-pr4 :
  ∀ {p q : Participant} {bs : G.Branches 0} {lbs : MergeSet}
    {l : Label} {Tp : Local₀}
    {Tq : Local₀} {U' : Observable} {Tq' : Local₀}
  → BranchProj p bs lbs
  → lookupM l lbs ≡ just Tp
  → choice p q bs ↾[ q ] Tq
  → Tq -[ p ?⟨ U' ⟩ ]→ₗ Tq'
  → Σ Local₀ (λ Tq'' → Tq -[ p ?⟨ obsLabel l ⟩ ]→ₗ Tq'')
sync-from-pr4 {bs = bs} {lbs = lbs} {l = l} bp hit qProj qLoc
  with global-branch-hit {bs = bs} {lbs = lbs} {l = l} bp hit
... | Gi , hitG =
  recv-from-choice-dst {bs = bs} {l = l} {Gi = Gi} hitG qProj qLoc

msg-cont-proj-recv :
  ∀ {s t : Participant} {b : Base} {G' : Global₀}
    {r src : Participant}
    {Tr : Local₀} {U' : Observable} {Tr' : Local₀}
  → src ≢ s
  → msg s t b G' ↾[ r ] Tr
  → Tr -[ src ?⟨ U' ⟩ ]→ₗ Tr'
  → G' ↾[ r ] Tr
msg-cont-proj-recv src≢s rProj rStep with out↾ rProj | rStep
... | PR2 _ | LR2 = ⊥-elim (src≢s refl)
... | PR3 _ _ sub | LR2 = force sub
... | PR3 _ _ sub | LR4 hit = force sub
... | PR3 _ _ sub | LR5 step = force sub
... | PR8 sub | LR5 step =
  let rec = msg-cont-proj-recv src≢s (force sub) step in
  roll↾ (wf-global rec) (wf-local rProj) (PR8 (next rec))

gmu-unfold-proj-recv :
  ∀ {body : G.Global (suc zero)}
    {r src : Participant}
    {Tr : Local₀} {U' : Observable} {Tr' : Local₀}
  → gmu body ↾[ r ] Tr
  → Tr -[ src ?⟨ U' ⟩ ]→ₗ Tr'
  → unfoldG (gmu body) ↾[ r ] Tr
gmu-unfold-proj-recv rProj rStep with out↾ rProj | rStep
... | PR7 _ sub | LR2 = force sub
... | PR7 _ sub | LR4 hit = force sub
... | PR7 _ sub | LR5 step = force sub
... | PR8 sub | LR5 step =
  let rec = gmu-unfold-proj-recv (force sub) step in
  roll↾ (wf-global rec) (wf-local rProj) (PR8 (next rec))

choice-branch-lift-recv :
  ∀ {s t q p : Participant}
    {bs : G.Branches 0} {l : Label} {Gi : Global₀}
    {Tq : Local₀} {U U' : Observable} {Tq' : Local₀}
  → p ≢ s
  → p ≢ t
  → lookupGB l bs ≡ just Gi
  → choice s t bs ↾[ q ] Tq
  → Tq -[ p ?⟨ U' ⟩ ]→ₗ Tq'
  → Σ Local₀ (λ Tqi →
      (Gi ↾[ q ] Tqi)
      ×
      (Σ Observable (λ V → Σ Local₀ (λ Tqi' → Tqi -[ p ?⟨ V ⟩ ]→ₗ Tqi'))
       ×
       (∀ {Tsync}
        → Tqi -[ p ?⟨ U ⟩ ]→ₗ Tsync
        → Σ Local₀ (λ Tqsync → Tq -[ p ?⟨ U ⟩ ]→ₗ Tqsync))))
choice-branch-lift-recv {s = s} {t = t} {q = q} {p = p}
                        {l = l} {Gi = Gi} {Tq = Tq} {U = U}
                        p≢s p≢t hitG qProj qLoc
  with out↾ qProj | qLoc
... | PR6 {M = Mq} _ _ bpq mΠq | qStep =
  let qInfo  = proj₁ bpq hitG
      Tqi    = proj₁ qInfo
      hitQ   = proj₁ (proj₂ qInfo)
      qGi    = force (proj₂ (proj₂ qInfo))
      q≤Tqi  = merge-≤-branch (force mΠq) hitQ
      upStep = recv-step-up-any-≤ₗ q≤Tqi qStep
      back   : ∀ {Tsync}
             → Tqi -[ p ?⟨ U ⟩ ]→ₗ Tsync
             → Σ Local₀ (λ Tqsync → Tq -[ p ?⟨ U ⟩ ]→ₗ Tqsync)
      back sync = recv-step-down-≤ₗ q≤Tqi sync
  in Tqi , (qGi , (upStep , back))
... | PR5 _ | LR4 _ = ⊥-elim (p≢s refl)
... | PR8 sub | LR5 step with choice-branch-lift-recv p≢s p≢t hitG (force sub) step
...   | Tqi , (qGi , (upStep , backUnf)) =
    let back : ∀ {Tsync}
             → Tqi -[ p ?⟨ U ⟩ ]→ₗ Tsync
             → Σ Local₀ (λ Tqsync → Tq -[ p ?⟨ U ⟩ ]→ₗ Tqsync)
        back sync =
          let r = backUnf sync in
          proj₁ r , LR5 (proj₂ r)
    in Tqi , (qGi , (upStep , back))

------------------------------------------------------------------------
-- Task 3: SafeState from exact projection
------------------------------------------------------------------------

safeState-from-↾ :
  ∀ {G : Global₀} {Δ₀ : Δ}
  → G ↾ Δ₀
  → SafeState Δ₀
safeState-from-↾ {G = G} {Δ₀ = Δ₀} G↾Δ {p} {q} {U} {U'} {Δp} {Δq}
                 (LTag pStep) (LTag qStep) =
  lift (safeState-local (wf-global (G↾Δ p)) (G↾Δ p) (G↾Δ q) pStep qStep)
  where
    lift :
      Σ Local₀ (λ Tq'' → Δ₀ q -[ p ?⟨ U ⟩ ]→ₗ Tq'')
      → CanSync₂ Δ₀ p q U
    lift (Tq'' , qStep') = CanSync₂-from-local pStep qStep'

    safeState-local :
      ∀ {G' : Global₀} {Tp Tq Tp' Tq'} {U U' : Observable}
      → wfG G'
      → G' ↾[ p ] Tp
      → G' ↾[ q ] Tq
      → Tp -[ q !⟨ U ⟩ ]→ₗ Tp'
      → Tq -[ p ?⟨ U' ⟩ ]→ₗ Tq'
      → Σ Local₀ (λ Tq'' → Tq -[ p ?⟨ U ⟩ ]→ₗ Tq'')

    safeState-local {U = U} wG' pProj qProj pLoc qLoc with out↾ pProj | pLoc | wG'
    ... | PR1 {p = p} {q = q} {b = b} sub | LR1 | WFG.wf-msg _ wG'' =
      let rec = recv-from-msg-dst qProj qLoc in
      proj₁ rec , proj₂ rec
    ... | PR3 {q = s} {r = t} p≢s p≢t sub | pLoc | WFG.wf-msg _ wG'' =
      safeState-local wG''
                      (force sub)
                      (msg-cont-proj-recv {s = s} {t = t} p≢s qProj qLoc)
                      pLoc
                      qLoc
    ... | PR4 {bs = bs} {lbs = lbs} bp | LR3 {l = l} hit | WFG.wf-choice _ _ _ =
      sync-from-pr4 {bs = bs} {lbs = lbs} {l = l} bp hit qProj qLoc
    ... | PR6 p≢s p≢t bp mΠ
      | pLoc
      | WFG.wf-choice _ ne wbs =
      let l₀   = proj₁ ne
          Gi   = proj₁ (proj₂ ne)
          hitG = proj₂ (proj₂ ne)
          pInfo = proj₁ bp hitG
          Tpi   = proj₁ pInfo
          hitP  = proj₁ (proj₂ pInfo)
          pGi   = force (proj₂ (proj₂ pInfo))
          p≤Tpi = merge-≤-branch (force mΠ) hitP
          pUp   = send-step-up-≤ₗ p≤Tpi pLoc
          pStepᵢ = proj₂ pUp
          qInfo = choice-branch-lift-recv {l = l₀} {Gi = Gi} {U = U}
                                       p≢s p≢t hitG qProj qLoc
          Tqi   = proj₁ qInfo
          qGi   = proj₁ (proj₂ qInfo)
          qUp   = proj₁ (proj₂ (proj₂ qInfo))
          qStepᵢ = proj₂ (proj₂ qUp)
          down  = proj₂ (proj₂ (proj₂ qInfo))
          wGi   = wbs hitG
          rec   = safeState-local wGi pGi qGi pStepᵢ qStepᵢ
      in down (proj₂ rec)
    ... | PR7 {body = body} ptp sub | pLoc | WFG.wf-mu _ wUnf =
      safeState-local wUnf
                      (force sub)
                      (gmu-unfold-proj-recv {body = body} qProj qLoc)
                      pLoc
                      qLoc
    ... | PR8 sub | LR5 step | wG'' =
      safeState-local wG'' (force sub) qProj step qLoc

------------------------------------------------------------------------
-- Task 5: Forward simulation (exact projection preserved up to ≤Δ)
------------------------------------------------------------------------

sim-↾ :
  ∀ {G : Global₀} {Δ₁ Δ₁' : Δ} {ι : Interaction}
  → G ↾ Δ₁
  → Δ₁ -[ ι ]→₂ Δ₁'
  → Σ Global₀ (λ G' →
    Σ Δ (λ Δ₂ →
      (G →ᵍ* G') × (G' ↾ Δ₂) × (Δ₁' ≤Δ Δ₂)))
sim-↾ G↾Δ₁ step = {!!}

------------------------------------------------------------------------
-- Low-risk derived layer (Tasks 4/6/7), parameterised by core lemmas
------------------------------------------------------------------------

safeState-from-⊑ :
  (safeState-from-↾ :
    ∀ {G : Global₀} {Δ₀ : Δ}
    → G ↾ Δ₀
    → SafeState Δ₀)
  → ∀ {G : Global₀} {Δ₀ : Δ}
  → Δ₀ ⊑ G
  → SafeState Δ₀
safeState-from-⊑ safeState-from-↾ (Δ' , G↾Δ' , Δ₀≤Δ') =
  safeStateDownward Δ₀≤Δ' (safeState-from-↾ G↾Δ')

sim-⊑ :
  (safeState-from-↾ :
    ∀ {G : Global₀} {Δ₀ : Δ}
    → G ↾ Δ₀
    → SafeState Δ₀)
  (sim-↾ :
    ∀ {G : Global₀} {Δ₁ Δ₁' : Δ} {ι : Interaction}
    → G ↾ Δ₁
    → Δ₁ -[ ι ]→₂ Δ₁'
    → Σ Global₀ (λ G' →
      Σ Δ (λ Δ₂ →
        (G →ᵍ* G') × (G' ↾ Δ₂) × (Δ₁' ≤Δ Δ₂))))
  → ∀ {G : Global₀} {Δ₀ Δ₀' : Δ}
  → Δ₀ ⊑ G
  → Δ₀ →₂ Δ₀'
  → Σ Global₀ (λ G' → Δ₀' ⊑ G')
sim-⊑ safeState-from-↾ sim-↾ {G}
      (Δ₁ , G↾Δ₁ , Δ₀≤Δ₁) step
  with stepSim≤ Δ₀≤Δ₁ (safeState-from-↾ G↾Δ₁) step
... | Δ₁' , (step₁ , Δ₀'≤Δ₁')
  with step₁
... | ι , red₁
  with sim-↾ G↾Δ₁ red₁
... | G' , Δ₂ , (G→*G' , G'↾Δ₂ , Δ₁'≤Δ₂) =
  G' , (Δ₂ , G'↾Δ₂ , ≤-trans-ctx Δ₀'≤Δ₁' Δ₁'≤Δ₂)

walk-⊑ :
  (safeState-from-↾ :
    ∀ {G : Global₀} {Δ₀ : Δ}
    → G ↾ Δ₀
    → SafeState Δ₀)
  (sim-↾ :
    ∀ {G : Global₀} {Δ₁ Δ₁' : Δ} {ι : Interaction}
    → G ↾ Δ₁
    → Δ₁ -[ ι ]→₂ Δ₁'
    → Σ Global₀ (λ G' →
      Σ Δ (λ Δ₂ →
        (G →ᵍ* G') × (G' ↾ Δ₂) × (Δ₁' ≤Δ Δ₂))))
  → ∀ {G : Global₀} {Δ₀ Δ₂ : Δ}
  → Δ₀ ⊑ G
  → Δ₀ →₂* Δ₂
  → Σ Global₀ (λ G' → Δ₂ ⊑ G')
walk-⊑ safeState-from-↾ sim-↾ {G} Δ₀⊑G rtc-refl = G , Δ₀⊑G
walk-⊑ safeState-from-↾ sim-↾ Δ₀⊑G (rtc-step step rest)
  with sim-⊑ safeState-from-↾ sim-↾ Δ₀⊑G step
... | G' , Δ₀'⊑G' =
  walk-⊑ safeState-from-↾ sim-↾ Δ₀'⊑G' rest

safe-from-↾ :
  (safeState-from-↾ :
    ∀ {G : Global₀} {Δ₀ : Δ}
    → G ↾ Δ₀
    → SafeState Δ₀)
  (sim-↾ :
    ∀ {G : Global₀} {Δ₁ Δ₁' : Δ} {ι : Interaction}
    → G ↾ Δ₁
    → Δ₁ -[ ι ]→₂ Δ₁'
    → Σ Global₀ (λ G' →
      Σ Δ (λ Δ₂ →
        (G →ᵍ* G') × (G' ↾ Δ₂) × (Δ₁' ≤Δ Δ₂))))
  → ∀ {G : Global₀} {Δ₀ : Δ}
  → G ↾ Δ₀
  → safe Δ₀
safe-from-↾ safeState-from-↾ sim-↾ {G} {Δ₀} G↾Δ₀ {Δ₂} Δ₀→*Δ₂ =
  safeState-from-⊑ safeState-from-↾
    (proj₂ (walk-⊑ safeState-from-↾ sim-↾ initial Δ₀→*Δ₂))
  where
    wfΔ₀ : wfΔ Δ₀
    wfΔ₀ p = wf-local (G↾Δ₀ p)

    initial : Δ₀ ⊑ G
    initial = Δ₀ , (G↾Δ₀ , ≤-refl-ctx wfΔ₀)

------------------------------------------------------------------------
-- Main theorem: any projected context is safe
------------------------------------------------------------------------

safe-from-projection :
  ∀ {G : Global₀} {Δ₀ : Δ}
  → G ↾ Δ₀
  → safe Δ₀
safe-from-projection = safe-from-↾ safeState-from-↾ sim-↾
