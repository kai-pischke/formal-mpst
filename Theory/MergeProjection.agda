{-# OPTIONS --safe --guardedness #-}

module Theory.MergeProjection (ℓ n : _) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (_≟_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Vec using (Vec; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Core.BranchTables as BT
import Syntax.LocalSessionTypes as LTS
import Syntax.GlobalSessionTypes as GTS
import Theory.WellFormedLocalTypes as WFL
import Theory.WellFormedGlobalTypes as WFG
import Theory.SessionSubtyping as SUB

module L = LTS ℓ n
module G = GTS ℓ n
module W = WFL ℓ n
module WG = WFG ℓ n
module Sub = SUB ℓ n

open L public using
  ( Label
  ; Participant
  ; Base
  ; _≢_
  ; Local
  ; Local₀
  ; Δ
  ; end
  ; send
  ; recv
  ; sel
  ; bra
  ; mu
  ; unfold
  )
  renaming
  ( Branches to LBranches
  ; singleton to singletonL
  )

open G public using
  ( Global
  ; Global₀
  ; msg
  ; choice
  )
  renaming
  ( end to gend
  ; mu to gmu
  ; Branches to GBranches
  ; lookupB to lookupGB
  ; unfold to unfoldG
  )

open W public using ()
open WG public using ()
open Sub public using (_≤Δ_)

------------------------------------------------------------------------
-- Small delay modality (coinductive relations use guarded premises).
------------------------------------------------------------------------

record ▹ (A : Set) : Set where
  coinductive
  field force : A
open ▹ public

next : ∀ {A : Set} → A → ▹ A
force (next a) = a

------------------------------------------------------------------------
-- Finite-set encodings used by merge/projection.
------------------------------------------------------------------------

MergeSet : Set
MergeSet = LBranches 0

-- Per-element branch tables (used for M5/M6).
BranchSet : Set
BranchSet = Vec (Maybe MergeSet) ℓ

lookupM : Label → MergeSet → Maybe Local₀
lookupM = BT.lookupB

lookupS : Label → BranchSet → Maybe MergeSet
lookupS = BT.lookupB

updM : Label → Maybe Local₀ → MergeSet → Label → Maybe Local₀
updM l x M l' with l' ≟ l
... | yes _ = x
... | no  _ = lookupM l' M

updateM : Label → Maybe Local₀ → MergeSet → MergeSet
updateM l x M = tabulate (updM l x M)

lookup-updateM-same :
  ∀ {l : Label} {x : Maybe Local₀} {M : MergeSet}
  → lookupM l (updateM l x M) ≡ x
lookup-updateM-same {l} {x} {M}
  rewrite lookup∘tabulate (updM l x M) l
  with l ≟ l
... | yes _ = refl
... | no l≢l = ⊥-elim (l≢l refl)

lookup-updateM-other :
  ∀ {l l' : Label} {x : Maybe Local₀} {M : MergeSet}
  → l' ≢ l
  → lookupM l' (updateM l x M) ≡ lookupM l' M
lookup-updateM-other {l} {l'} {x} {M} l'≢l
  rewrite lookup∘tabulate (updM l x M) l'
  with l' ≟ l
... | yes eq = ⊥-elim (l'≢l eq)
... | no _ = refl

collectLabel : Label → BranchSet → MergeSet
collectLabel l S = tabulate pick
  where
    pick : Label → Maybe Local₀
    pick i with lookupS i S
    ... | nothing  = nothing
    ... | just bsᵢ = lookupM l bsᵢ

wfMergeSet : MergeSet → Set
wfMergeSet M =
  ∀ {l T}
  → lookupM l M ≡ just T
  → W.wf T

wfBranchSet : BranchSet → Set
wfBranchSet S =
  ∀ {l M}
  → lookupS l S ≡ just M
  → wfMergeSet M

------------------------------------------------------------------------
-- Side-conditions for merge rules.
------------------------------------------------------------------------

data SendEntry (q : Participant) (b : Base)
              : Maybe Local₀ → Maybe Local₀ → Set where
  send-none : SendEntry q b nothing nothing
  send-hit  : ∀ {T} → SendEntry q b (just (send q b T)) (just T)

SendHeads : Participant → Base → MergeSet → MergeSet → Set
SendHeads q b M K = ∀ l → SendEntry q b (lookupM l M) (lookupM l K)

data RecvEntry (q : Participant) (b : Base)
              : Maybe Local₀ → Maybe Local₀ → Set where
  recv-none : RecvEntry q b nothing nothing
  recv-hit  : ∀ {T} → RecvEntry q b (just (recv q b T)) (just T)

RecvHeads : Participant → Base → MergeSet → MergeSet → Set
RecvHeads q b M K = ∀ l → RecvEntry q b (lookupM l M) (lookupM l K)

data SelEntry (q : Participant)
             : Maybe Local₀ → Maybe MergeSet → Set where
  sel-none : SelEntry q nothing nothing
  sel-hit  : ∀ {bs} → SelEntry q (just (sel q bs)) (just bs)

SelHeads : Participant → MergeSet → BranchSet → Set
SelHeads q M S = ∀ l → SelEntry q (lookupM l M) (lookupS l S)

data BraEntry (q : Participant)
             : Maybe Local₀ → Maybe MergeSet → Set where
  bra-none : BraEntry q nothing nothing
  bra-hit  : ∀ {bs} → BraEntry q (just (bra q bs)) (just bs)

BraHeads : Participant → MergeSet → BranchSet → Set
BraHeads q M S = ∀ l → BraEntry q (lookupM l M) (lookupS l S)

AllNoneAt : Label → BranchSet → Set
AllNoneAt l S =
  ∀ {i bsᵢ}
  → lookupS i S ≡ just bsᵢ
  → lookupM l bsᵢ ≡ nothing

AllJustAt : Label → BranchSet → Set
AllJustAt l S =
  ∀ {i bsᵢ}
  → lookupS i S ≡ just bsᵢ
  → Σ Local₀ (λ T → lookupM l bsᵢ ≡ just T)

AnyJustAt : Label → BranchSet → Set
AnyJustAt l S =
  Σ Label (λ i →
  Σ MergeSet (λ bsᵢ →
    (lookupS i S ≡ just bsᵢ) ×
    Σ Local₀ (λ T → lookupM l bsᵢ ≡ just T)))

SelDomainCommon : BranchSet → MergeSet → Set
SelDomainCommon S bs =
  (∀ l
   → AllNoneAt l S
   → lookupM l bs ≡ nothing)
  ×
  (∀ l
   → AllJustAt l S
   → Σ Local₀ (λ T → lookupM l bs ≡ just T))
  ×
  (∀ {l T}
   → lookupM l bs ≡ just T
   → AllJustAt l S)
  ×
  (∀ l
   → lookupM l bs ≡ nothing
   → AllNoneAt l S)

BraDomainUnion : BranchSet → MergeSet → Set
BraDomainUnion S bs =
  (∀ l
   → AnyJustAt l S
   → Σ Local₀ (λ T → lookupM l bs ≡ just T))
  ×
  (∀ l
   → AllNoneAt l S
   → lookupM l bs ≡ nothing)
  ×
  (∀ {l T}
   → lookupM l bs ≡ just T
   → AnyJustAt l S)
  ×
  (∀ l
   → lookupM l bs ≡ nothing
   → AllNoneAt l S)

------------------------------------------------------------------------
-- (1) Coinductive merge relation: M Π T
------------------------------------------------------------------------

infix 4 _Π_

mutual
  record _Π_ (M : MergeSet) (T : Local₀) : Set where
    coinductive
    field
      wf-set    : wfMergeSet M
      wf-merged : W.wf T
      outΠ      : MergeStep M T

  data MergeLabel (M : MergeSet) : Maybe Local₀ → Set where
    ml-none : MergeLabel M nothing
    ml-just : ∀ {T} → ▹ (M Π T) → MergeLabel M (just T)

  LabelwiseMerge : BranchSet → MergeSet → Set
  LabelwiseMerge S bs = ∀ l → MergeLabel (collectLabel l S) (lookupM l bs)

  data UnfoldOne : MergeSet → MergeSet → Set where
    unfold-one :
      ∀ {M l body}
      → lookupM l M ≡ just (mu body)
      → UnfoldOne M (updateM l (just (unfold (mu body))) M)

  data MergeStep : MergeSet → Local₀ → Set where
    -- [M1]
    M1 :
      ∀ {l}
      → MergeStep (singletonL l end) end

    -- [M2]
    M2 :
      ∀ {M M' T}
      → UnfoldOne M M'
      → ▹ (M' Π T)
      → MergeStep M T

    -- [M3]
    M3 :
      ∀ {M K q b T}
      → SendHeads q b M K
      → ▹ (K Π T)
      → MergeStep M (send q b T)

    -- [M4]
    M4 :
      ∀ {M K q b T}
      → RecvHeads q b M K
      → ▹ (K Π T)
      → MergeStep M (recv q b T)

    -- [M5]
    M5 :
      ∀ {M S q bs}
      → SelHeads q M S
      → SelDomainCommon S bs
      → LabelwiseMerge S bs
      → MergeStep M (sel q bs)

    -- [M6]
    M6 :
      ∀ {M S q bs}
      → BraHeads q M S
      → BraDomainUnion S bs
      → LabelwiseMerge S bs
      → MergeStep M (bra q bs)

open _Π_ public

rollΠ : ∀ {M T} → wfMergeSet M → W.wf T → MergeStep M T → M Π T
wf-set (rollΠ wM wT s) = wM
wf-merged (rollΠ wM wT s) = wT
outΠ (rollΠ wM wT s) = s

------------------------------------------------------------------------
-- Participant occurrence in globals (used by PR7/PR10).
------------------------------------------------------------------------

mutual
  data pt {k : _} (p : Participant) : Global k → Set where
    pt-msg-src :
      ∀ {q b G}
      → pt p (msg p q b G)

    pt-msg-dst :
      ∀ {q b G}
      → pt p (msg q p b G)

    pt-msg-next :
      ∀ {q r b G}
      → pt p G
      → pt p (msg q r b G)

    pt-choice-src :
      ∀ {q bs}
      → pt p (choice p q bs)

    pt-choice-dst :
      ∀ {q bs}
      → pt p (choice q p bs)

    pt-choice-next :
      ∀ {q r bs}
      → ptB p bs
      → pt p (choice q r bs)

    pt-mu :
      ∀ {body}
      → pt p body
      → pt p (gmu body)

  data ptB {k : _} (p : Participant) : GBranches k → Set where
    ptB-here :
      ∀ {l g bs}
      → lookupGB l bs ≡ just g
      → pt p g
      → ptB p bs

------------------------------------------------------------------------
-- (2) Coinductive projection relation: G ↾[ p ] T
------------------------------------------------------------------------

infix 4 _↾[_]_

mutual
  record _↾[_]_ (G : Global₀) (p : Participant) (T : Local₀) : Set where
    coinductive
    field
      wf-global : WG.wf G
      wf-local  : W.wf T
      out↾      : ProjStep G p T

  BranchProj : Participant → GBranches 0 → MergeSet → Set
  BranchProj p gbs lbs =
    (∀ {l Gi}
     → lookupGB l gbs ≡ just Gi
     → Σ Local₀ (λ Ti → (lookupM l lbs ≡ just Ti) × ▹ (Gi ↾[ p ] Ti)))
    ×
    (∀ l
     → lookupGB l gbs ≡ nothing
     → lookupM l lbs ≡ nothing)

  data ProjStep : Global₀ → Participant → Local₀ → Set where
    -- [PR1]
    PR1 :
      ∀ {p q b G T}
      → ▹ (G ↾[ p ] T)
      → ProjStep (msg p q b G) p (send q b T)

    -- [PR2]
    PR2 :
      ∀ {p q b G T}
      → ▹ (G ↾[ p ] T)
      → ProjStep (msg q p b G) p (recv q b T)

    -- [PR3]
    PR3 :
      ∀ {p q r b G T}
      → p ≢ q
      → p ≢ r
      → ▹ (G ↾[ p ] T)
      → ProjStep (msg q r b G) p T

    -- [PR4]
    PR4 :
      ∀ {p q bs lbs}
      → BranchProj p bs lbs
      → ProjStep (choice p q bs) p (sel q lbs)

    -- [PR5]
    PR5 :
      ∀ {p q bs lbs}
      → BranchProj p bs lbs
      → ProjStep (choice q p bs) p (bra q lbs)

    -- [PR6]
    PR6 :
      ∀ {p q r bs M T}
      → p ≢ q
      → p ≢ r
      → BranchProj p bs M
      → ▹ (M Π T)
      → ProjStep (choice q r bs) p T

    -- [PR7]
    PR7 :
      ∀ {p body T}
      → pt p body
      → ▹ (unfoldG (gmu body) ↾[ p ] T)
      → ProjStep (gmu body) p T

    -- [PR8]
    PR8 :
      ∀ {p G body}
      → ▹ (G ↾[ p ] unfold (mu body))
      → ProjStep G p (mu body)

    -- [PR9]
    PR9 :
      ∀ {p G}
      → ¬ pt p G
      → ProjStep G p end

open _↾[_]_ public

roll↾ :
  ∀ {G p T}
  → WG.wf G
  → W.wf T
  → ProjStep G p T
  → G ↾[ p ] T
wf-global (roll↾ wG wT s) = wG
wf-local  (roll↾ wG wT s) = wT
out↾      (roll↾ wG wT s) = s

------------------------------------------------------------------------
-- Context-level projection and compatibility with context subtyping
------------------------------------------------------------------------

infix 4 _↾_ _⊑_

_↾_ : Global₀ → Δ → Set
G ↾ Δ₀ = ∀ p → G ↾[ p ] (Δ₀ p)

_⊑_ : Δ → Global₀ → Set
Δ₀ ⊑ G = Σ Δ (λ Δ' → (G ↾ Δ') × (Δ₀ ≤Δ Δ'))
