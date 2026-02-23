{-# OPTIONS --guardedness #-}

module Synthesis.GlobalSynthesis (ℓ n : _) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin; _≟_)
open import Data.Fin.Base as Fin using (toℕ)
import Data.Fin as F
import Data.Fin.Properties as FinP
open import Data.Vec as Vec using (Vec; tabulate; lookup)
  renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Vec.Properties as VecP using (≡-dec; lookup∘tabulate; tabulate-cong)
open import Data.List.Base as List using (List; []; _∷_; _++_; take; drop; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties as LMemP using (∈-allFin; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Properties as ListP using (take++drop≡id)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
import Syntax.GlobalSessionTypes as GTS
import Theory.MergeProjection as MP
import Theory.LocalSemanticProperties as LSP
import Syntax.LocalSessionTypes as LTS
import Theory.WellFormedLocalTypes as WFLT

module G = GTS ℓ n
module M = MP ℓ n
module S = LSP ℓ n
module L = LTS ℓ n
module WFL = WFLT ℓ n

open M public using
  ( Participant
  ; Δ
  ; Global₀
  ; _⊑_
  )

open S public using
  ( safe
  ; liveContext
  ; stepStatus
  )

open WFL public using
  ( wfΔ
  ; wf-pres-→₂
  )

open G using
  ( Global
  ; msg
  ; choice
  ; mu
  ; var
  )

------------------------------------------------------------------------
-- Priorities and synthesis keys
------------------------------------------------------------------------

Priority : Set
Priority = Participant

------------------------------------------------------------------------
-- Synthesis keys and environments
------------------------------------------------------------------------

record SynthKey : Set where
  constructor key
  field
    ctx : Δ
    prio : Priority

open SynthKey public

record _≈key_ (κ₁ κ₂ : SynthKey) : Set where
  field
    ctx≈ : ∀ p → ctx κ₁ p ≡ ctx κ₂ p
    prio≈ : prio κ₁ ≡ prio κ₂

open _≈key_ public

record SynthEnv (k : ℕ) : Set where
  field
    lookupEnv : SynthKey → Maybe (Fin k)

    -- Distinct keys cannot share the same global recursion variable.
    uniqueVar :
      ∀ {κ₁ κ₂ i}
      → lookupEnv κ₁ ≡ just i
      → lookupEnv κ₂ ≡ just i
      → κ₁ ≈key κ₂

open SynthEnv public

emptyEnv : SynthEnv zero
lookupEnv emptyEnv _ = nothing
uniqueVar emptyEnv {i = ()}

------------------------------------------------------------------------
-- Synthesis
------------------------------------------------------------------------

SenderWitness : Δ → Participant → Set
SenderWitness Δ₀ m =
  Σ Participant (λ q →
  Σ S.Observable (λ U →
    S.CanSync₂ Δ₀ m q U))

senderEnabled? :
  (Δ₀ : Δ)
  → wfΔ Δ₀
  → (m : Participant)
  → Dec (SenderWitness Δ₀ m)
senderEnabled? Δ₀ wΔ m =
  S.findFin
    (λ q →
      Σ S.Observable (λ U →
        S.CanSync₂ Δ₀ m q U))
    (λ q →
      S.findObservable
        (λ U → S.CanSync₂ Δ₀ m q U)
        (λ U → S.canSync₂? Δ₀ wΔ m q U))

participantsFrom : Priority → List Participant
participantsFrom p =
  List.drop (Fin.toℕ p) (List.allFin n) List.++
  List.take (Fin.toℕ p) (List.allFin n)

findFirst :
  ∀ {A : Set} {P : A → Set}
  → (xs : List A)
  → ((x : A) → Dec (P x))
  → Maybe (Σ A P)
findFirst [] dec = nothing
findFirst (x ∷ xs) dec with dec x
... | yes px = just (x , px)
... | no ¬px = findFirst xs dec

findFirst-none :
  ∀ {A : Set} {P : A → Set}
  → (xs : List A)
  → (dec : (x : A) → Dec (P x))
  → findFirst xs dec ≡ nothing
  → ∀ {x} → x ∈ xs → ¬ P x
findFirst-none [] dec eq ()
findFirst-none (y ∷ ys) dec eq {x} x∈ with dec y | eq
... | yes py | ()
... | no ¬py | eq' with x∈
...   | here refl = ¬py
...   | there x∈ys = findFirst-none ys dec eq' x∈ys

nextSender? :
  (Δ₀ : Δ)
  → wfΔ Δ₀
  → (prio : Priority)
  → Maybe (Σ Participant (λ m → SenderWitness Δ₀ m))
nextSender? Δ₀ wΔ prio =
  findFirst (participantsFrom prio) (senderEnabled? Δ₀ wΔ)

participantsFrom-contains :
  (prio : Priority)
  → (m : Participant)
  → m ∈ participantsFrom prio
participantsFrom-contains prio m with
  LMemP.∈-++⁻
    (List.take (Fin.toℕ prio) (List.allFin n))
    {ys = List.drop (Fin.toℕ prio) (List.allFin n)}
    (subst
      (λ ys → m ∈ ys)
      (sym (ListP.take++drop≡id (Fin.toℕ prio) (List.allFin n)))
      (LMemP.∈-allFin m))
... | inj₁ m∈take = LMemP.∈-++⁺ʳ (List.drop (Fin.toℕ prio) (List.allFin n)) m∈take
... | inj₂ m∈drop = LMemP.∈-++⁺ˡ m∈drop

senderFromCanStep :
  ∀ {Δ₀ : Δ}
  → S.S.CanStep₂ Δ₀
  → Σ Participant (λ m → SenderWitness Δ₀ m)
senderFromCanStep (Δ₁ , (S.S._↝⟨_⟩_ m U q , sync)) =
  m , (q , (U , (Δ₁ , sync)))

mutual
  maybeLocal-≟ :
    ∀ {k}
    → (x y : Maybe (L.Local k))
    → Dec (x ≡ y)
  maybeLocal-≟ nothing nothing = yes refl
  maybeLocal-≟ nothing (just y) = no λ ()
  maybeLocal-≟ (just x) nothing = no λ ()
  maybeLocal-≟ (just x) (just y) with local-≟ x y
  ... | yes x≡y = yes (cong just x≡y)
  ... | no x≢y = no λ where refl → x≢y refl

  branchesVec-≟ :
    ∀ {k m}
    → (bs₁ bs₂ : Vec (Maybe (L.Local k)) m)
    → Dec (bs₁ ≡ bs₂)
  branchesVec-≟ []ᵥ []ᵥ = yes refl
  branchesVec-≟ (x ∷ᵥ xs) (y ∷ᵥ ys) with maybeLocal-≟ x y | branchesVec-≟ xs ys
  ... | yes refl | yes refl = yes refl
  ... | no x≢y | _ = no λ where refl → x≢y refl
  ... | yes refl | no xs≢ys = no λ where refl → xs≢ys refl

  branches-≟ :
    ∀ {k}
    → (bs₁ bs₂ : L.Branches k)
    → Dec (bs₁ ≡ bs₂)
  branches-≟ = branchesVec-≟

  local-≟ :
    ∀ {k}
    → (T U : L.Local k)
    → Dec (T ≡ U)
  local-≟ L.end L.end = yes refl
  local-≟ L.end (L.send p b T) = no λ ()
  local-≟ L.end (L.recv p b T) = no λ ()
  local-≟ L.end (L.sel p bs) = no λ ()
  local-≟ L.end (L.bra p bs) = no λ ()
  local-≟ L.end (L.mu T) = no λ ()
  local-≟ L.end (L.var x) = no λ ()

  local-≟ (L.send p b T) L.end = no λ ()
  local-≟ (L.send p b T) (L.send p' b' U) with p ≟ p' | S.base-≟ b b' | local-≟ T U
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no p≢p' | _ | _ = no λ where refl → p≢p' refl
  ... | yes refl | no b≢b' | _ = no λ where refl → b≢b' refl
  ... | yes refl | yes refl | no T≢U = no λ where refl → T≢U refl
  local-≟ (L.send p b T) (L.recv p' b' U) = no λ ()
  local-≟ (L.send p b T) (L.sel p' bs) = no λ ()
  local-≟ (L.send p b T) (L.bra p' bs) = no λ ()
  local-≟ (L.send p b T) (L.mu U) = no λ ()
  local-≟ (L.send p b T) (L.var x) = no λ ()

  local-≟ (L.recv p b T) L.end = no λ ()
  local-≟ (L.recv p b T) (L.send p' b' U) = no λ ()
  local-≟ (L.recv p b T) (L.recv p' b' U) with p ≟ p' | S.base-≟ b b' | local-≟ T U
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no p≢p' | _ | _ = no λ where refl → p≢p' refl
  ... | yes refl | no b≢b' | _ = no λ where refl → b≢b' refl
  ... | yes refl | yes refl | no T≢U = no λ where refl → T≢U refl
  local-≟ (L.recv p b T) (L.sel p' bs) = no λ ()
  local-≟ (L.recv p b T) (L.bra p' bs) = no λ ()
  local-≟ (L.recv p b T) (L.mu U) = no λ ()
  local-≟ (L.recv p b T) (L.var x) = no λ ()

  local-≟ (L.sel p bs) L.end = no λ ()
  local-≟ (L.sel p bs) (L.send p' b U) = no λ ()
  local-≟ (L.sel p bs) (L.recv p' b U) = no λ ()
  local-≟ (L.sel p bs) (L.sel p' bs') with p ≟ p' | branches-≟ bs bs'
  ... | yes refl | yes refl = yes refl
  ... | no p≢p' | _ = no λ where refl → p≢p' refl
  ... | yes refl | no bs≢bs' = no λ where refl → bs≢bs' refl
  local-≟ (L.sel p bs) (L.bra p' bs') = no λ ()
  local-≟ (L.sel p bs) (L.mu U) = no λ ()
  local-≟ (L.sel p bs) (L.var x) = no λ ()

  local-≟ (L.bra p bs) L.end = no λ ()
  local-≟ (L.bra p bs) (L.send p' b U) = no λ ()
  local-≟ (L.bra p bs) (L.recv p' b U) = no λ ()
  local-≟ (L.bra p bs) (L.sel p' bs') = no λ ()
  local-≟ (L.bra p bs) (L.bra p' bs') with p ≟ p' | branches-≟ bs bs'
  ... | yes refl | yes refl = yes refl
  ... | no p≢p' | _ = no λ where refl → p≢p' refl
  ... | yes refl | no bs≢bs' = no λ where refl → bs≢bs' refl
  local-≟ (L.bra p bs) (L.mu U) = no λ ()
  local-≟ (L.bra p bs) (L.var x) = no λ ()

  local-≟ (L.mu T) L.end = no λ ()
  local-≟ (L.mu T) (L.send p b U) = no λ ()
  local-≟ (L.mu T) (L.recv p b U) = no λ ()
  local-≟ (L.mu T) (L.sel p bs) = no λ ()
  local-≟ (L.mu T) (L.bra p bs) = no λ ()
  local-≟ (L.mu T) (L.mu U) with local-≟ T U
  ... | yes refl = yes refl
  ... | no T≢U = no λ where refl → T≢U refl
  local-≟ (L.mu T) (L.var x) = no λ ()

  local-≟ (L.var x) L.end = no λ ()
  local-≟ (L.var x) (L.send p b U) = no λ ()
  local-≟ (L.var x) (L.recv p b U) = no λ ()
  local-≟ (L.var x) (L.sel p bs) = no λ ()
  local-≟ (L.var x) (L.bra p bs) = no λ ()
  local-≟ (L.var x) (L.mu U) = no λ ()
  local-≟ (L.var x) (L.var y) with x ≟ y
  ... | yes refl = yes refl
  ... | no x≢y = no λ where refl → x≢y refl

ctx≈? :
  (Δ₁ Δ₂ : Δ)
  → Dec (∀ p → Δ₁ p ≡ Δ₂ p)
ctx≈? Δ₁ Δ₂ with VecP.≡-dec local-≟ (tabulate Δ₁) (tabulate Δ₂)
... | yes eq = yes λ p →
  trans
    (sym (VecP.lookup∘tabulate Δ₁ p))
    (trans (cong (λ xs → lookup xs p) eq) (VecP.lookup∘tabulate Δ₂ p))
... | no ¬eq = no λ Δ₁≈Δ₂ →
  ¬eq (VecP.tabulate-cong Δ₁≈Δ₂)

key≈? :
  (κ₁ κ₂ : SynthKey)
  → Dec (κ₁ ≈key κ₂)
key≈? (key Δ₁ p₁) (key Δ₂ p₂) with ctx≈? Δ₁ Δ₂ | p₁ ≟ p₂
... | yes Δ₁≈Δ₂ | yes p₁≡p₂ = yes record
  { ctx≈ = Δ₁≈Δ₂
  ; prio≈ = p₁≡p₂
  }
... | no Δ₁≉Δ₂ | _ = no λ κ₁≈κ₂ →
  Δ₁≉Δ₂ (ctx≈ κ₁≈κ₂)
... | yes _ | no p₁≢p₂ = no λ κ₁≈κ₂ →
  p₁≢p₂ (prio≈ κ₁≈κ₂)

liftVar :
  ∀ {k}
  → Maybe (Fin k)
  → Maybe (Fin (suc k))
liftVar nothing = nothing
liftVar (just i) = just (F.suc i)

lookupExt :
  ∀ {k}
  → (Γ : SynthEnv k)
  → (Δ₀ : Δ)
  → (m : Priority)
  → SynthKey
  → Maybe (Fin (suc k))
lookupExt Γ Δ₀ m κ with key≈? κ (key Δ₀ m)
... | yes _ = just F.zero
... | no _ = liftVar (lookupEnv Γ κ)

lookupExt-zero→target :
  ∀ {k} (Γ : SynthEnv k) (Δ₀ : Δ) (m : Priority) {κ}
  → lookupExt Γ Δ₀ m κ ≡ just F.zero
  → κ ≈key key Δ₀ m
lookupExt-zero→target Γ Δ₀ m {κ} eq with key≈? κ (key Δ₀ m) | eq
... | yes κ≈ | _ = κ≈
... | no _ | eq' with lookupEnv Γ κ | eq'
...   | nothing | ()
...   | just i | ()

lookupExt-suc→old :
  ∀ {k} (Γ : SynthEnv k) (Δ₀ : Δ) (m : Priority) {κ} {j : Fin k}
  → lookupExt Γ Δ₀ m κ ≡ just (F.suc j)
  → lookupEnv Γ κ ≡ just j
lookupExt-suc→old Γ Δ₀ m {κ} {j} eq with key≈? κ (key Δ₀ m) | eq
... | yes _ | ()
... | no _ | eq' with lookupEnv Γ κ | eq'
...   | nothing | ()
...   | just i | refl = refl

extendUniqueVar :
  ∀ {k} (Γ : SynthEnv k) (Δ₀ : Δ) (m : Priority) {κ₁ κ₂ i}
  → lookupExt Γ Δ₀ m κ₁ ≡ just i
  → lookupExt Γ Δ₀ m κ₂ ≡ just i
  → κ₁ ≈key κ₂
extendUniqueVar Γ Δ₀ m {κ₁} {κ₂} {F.zero} h₁ h₂
  with lookupExt-zero→target Γ Δ₀ m h₁
     | lookupExt-zero→target Γ Δ₀ m h₂
... | κ₁≈ | κ₂≈ = record
  { ctx≈ = λ p → trans (ctx≈ κ₁≈ p) (sym (ctx≈ κ₂≈ p))
  ; prio≈ = trans (prio≈ κ₁≈) (sym (prio≈ κ₂≈))
  }
extendUniqueVar Γ Δ₀ m {κ₁} {κ₂} {F.suc i} h₁ h₂ =
  uniqueVar Γ
    (lookupExt-suc→old Γ Δ₀ m h₁)
    (lookupExt-suc→old Γ Δ₀ m h₂)

extendEnv :
  ∀ {k}
  → (Γ : SynthEnv k)
  → (Δ₀ : Δ)
  → (m : Priority)
  → SynthEnv (suc k)
lookupEnv (extendEnv Γ Δ₀ m) = lookupExt Γ Δ₀ m
uniqueVar (extendEnv Γ Δ₀ m) = extendUniqueVar Γ Δ₀ m

nextPriority : Priority → Priority
nextPriority p = _mod_ (suc (Fin.toℕ p)) n {{FinP.nonZeroIndex p}}

nextSender :
  (Δ₀ : Δ)
  → wfΔ Δ₀
  → (prio : Priority)
  → S.S.CanStep₂ Δ₀
  → Σ Participant (λ m → SenderWitness Δ₀ m)
nextSender Δ₀ wΔ prio canStep with nextSender? Δ₀ wΔ prio in fs
... | just m = m
... | nothing = ⊥-elim (noSender senderM)
  where
    sender : Σ Participant (λ m → SenderWitness Δ₀ m)
    sender = senderFromCanStep canStep

    m : Participant
    m = proj₁ sender

    senderM : SenderWitness Δ₀ m
    senderM = proj₂ sender

    m∈prio : m ∈ participantsFrom prio
    m∈prio = participantsFrom-contains prio m

    noSender : ¬ SenderWitness Δ₀ m
    noSender = findFirst-none (participantsFrom prio) (senderEnabled? Δ₀ wΔ) fs m∈prio

synth :
  ∀ {k}
  → (Δ₀ : Δ)
  → wfΔ Δ₀
  → (Γ : SynthEnv k)
  → (prio : Priority)
  → Global k
{-# TERMINATING #-}
synth Δ₀ wΔ Γ prio with stepStatus Δ₀ wΔ
... | inj₁ stuckΔ₀ = G.end
... | inj₂ canStepΔ₀ with nextSender Δ₀ wΔ prio canStepΔ₀
...   | m , senderM with lookupEnv Γ (key Δ₀ m)
...     | just i = var i
...     | nothing with senderM
...       | q , (S.obsBase b , (Δ₁ , sync)) =
          let Γ' = extendEnv Γ Δ₀ m
              wΔ₁ = wf-pres-→₂ wΔ sync
              G' = synth Δ₁ wΔ₁ Γ' (nextPriority m)
          in mu (msg m q b G')
...       | q , (S.obsLabel l , (Δ₁ , sync)) =
          mu (choice m q (tabulate branchAt))
          where
            Γ' = extendEnv Γ Δ₀ m

            branchAt : _ → Maybe (Global (suc _))
            branchAt l' with S.canSync₂? Δ₀ wΔ m q (S.obsLabel l')
            ... | yes (Δᵢ , syncᵢ) =
              let wΔᵢ = wf-pres-→₂ wΔ syncᵢ
                  Gᵢ = synth Δᵢ wΔᵢ Γ' (nextPriority m)
              in just Gᵢ
            ... | no _ = nothing
