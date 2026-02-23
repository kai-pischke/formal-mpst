{-# OPTIONS --safe #-}

module Semantics.OperationalSemantics (ℓ n : _) where

open import Data.Bool using (Bool; true; false) renaming (not to notᵇ; _∨_ to _∨ᵇ_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Base as Nat using () renaming (_+_ to _+ℕ_; _≤ᵇ_ to _≤ℕᵇ_)
open import Data.Integer.Base as Int using (ℤ) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤᵇ_)
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Syntax.ProcessSyntax as PS

module Syn = PS ℓ n
open Syn public using
  ( Label
  ; Participant
  ; Expr
  ; Expr₀
  ; litTrue
  ; litFalse
  ; natLit
  ; intLit
  ; evar
  ; _∨_
  ; ¬_
  ; _+_
  ; _⊕_
  ; _≤_
  ; Process
  ; Process₀
  ; inactive
  ; send
  ; recv
  ; sel
  ; bra
  ; if_then_else_
  ; mu
  ; pvar
  ; Branches
  ; lookupB
  ; Session
  ; SessionExpr
  ; eval
  )

------------------------------------------------------------------------
-- Expression semantics (closed expressions)
------------------------------------------------------------------------

data Value : Set where
  vbool : Bool → Value
  vnat  : ℕ → Value
  vint  : ℤ → Value

pure : ∀ {A : Set} → A → List A
pure x = x ∷ []

infixl 1 _>>=_
_>>=_ : ∀ {A B : Set} → List A → (A → List B) → List B
[] >>= f       = []
(x ∷ xs) >>= f = f x ++ (xs >>= f)

evalNot : Value → List Value
evalNot (vbool b) = pure (vbool (notᵇ b))
evalNot _         = []

evalOr : Value → Value → List Value
evalOr (vbool b₁) (vbool b₂) = pure (vbool (b₁ ∨ᵇ b₂))
evalOr _          _          = []

evalPlus : Value → Value → List Value
evalPlus (vnat n₁) (vnat n₂) = pure (vnat (n₁ +ℕ n₂))
evalPlus (vint i₁) (vint i₂) = pure (vint (i₁ +ℤ i₂))
evalPlus _         _         = []

evalLe : Value → Value → List Value
evalLe (vnat n₁) (vnat n₂) = pure (vbool (n₁ ≤ℕᵇ n₂))
evalLe (vint i₁) (vint i₂) = pure (vbool (i₁ ≤ℤᵇ i₂))
evalLe _         _         = []

evalExpr : Expr₀ → List Value
evalExpr litTrue      = pure (vbool true)
evalExpr litFalse     = pure (vbool false)
evalExpr (natLit n)   = pure (vnat n)
evalExpr (intLit i)   = pure (vint i)
evalExpr (evar ())
evalExpr (e₁ ∨ e₂)    =
  evalExpr e₁ >>= λ v₁ →
  evalExpr e₂ >>= λ v₂ →
  evalOr v₁ v₂
evalExpr (¬ e)        =
  evalExpr e >>= evalNot
evalExpr (e₁ + e₂)    =
  evalExpr e₁ >>= λ v₁ →
  evalExpr e₂ >>= λ v₂ →
  evalPlus v₁ v₂
evalExpr (e₁ ⊕ e₂)    = evalExpr e₁ ++ evalExpr e₂
evalExpr (e₁ ≤ e₂)    =
  evalExpr e₁ >>= λ v₁ →
  evalExpr e₂ >>= λ v₂ →
  evalLe v₁ v₂

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

infix 4 _⇓_
_⇓_ : Expr₀ → Value → Set
e ⇓ v = v ∈ evalExpr e

------------------------------------------------------------------------
-- Expression-variable substitution into processes (for R-COMM)
------------------------------------------------------------------------

ERen : ℕ → ℕ → Set
ERen v v' = Fin v → Fin v'

ESub : ℕ → ℕ → Set
ESub v v' = Fin v → Expr v'

renameExpr : ∀ {v v'} → ERen v v' → Expr v → Expr v'
renameExpr ρ litTrue      = litTrue
renameExpr ρ litFalse     = litFalse
renameExpr ρ (natLit n)   = natLit n
renameExpr ρ (intLit i)   = intLit i
renameExpr ρ (evar x)     = evar (ρ x)
renameExpr ρ (e₁ ∨ e₂)    = renameExpr ρ e₁ ∨ renameExpr ρ e₂
renameExpr ρ (¬ e)        = ¬ (renameExpr ρ e)
renameExpr ρ (e₁ + e₂)    = renameExpr ρ e₁ + renameExpr ρ e₂
renameExpr ρ (e₁ ⊕ e₂)    = renameExpr ρ e₁ ⊕ renameExpr ρ e₂
renameExpr ρ (e₁ ≤ e₂)    = renameExpr ρ e₁ ≤ renameExpr ρ e₂

liftESub : ∀ {v v'} → ESub v v' → ESub (suc v) (suc v')
liftESub σ zero    = evar zero
liftESub σ (suc i) = renameExpr suc (σ i)

substExpr : ∀ {v v'} → ESub v v' → Expr v → Expr v'
substExpr σ litTrue      = litTrue
substExpr σ litFalse     = litFalse
substExpr σ (natLit n)   = natLit n
substExpr σ (intLit i)   = intLit i
substExpr σ (evar x)     = σ x
substExpr σ (e₁ ∨ e₂)    = substExpr σ e₁ ∨ substExpr σ e₂
substExpr σ (¬ e)        = ¬ (substExpr σ e)
substExpr σ (e₁ + e₂)    = substExpr σ e₁ + substExpr σ e₂
substExpr σ (e₁ ⊕ e₂)    = substExpr σ e₁ ⊕ substExpr σ e₂
substExpr σ (e₁ ≤ e₂)    = substExpr σ e₁ ≤ substExpr σ e₂

mutual
  substMaybeProc : ∀ {k v v'} → ESub v v' → Maybe (Process k v) → Maybe (Process k v')
  substMaybeProc σ nothing  = nothing
  substMaybeProc σ (just P) = just (substProc σ P)

  substVecProc : ∀ {k v v' m}
               → ESub v v'
               → Vec (Maybe (Process k v)) m
               → Vec (Maybe (Process k v')) m
  substVecProc σ []       = []
  substVecProc σ (x ∷ xs) = substMaybeProc σ x ∷ substVecProc σ xs

  substBranches : ∀ {k v v'} → ESub v v' → Branches k v → Branches k v'
  substBranches σ = substVecProc σ

  substProc : ∀ {k v v'} → ESub v v' → Process k v → Process k v'
  substProc σ inactive             = inactive
  substProc σ (send p e P)         = send p (substExpr σ e) (substProc σ P)
  substProc σ (recv p P)           = recv p (substProc (liftESub σ) P)
  substProc σ (sel p l P)          = sel p l (substProc σ P)
  substProc σ (bra p bs)           = bra p (substBranches σ bs)
  substProc σ (if e then P else Q) = if substExpr σ e then substProc σ P else substProc σ Q
  substProc σ (mu body)            = mu (substProc σ body)
  substProc σ (pvar X)             = pvar X

valueExpr : ∀ {v} → Value → Expr v
valueExpr (vbool true)  = litTrue
valueExpr (vbool false) = litFalse
valueExpr (vnat n)      = natLit n
valueExpr (vint i)      = intLit i

substTopProc : ∀ {k v} → Value → Process k (suc v) → Process k v
substTopProc {k} {v} w = substProc σ
  where
    σ : ESub (suc v) v
    σ zero    = valueExpr w
    σ (suc i) = evar i

------------------------------------------------------------------------
-- Structural congruence / expansion
--
-- Asymmetric relation:
-- left can be viewed as right where the right may be unfolded.
------------------------------------------------------------------------

PRen : ℕ → ℕ → Set
PRen k k' = Fin k → Fin k'

PSub : ℕ → ℕ → ℕ → Set
PSub k k' v = Fin k → Process k' v

liftPSubExpr : ∀ {k k' v} → PSub k k' v → PSub k k' (suc v)
liftPSubExpr {k} {k'} {v} σ i = substProc τ (σ i)
  where
    τ : ESub v (suc v)
    τ j = evar (suc j)

liftPRen : ∀ {k k'} → PRen k k' → PRen (suc k) (suc k')
liftPRen ρ zero    = zero
liftPRen ρ (suc i) = suc (ρ i)

mutual
  renamePMaybe : ∀ {k k' v} → PRen k k' → Maybe (Process k v) → Maybe (Process k' v)
  renamePMaybe ρ nothing  = nothing
  renamePMaybe ρ (just P) = just (renameP ρ P)

  renamePVec : ∀ {k k' v m}
             → PRen k k'
             → Vec (Maybe (Process k v)) m
             → Vec (Maybe (Process k' v)) m
  renamePVec ρ []       = []
  renamePVec ρ (x ∷ xs) = renamePMaybe ρ x ∷ renamePVec ρ xs

  renamePBranches : ∀ {k k' v} → PRen k k' → Branches k v → Branches k' v
  renamePBranches ρ = renamePVec ρ

  renameP : ∀ {k k' v} → PRen k k' → Process k v → Process k' v
  renameP ρ inactive             = inactive
  renameP ρ (send p e P)         = send p e (renameP ρ P)
  renameP ρ (recv p P)           = recv p (renameP ρ P)
  renameP ρ (sel p l P)          = sel p l (renameP ρ P)
  renameP ρ (bra p bs)           = bra p (renamePBranches ρ bs)
  renameP ρ (if e then P else Q) = if e then renameP ρ P else renameP ρ Q
  renameP ρ (mu body)            = mu (renameP (liftPRen ρ) body)
  renameP ρ (pvar X)             = pvar (ρ X)

wkP : ∀ {k v} → Process k v → Process (suc k) v
wkP = renameP suc

liftPSub : ∀ {k k' v} → PSub k k' v → PSub (suc k) (suc k') v
liftPSub σ zero    = pvar zero
liftPSub σ (suc i) = wkP (σ i)

mutual
  substPMaybe : ∀ {k k' v} → PSub k k' v → Maybe (Process k v) → Maybe (Process k' v)
  substPMaybe σ nothing  = nothing
  substPMaybe σ (just P) = just (substP σ P)

  substPVec : ∀ {k k' v m}
            → PSub k k' v
            → Vec (Maybe (Process k v)) m
            → Vec (Maybe (Process k' v)) m
  substPVec σ []       = []
  substPVec σ (x ∷ xs) = substPMaybe σ x ∷ substPVec σ xs

  substPBranches : ∀ {k k' v} → PSub k k' v → Branches k v → Branches k' v
  substPBranches σ = substPVec σ

  substP : ∀ {k k' v} → PSub k k' v → Process k v → Process k' v
  substP σ inactive             = inactive
  substP σ (send p e P)         = send p e (substP σ P)
  substP σ (recv p P)           = recv p (substP (liftPSubExpr σ) P)
  substP σ (sel p l P)          = sel p l (substP σ P)
  substP σ (bra p bs)           = bra p (substPBranches σ bs)
  substP σ (if e then P else Q) = if e then substP σ P else substP σ Q
  substP σ (mu body)            = mu (substP (liftPSub σ) body)
  substP σ (pvar X)             = σ X

unfoldP : ∀ {k v} → Process k v → Process k v
unfoldP {k} {v} (mu body) =
  substP σ body
  where
    σ : PSub (suc k) k v
    σ zero    = mu body
    σ (suc i) = pvar i
unfoldP P = P

infix 4 _⇛ᵖ_ _⇛ᵐ_ _⇛ᵇ_

data _⇛ᵖ_ {k v} : Process k v → Process k v → Set
data _⇛ᵐ_ {k v} : Maybe (Process k v) → Maybe (Process k v) → Set
data _⇛ᵇ_ {k v} : ∀ {m} → Vec (Maybe (Process k v)) m → Vec (Maybe (Process k v)) m → Set

data _⇛ᵖ_ {k v} where
  prefl : ∀ {P} → P ⇛ᵖ P
  ptrans : ∀ {P Q R} → P ⇛ᵖ Q → Q ⇛ᵖ R → P ⇛ᵖ R

  -- Optional unfolding on the right.
  punfoldᵣ : ∀ {body} → mu body ⇛ᵖ unfoldP (mu body)

  p-send : ∀ {p e P Q} → P ⇛ᵖ Q → send p e P ⇛ᵖ send p e Q
  p-recv : ∀ {p P Q} → P ⇛ᵖ Q → recv p P ⇛ᵖ recv p Q
  p-sel  : ∀ {p l P Q} → P ⇛ᵖ Q → sel p l P ⇛ᵖ sel p l Q
  p-bra  : ∀ {p bs cs} → bs ⇛ᵇ cs → bra p bs ⇛ᵖ bra p cs
  p-if   : ∀ {e P P' Q Q'} → P ⇛ᵖ P' → Q ⇛ᵖ Q' → if e then P else Q ⇛ᵖ if e then P' else Q'
  p-mu   : ∀ {body body'} → body ⇛ᵖ body' → mu body ⇛ᵖ mu body'

data _⇛ᵐ_ {k v} where
  m-nothing : nothing ⇛ᵐ nothing
  m-just    : ∀ {P Q} → P ⇛ᵖ Q → just P ⇛ᵐ just Q

data _⇛ᵇ_ {k v} where
  bnil  : [] ⇛ᵇ []
  bcons :
    ∀ {m}
    {x y : Maybe (Process k v)}
    {xs ys : Vec (Maybe (Process k v)) m}
    → x ⇛ᵐ y
    → xs ⇛ᵇ ys
    → (x ∷ xs) ⇛ᵇ (y ∷ ys)

infix 4 _⇛_
_⇛_ : Session → Session → Set
M ⇛ N = ∀ p → M p ⇛ᵖ N p

------------------------------------------------------------------------
-- Session semantics
------------------------------------------------------------------------

update : Participant → Process₀ → Session → Session
update p P M q with q ≟ p
... | yes _ = P
... | no  _ = M q

data Outcome : Set where
  ok    : Session → Outcome
  error : Outcome

data NonBool : Value → Set where
  nonNat : ∀ n → NonBool (vnat n)
  nonInt : ∀ i → NonBool (vint i)

infix 2 _⟶_
data _⟶_ : Session → Outcome → Set where
  R-COMM :
    ∀ {M p q P Q e v}
    → M p ≡ recv q P
    → M q ≡ send p e Q
    → e ⇓ v
    → M ⟶ ok (update q Q (update p (substTopProc v P) M))

  R-BRA :
    ∀ {M p q l P bs Pk}
    → M p ≡ sel q l P
    → M q ≡ bra p bs
    → lookupB l bs ≡ just Pk
    → M ⟶ ok (update q Pk (update p P M))

  T-COND :
    ∀ {M p e P Q}
    → M p ≡ if e then P else Q
    → e ⇓ vbool true
    → M ⟶ ok (update p P M)

  F-COND :
    ∀ {M p e P Q}
    → M p ≡ if e then P else Q
    → e ⇓ vbool false
    → M ⟶ ok (update p Q M)

  V-ERR :
    ∀ {M p e P Q v}
    → M p ≡ if e then P else Q
    → e ⇓ v
    → NonBool v
    → M ⟶ error

  C-ERR :
    ∀ {M p q l P bs}
    → M p ≡ sel q l P
    → M q ≡ bra p bs
    → lookupB l bs ≡ nothing
    → M ⟶ error

  R-STR :
    ∀ {M₁ M₂ M₃ M₄}
    → M₁ ⇛ M₂
    → M₂ ⟶ ok M₃
    → M₃ ⇛ M₄
    → M₁ ⟶ ok M₄

  R-STR-ERR :
    ∀ {M₁ M₂}
    → M₁ ⇛ M₂
    → M₂ ⟶ error
    → M₁ ⟶ error

-- Optional wrapper: semantics directly on session-expression syntax.
infix 2 _⟶ₑ_
_⟶ₑ_ : SessionExpr → Outcome → Set
M ⟶ₑ R = eval M ⟶ R
