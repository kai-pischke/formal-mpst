{-# OPTIONS --safe --guardedness #-}

module Theory.LocalSemanticProperties (ℓ n : _) where

open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; _≟_) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; Σ; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
import Semantics.LocalOperationalSemantics as LOS
import Theory.SessionSubtypingProperties as SUB
import Theory.WellFormedLocalTypes as WFL
import Core.SessionBase as SB

module S = LOS ℓ n
module Sub = SUB ℓ n
module W = WFL ℓ n
module B = SB ℓ n

open B using (Base; bool; nat; int)

open S public using
  ( Participant
  ; Observable
  ; Local₀
  ; send
  ; recv
  ; sel
  ; bra
  ; Δ
  ; SafeState
  ; CanSync₂
  ; safe
  ; Trace
  ; unfoldᵗ
  ; Fair
  ; Live
  ; liveContext
  ; _!⟨_⟩
  ; _?⟨_⟩
  ; _∶_
  ; obsBase
  ; obsLabel
  ; _↝⟨_⟩_
  ; _-[_]→ₗ_
  ; _-[_]→₁_
  ; _-[_]→₂_
  ; _-[_,_]?→₁_
  ; updateΔ
  ; LTag
  ; LR1
  ; LR2
  ; LR3
  ; LR4
  ; LR5
  ; LEnv
  ; _→₂_
  ; _→₂*_
  ; rtc-refl
  ; rtc-step
  )

open Sub public using
  ( _≤_
  ; _≤Δ_
  ; wf-left
  ; wf-right
  ; out
  ; force
  ; s-send
  ; s-recv
  ; s-sel
  ; s-bra
  ; s-muL
  ; s-muR
  ; SelM
  ; BraM
  ; sel-just
  ; bra-just
  )

open W public using
  ( wf
  ; wf-end
  ; wf-send
  ; wf-recv
  ; wf-sel
  ; NonEmpty
  ; wf-bra
  ; wf-mu
  ; lookupB
  ; wfΔ
  )

private
  R : Local₀ → Local₀ → Set
  R X Y = Sub.▹ (X ≤ Y)

------------------------------------------------------------------------
-- Decidable synchronous progress for well-formed contexts
------------------------------------------------------------------------

base-≟ : ∀ (b₁ b₂ : Base) → Dec (b₁ ≡ b₂)
base-≟ bool bool = yes refl
base-≟ bool nat  = no λ ()
base-≟ bool int  = no λ ()
base-≟ nat  bool = no λ ()
base-≟ nat  nat  = yes refl
base-≟ nat  int  = no λ ()
base-≟ int  bool = no λ ()
base-≟ int  nat  = no λ ()
base-≟ int  int  = yes refl

nothing≢just : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
nothing≢just ()

findFin :
  ∀ {m}
  → (P : Fin m → Set)
  → ((i : Fin m) → Dec (P i))
  → Dec (Σ (Fin m) P)
findFin {m = zero} P dec = no λ { (() , _) }
findFin {m = suc m} P dec with dec fzero
... | yes p0 = yes (fzero , p0)
... | no ¬p0 with findFin {m = m} (λ i → P (fsuc i)) (λ i → dec (fsuc i))
...   | yes (i , pi) = yes (fsuc i , pi)
...   | no ¬ps = no λ where
      (fzero  , p0) → ¬p0 p0
      (fsuc i , pi) → ¬ps (i , pi)

findObservable :
  (P : Observable → Set)
  → ((U : Observable) → Dec (P U))
  → Dec (Σ Observable P)
findObservable P dec with dec (obsBase bool)
... | yes pbool = yes (obsBase bool , pbool)
... | no ¬pbool with dec (obsBase nat)
...   | yes pnat = yes (obsBase nat , pnat)
...   | no ¬pnat with dec (obsBase int)
...     | yes pint = yes (obsBase int , pint)
...     | no ¬pint with findFin (λ l → P (obsLabel l)) (λ l → dec (obsLabel l))
...       | yes (l , pl) = yes (obsLabel l , pl)
...       | no ¬pl = no λ where
            (obsBase bool , p) → ¬pbool p
            (obsBase nat  , p) → ¬pnat p
            (obsBase int  , p) → ¬pint p
            (obsLabel l   , p) → ¬pl (l , p)

send-step? :
  ∀ {T q U}
  → (wT : wf T)
  → Dec (Σ Local₀ (λ T' → T -[ q !⟨ U ⟩ ]→ₗ T'))
send-step? {q = q} {U = U} wf-end = no λ where ()
send-step? {q = q} {U = U} (wf-send {p = p} {B = B} {t = t} wt) = decide (q ≟ p) U
  where
    decide :
      Dec (q ≡ p)
      → (U : Observable)
      → Dec (Σ Local₀ (λ T' → send p B t -[ q !⟨ U ⟩ ]→ₗ T'))
    decide (no q≢p) U = no λ where
      (_ , LR1) → q≢p refl
    decide (yes q≡p) (obsLabel l) = no λ where ()
    decide (yes q≡p) (obsBase B') with base-≟ B' B
    ... | no B'≢B = no λ where
      (_ , LR1) → B'≢B refl
    ... | yes B'≡B =
      yes
        ( t
        , subst
            (λ q₀ → send p B t -[ q₀ !⟨ obsBase B' ⟩ ]→ₗ t)
            (sym q≡p)
            (subst
               (λ B₀ → send p B t -[ p !⟨ obsBase B₀ ⟩ ]→ₗ t)
               (sym B'≡B)
               LR1)
        )
send-step? {q = q} {U = U} (wf-recv wt) = no λ where ()
send-step? {q = q} {U = U} (wf-sel {p = p} {bs = bs} ne wbs) = decide (q ≟ p) U
  where
    decide :
      Dec (q ≡ p)
      → (U : Observable)
      → Dec (Σ Local₀ (λ T' → sel p bs -[ q !⟨ U ⟩ ]→ₗ T'))
    decide (no q≢p) U = no λ where
      (_ , LR3 hit) → q≢p refl
    decide (yes q≡p) (obsBase B) = no λ where ()
    decide (yes q≡p) (obsLabel l) with lookupB l bs in eq
    ... | nothing = no λ where
      (_ , LR3 hit) → nothing≢just (trans (sym hit) eq)
    ... | just t rewrite q≡p = yes (t , LR3 eq)
send-step? {q = q} {U = U} (wf-bra ne wbs) = no λ where ()
send-step? {q = q} {U = U} (wf-mu g wunf) with send-step? {q = q} {U = U} wunf
... | yes (T' , step) = yes (T' , LR5 step)
... | no ¬step = no λ where
    (_ , LR5 step) → ¬step ( _ , step)

recv-step? :
  ∀ {T q U}
  → (wT : wf T)
  → Dec (Σ Local₀ (λ T' → T -[ q ?⟨ U ⟩ ]→ₗ T'))
recv-step? {q = q} {U = U} wf-end = no λ where ()
recv-step? {q = q} {U = U} (wf-send wt) = no λ where ()
recv-step? {q = q} {U = U} (wf-recv {p = p} {B = B} {t = t} wt) = decide (q ≟ p) U
  where
    decide :
      Dec (q ≡ p)
      → (U : Observable)
      → Dec (Σ Local₀ (λ T' → recv p B t -[ q ?⟨ U ⟩ ]→ₗ T'))
    decide (no q≢p) U = no λ where
      (_ , LR2) → q≢p refl
    decide (yes q≡p) (obsLabel l) = no λ where ()
    decide (yes q≡p) (obsBase B') with base-≟ B' B
    ... | no B'≢B = no λ where
      (_ , LR2) → B'≢B refl
    ... | yes B'≡B =
      yes
        ( t
        , subst
            (λ q₀ → recv p B t -[ q₀ ?⟨ obsBase B' ⟩ ]→ₗ t)
            (sym q≡p)
            (subst
               (λ B₀ → recv p B t -[ p ?⟨ obsBase B₀ ⟩ ]→ₗ t)
               (sym B'≡B)
               LR2)
        )
recv-step? {q = q} {U = U} (wf-sel ne wbs) = no λ where ()
recv-step? {q = q} {U = U} (wf-bra {p = p} {bs = bs} ne wbs) = decide (q ≟ p) U
  where
    decide :
      Dec (q ≡ p)
      → (U : Observable)
      → Dec (Σ Local₀ (λ T' → bra p bs -[ q ?⟨ U ⟩ ]→ₗ T'))
    decide (no q≢p) U = no λ where
      (_ , LR4 hit) → q≢p refl
    decide (yes q≡p) (obsBase B) = no λ where ()
    decide (yes q≡p) (obsLabel l) with lookupB l bs in eq
    ... | nothing = no λ where
      (_ , LR4 hit) → nothing≢just (trans (sym hit) eq)
    ... | just t rewrite q≡p = yes (t , LR4 eq)
recv-step? {q = q} {U = U} (wf-mu g wunf) with recv-step? {q = q} {U = U} wunf
... | yes (T' , step) = yes (T' , LR5 step)
... | no ¬step = no λ where
    (_ , LR5 step) → ¬step ( _ , step)

tag-step-target' :
  ∀ {Δ₀ p ζ Δ₁}
  → (red : Δ₀ -[ p ∶ ζ ]→₁ Δ₁)
  → Σ Local₀ (λ T' → (Δ₀ p -[ ζ ]→ₗ T') × (Δ₁ ≡ updateΔ p T' Δ₀))
tag-step-target' (LTag step) = _ , (step , refl)

canSync₂? :
  ∀ (Δ₀ : Δ)
  → wfΔ Δ₀
  → (p q : Participant)
  → (U : Observable)
  → Dec (CanSync₂ Δ₀ p q U)
canSync₂? Δ₀ wΔ p q U
  with send-step? {T = Δ₀ p} {q = q} {U = U} (wΔ p)
     | recv-step? {T = Δ₀ q} {q = p} {U = U} (wΔ q)
... | yes (Tp' , pStep) | yes (Tq' , qStep) =
  yes
    ( updateΔ q Tq' (updateΔ p Tp' Δ₀)
    , LEnv (LTag pStep) (LTag qStep)
    )
... | no ¬p | _ = no λ where
    (Δ₁ , LEnv pRed qRed) →
      let p-info = tag-step-target' pRed in
      ¬p (proj₁ p-info , proj₁ (proj₂ p-info))
... | _ | no ¬q = no λ where
    (Δ₁ , LEnv pRed qRed) →
      let q-info = tag-step-target' qRed in
      ¬q (proj₁ q-info , proj₁ (proj₂ q-info))

canStep₂? :
  ∀ (Δ₀ : Δ)
  → wfΔ Δ₀
  → Dec (S.CanStep₂ Δ₀)
canStep₂? Δ₀ wΔ
  with findFin
         (λ p →
           Σ Participant (λ q →
           Σ Observable (λ U →
             CanSync₂ Δ₀ p q U)))
         (λ p →
            findFin
              (λ q →
                Σ Observable (λ U →
                  CanSync₂ Δ₀ p q U))
              (λ q →
                 findObservable
                   (λ U → CanSync₂ Δ₀ p q U)
                   (λ U → canSync₂? Δ₀ wΔ p q U)))
... | yes (p , (q , (U , (Δ₁ , sync)))) =
  yes (Δ₁ , ((p ↝⟨ U ⟩ q) , sync))
... | no ¬sync = no λ where
    (Δ₁ , ((p ↝⟨ U ⟩ q) , sync)) → ¬sync (p , (q , (U , (Δ₁ , sync))))

stuck₂? :
  ∀ (Δ₀ : Δ)
  → wfΔ Δ₀
  → Dec (S.Stuck₂ Δ₀)
stuck₂? Δ₀ wΔ with canStep₂? Δ₀ wΔ
... | yes canStep = no (λ stuck → stuck canStep)
... | no stuck    = yes stuck

stepStatus :
  ∀ (Δ₀ : Δ)
  → wfΔ Δ₀
  → S.Stuck₂ Δ₀ ⊎ S.CanStep₂ Δ₀
stepStatus Δ₀ wΔ with canStep₂? Δ₀ wΔ
... | yes canStep = inj₂ canStep
... | no stuck    = inj₁ stuck

------------------------------------------------------------------------
-- One-sided action monotonicity helper
------------------------------------------------------------------------

selM-right-just :
  ∀ {a mb}
  → SelM R (just a) mb
  → Σ Local₀ (λ b → mb ≡ just b)
selM-right-just (sel-just r) = _ , refl

selM-right-just≤ :
  ∀ {a mb}
  → SelM R (just a) mb
  → Σ Local₀ (λ b → (mb ≡ just b) × (a ≤ b))
selM-right-just≤ (sel-just r) = _ , (refl , force r)

sel-dom-hit :
  ∀ {bs bs' l t}
  → lookupB l bs ≡ just t
  → Sub.SelDom≤ R bs bs'
  → Σ Local₀ (λ u → lookupB l bs' ≡ just u)
sel-dom-hit {bs = bs} {bs' = bs'} {l = l} hit dom
  with selM-right-just (subst (λ m → SelM R m (lookupB l bs')) hit (dom l))
... | u , hit' = u , hit'

send-step-up-≤ₗ-w :
  ∀ {T U T' q Obs}
  → wf U
  → T ≤ U
  → T -[ q !⟨ Obs ⟩ ]→ₗ T'
  → Σ Local₀ (λ U' → U -[ q !⟨ Obs ⟩ ]→ₗ U')
send-step-up-≤ₗ-w wU TU LR1 with out TU
... | s-send r = _ , LR1
... | s-muR r with wU
...   | wf-mu _ wunf with send-step-up-≤ₗ-w wunf (force r) LR1
...     | U' , stepU = U' , LR5 stepU
send-step-up-≤ₗ-w wU TU (LR3 {l = l} hit) with out TU
... | s-sel {bs = bs} {bs' = bs'} dom =
  let rightHit = sel-dom-hit {bs = bs} {bs' = bs'} {l = l} hit dom in
  proj₁ rightHit , LR3 (proj₂ rightHit)
... | s-muR r with wU
...   | wf-mu _ wunf with send-step-up-≤ₗ-w wunf (force r) (LR3 {l = l} hit)
...     | U' , stepU = U' , LR5 stepU
send-step-up-≤ₗ-w wU TU (LR5 step) with out TU
... | s-muL r = send-step-up-≤ₗ-w wU (force r) step
... | s-muR r with wU
...   | wf-mu _ wunf with send-step-up-≤ₗ-w wunf (force r) (LR5 step)
...     | U' , stepU = U' , LR5 stepU

send-step-up-≤ₗ :
  ∀ {T U T' q Obs}
  → T ≤ U
  → T -[ q !⟨ Obs ⟩ ]→ₗ T'
  → Σ Local₀ (λ U' → U -[ q !⟨ Obs ⟩ ]→ₗ U')
send-step-up-≤ₗ TU step = send-step-up-≤ₗ-w (wf-right TU) TU step

send-step-up-≤ₗ≤-w :
  ∀ {T U T' q Obs}
  → wf U
  → T ≤ U
  → T -[ q !⟨ Obs ⟩ ]→ₗ T'
  → Σ Local₀ (λ U' → (U -[ q !⟨ Obs ⟩ ]→ₗ U') × (T' ≤ U'))
send-step-up-≤ₗ≤-w wU TU LR1 with out TU
... | s-send r = _ , (LR1 , force r)
... | s-muR r with wU
...   | wf-mu _ wunf with send-step-up-≤ₗ≤-w wunf (force r) LR1
...     | U' , (stepU , rel) = U' , (LR5 stepU , rel)
send-step-up-≤ₗ≤-w wU TU (LR3 {l = l} hit) with out TU
... | s-sel {bs' = bs'} dom =
  let right = selM-right-just≤ (subst (λ m → SelM R m (lookupB l bs')) hit (dom l)) in
  proj₁ right , (LR3 (proj₁ (proj₂ right)) , proj₂ (proj₂ right))
... | s-muR r with wU
...   | wf-mu _ wunf with send-step-up-≤ₗ≤-w wunf (force r) (LR3 {l = l} hit)
...     | U' , (stepU , rel) = U' , (LR5 stepU , rel)
send-step-up-≤ₗ≤-w wU TU (LR5 step) with out TU
... | s-muL r = send-step-up-≤ₗ≤-w wU (force r) step
... | s-muR r with wU
...   | wf-mu _ wunf with send-step-up-≤ₗ≤-w wunf (force r) (LR5 step)
...     | U' , (stepU , rel) = U' , (LR5 stepU , rel)

send-step-up-≤ₗ≤ :
  ∀ {T U T' q Obs}
  → T ≤ U
  → T -[ q !⟨ Obs ⟩ ]→ₗ T'
  → Σ Local₀ (λ U' → (U -[ q !⟨ Obs ⟩ ]→ₗ U') × (T' ≤ U'))
send-step-up-≤ₗ≤ TU step = send-step-up-≤ₗ≤-w (wf-right TU) TU step

send-step-up-≤₁ :
  ∀ {Δ₀ Δ₁ p q Obs Δp}
  → Δ₀ ≤Δ Δ₁
  → Δ₀ -[ p ∶ (q !⟨ Obs ⟩) ]→₁ Δp
  → Σ Δ (λ Δp' → Δ₁ -[ p ∶ (q !⟨ Obs ⟩) ]→₁ Δp')
send-step-up-≤₁ {Δ₀} {Δ₁} Δ₀≤Δ₁ (LTag {Δ₀ = Δ₀} {p} step)
  with send-step-up-≤ₗ (Δ₀≤Δ₁ p) step
... | T' , step' = updateΔ p T' Δ₁ , LTag step'

braM-left-just :
  ∀ {ma b}
  → BraM R ma (just b)
  → Σ Local₀ (λ a → ma ≡ just a)
braM-left-just (bra-just r) = _ , refl

braM-left-just≤ :
  ∀ {ma b}
  → BraM R ma (just b)
  → Σ Local₀ (λ a → (ma ≡ just a) × (a ≤ b))
braM-left-just≤ (bra-just r) = _ , (refl , force r)

bra-dom-hit :
  ∀ {bs bs' l u}
  → lookupB l bs' ≡ just u
  → Sub.BraDom≤ R bs bs'
  → Σ Local₀ (λ t → lookupB l bs ≡ just t)
bra-dom-hit {bs = bs} {bs' = bs'} {l = l} hit dom
  with braM-left-just (subst (λ m → BraM R (lookupB l bs) m) hit (dom l))
... | t , hit' = t , hit'

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

det-send :
  ∀ {T p Obs T₁ T₂}
  → T -[ p !⟨ Obs ⟩ ]→ₗ T₁
  → T -[ p !⟨ Obs ⟩ ]→ₗ T₂
  → T₁ ≡ T₂
det-send LR1 LR1 = refl
det-send (LR3 hit₁) (LR3 hit₂) = just-injective (trans (sym hit₁) hit₂)
det-send (LR5 s₁) (LR5 s₂) = det-send s₁ s₂

det-recv :
  ∀ {T p Obs T₁ T₂}
  → T -[ p ?⟨ Obs ⟩ ]→ₗ T₁
  → T -[ p ?⟨ Obs ⟩ ]→ₗ T₂
  → T₁ ≡ T₂
det-recv LR2 LR2 = refl
det-recv (LR4 hit₁) (LR4 hit₂) = just-injective (trans (sym hit₁) hit₂)
det-recv (LR5 s₁) (LR5 s₂) = det-recv s₁ s₂

recv-step-down-≤ₗ-w :
  ∀ {T U U' q Obs}
  → wf T
  → T ≤ U
  → U -[ q ?⟨ Obs ⟩ ]→ₗ U'
  → Σ Local₀ (λ T' → T -[ q ?⟨ Obs ⟩ ]→ₗ T')
recv-step-down-≤ₗ-w wT TU LR2 with out TU
... | s-recv r = _ , LR2
... | s-muL r with wT
...   | wf-mu _ wunf with recv-step-down-≤ₗ-w wunf (force r) LR2
...     | T' , stepT = T' , LR5 stepT
recv-step-down-≤ₗ-w wT TU (LR4 {l = l} hit) with out TU
... | s-bra {bs = bs} {bs' = bs'} dom =
  let leftHit = bra-dom-hit {bs = bs} {bs' = bs'} {l = l} hit dom in
  proj₁ leftHit , LR4 (proj₂ leftHit)
... | s-muL r with wT
...   | wf-mu _ wunf with recv-step-down-≤ₗ-w wunf (force r) (LR4 {l = l} hit)
...     | T' , stepT = T' , LR5 stepT
recv-step-down-≤ₗ-w wT TU (LR5 step) with out TU
... | s-muR r = recv-step-down-≤ₗ-w wT (force r) step
... | s-muL r with wT
...   | wf-mu _ wunf with recv-step-down-≤ₗ-w wunf (force r) (LR5 step)
...     | T' , stepT = T' , LR5 stepT

recv-step-down-≤ₗ :
  ∀ {T U U' q Obs}
  → T ≤ U
  → U -[ q ?⟨ Obs ⟩ ]→ₗ U'
  → Σ Local₀ (λ T' → T -[ q ?⟨ Obs ⟩ ]→ₗ T')
recv-step-down-≤ₗ TU step = recv-step-down-≤ₗ-w (wf-left TU) TU step

recv-step-down-≤ₗ≤-w :
  ∀ {T U U' q Obs}
  → wf T
  → T ≤ U
  → U -[ q ?⟨ Obs ⟩ ]→ₗ U'
  → Σ Local₀ (λ T' → (T -[ q ?⟨ Obs ⟩ ]→ₗ T') × (T' ≤ U'))
recv-step-down-≤ₗ≤-w wT TU LR2 with out TU
... | s-recv r = _ , (LR2 , force r)
... | s-muL r with wT
...   | wf-mu _ wunf with recv-step-down-≤ₗ≤-w wunf (force r) LR2
...     | T' , (stepT , rel) = T' , (LR5 stepT , rel)
recv-step-down-≤ₗ≤-w wT TU (LR4 {l = l} hit) with out TU
... | s-bra {bs = bs} {bs' = bs'} dom =
  let left = braM-left-just≤ (subst (λ m → BraM R (lookupB l bs) m) hit (dom l)) in
  proj₁ left , (LR4 (proj₁ (proj₂ left)) , proj₂ (proj₂ left))
... | s-muL r with wT
...   | wf-mu _ wunf with recv-step-down-≤ₗ≤-w wunf (force r) (LR4 {l = l} hit)
...     | T' , (stepT , rel) = T' , (LR5 stepT , rel)
recv-step-down-≤ₗ≤-w wT TU (LR5 step) with out TU
... | s-muR r = recv-step-down-≤ₗ≤-w wT (force r) step
... | s-muL r with wT
...   | wf-mu _ wunf with recv-step-down-≤ₗ≤-w wunf (force r) (LR5 step)
...     | T' , (stepT , rel) = T' , (LR5 stepT , rel)

recv-step-down-≤ₗ≤ :
  ∀ {T U U' q Obs}
  → T ≤ U
  → U -[ q ?⟨ Obs ⟩ ]→ₗ U'
  → Σ Local₀ (λ T' → (T -[ q ?⟨ Obs ⟩ ]→ₗ T') × (T' ≤ U'))
recv-step-down-≤ₗ≤ TU step = recv-step-down-≤ₗ≤-w (wf-left TU) TU step

recv-step-down-≤₁ :
  ∀ {Δ₀ Δ₁ p q Obs Δq}
  → Δ₀ ≤Δ Δ₁
  → Δ₁ -[ p ∶ (q ?⟨ Obs ⟩) ]→₁ Δq
  → Σ Δ (λ Δq' → Δ₀ -[ p ∶ (q ?⟨ Obs ⟩) ]→₁ Δq')
recv-step-down-≤₁ {Δ₀} {Δ₁} Δ₀≤Δ₁ (LTag {Δ₀ = Δ₁} {p} step)
  with recv-step-down-≤ₗ (Δ₀≤Δ₁ p) step
... | T' , step' = updateΔ p T' Δ₀ , LTag step'

recv-step-up-any-≤ₗ-w :
  ∀ {T U T' q Obs}
  → wf U
  → T ≤ U
  → T -[ q ?⟨ Obs ⟩ ]→ₗ T'
  → Σ Observable (λ Obs' → Σ Local₀ (λ U' → U -[ q ?⟨ Obs' ⟩ ]→ₗ U'))
recv-step-up-any-≤ₗ-w wU TU LR2 with out TU
... | s-recv r = _ , (_ , LR2)
... | s-muR r with wU
...   | wf-mu _ wunf with recv-step-up-any-≤ₗ-w wunf (force r) LR2
...     | Obs' , (U' , stepU) = Obs' , (U' , LR5 stepU)
recv-step-up-any-≤ₗ-w (wf-bra (l' , u' , hit') wbs) TU (LR4 {l = l} hit) with out TU
... | s-bra {bs' = bs'} dom = obsLabel l' , (u' , LR4 hit')
recv-step-up-any-≤ₗ-w (wf-mu _ wunf) TU (LR4 {l = l} hit) with out TU
... | s-muR r with recv-step-up-any-≤ₗ-w wunf (force r) (LR4 {l = l} hit)
...     | Obs' , (U' , stepU) = Obs' , (U' , LR5 stepU)
recv-step-up-any-≤ₗ-w wf-end TU (LR4 hit) with out TU
... | ()
recv-step-up-any-≤ₗ-w (wf-send wT) TU (LR4 hit) with out TU
... | ()
recv-step-up-any-≤ₗ-w (wf-recv wT) TU (LR4 hit) with out TU
... | ()
recv-step-up-any-≤ₗ-w (wf-sel ne wbs) TU (LR4 hit) with out TU
... | ()
recv-step-up-any-≤ₗ-w wU TU (LR5 step) with out TU
... | s-muL r = recv-step-up-any-≤ₗ-w wU (force r) step
... | s-muR r with wU
...   | wf-mu _ wunf with recv-step-up-any-≤ₗ-w wunf (force r) (LR5 step)
...     | Obs' , (U' , stepU) = Obs' , (U' , LR5 stepU)

recv-step-up-any-≤ₗ :
  ∀ {T U T' q Obs}
  → T ≤ U
  → T -[ q ?⟨ Obs ⟩ ]→ₗ T'
  → Σ Observable (λ Obs' → Σ Local₀ (λ U' → U -[ q ?⟨ Obs' ⟩ ]→ₗ U'))
recv-step-up-any-≤ₗ TU step = recv-step-up-any-≤ₗ-w (wf-right TU) TU step

recv-step-up-any-≤₁ :
  ∀ {Δ₀ Δ₁ p q Obs Δq}
  → Δ₀ ≤Δ Δ₁
  → Δ₀ -[ p ∶ (q ?⟨ Obs ⟩) ]→₁ Δq
  → Σ Observable (λ Obs' → Σ Δ (λ Δq' → Δ₁ -[ p ∶ (q ?⟨ Obs' ⟩) ]→₁ Δq'))
recv-step-up-any-≤₁ {Δ₀} {Δ₁} Δ₀≤Δ₁ (LTag {Δ₀ = Δ₀} {p} step)
  with recv-step-up-any-≤ₗ (Δ₀≤Δ₁ p) step
... | Obs' , (T' , step') = Obs' , (updateΔ p T' Δ₁ , LTag step')

send-step-down-any-≤ₗ-w :
  ∀ {T U U' q Obs}
  → wf T
  → T ≤ U
  → U -[ q !⟨ Obs ⟩ ]→ₗ U'
  → Σ Observable (λ Obs' → Σ Local₀ (λ T' → T -[ q !⟨ Obs' ⟩ ]→ₗ T'))
send-step-down-any-≤ₗ-w wT TU LR1 with out TU
... | s-send r = _ , (_ , LR1)
... | s-muL r with wT
...   | wf-mu _ wunf with send-step-down-any-≤ₗ-w wunf (force r) LR1
...     | Obs' , (T' , stepT) = Obs' , (T' , LR5 stepT)
send-step-down-any-≤ₗ-w (wf-sel (l' , t' , hit') wbs) TU (LR3 {l = l} hit) with out TU
... | s-sel {bs = bs} {bs' = bs'} dom = obsLabel l' , (t' , LR3 hit')
send-step-down-any-≤ₗ-w (wf-mu _ wunf) TU (LR3 {l = l} hit) with out TU
... | s-muL r with send-step-down-any-≤ₗ-w wunf (force r) (LR3 {l = l} hit)
...     | Obs' , (T' , stepT) = Obs' , (T' , LR5 stepT)
send-step-down-any-≤ₗ-w wf-end TU (LR3 hit) with out TU
... | ()
send-step-down-any-≤ₗ-w (wf-send wT) TU (LR3 hit) with out TU
... | ()
send-step-down-any-≤ₗ-w (wf-recv wT) TU (LR3 hit) with out TU
... | ()
send-step-down-any-≤ₗ-w (wf-bra ne wbs) TU (LR3 hit) with out TU
... | ()
send-step-down-any-≤ₗ-w wT TU (LR5 step) with out TU
... | s-muR r = send-step-down-any-≤ₗ-w wT (force r) step
... | s-muL r with wT
...   | wf-mu _ wunf with send-step-down-any-≤ₗ-w wunf (force r) (LR5 step)
...     | Obs' , (T' , stepT) = Obs' , (T' , LR5 stepT)

send-step-down-any-≤ₗ :
  ∀ {T U U' q Obs}
  → T ≤ U
  → U -[ q !⟨ Obs ⟩ ]→ₗ U'
  → Σ Observable (λ Obs' → Σ Local₀ (λ T' → T -[ q !⟨ Obs' ⟩ ]→ₗ T'))
send-step-down-any-≤ₗ TU step = send-step-down-any-≤ₗ-w (wf-left TU) TU step

send-step-down-any-≤₁ :
  ∀ {Δ₀ Δ₁ p q Obs Δp}
  → Δ₀ ≤Δ Δ₁
  → Δ₁ -[ p ∶ (q !⟨ Obs ⟩) ]→₁ Δp
  → Σ Observable (λ Obs' → Σ Δ (λ Δp' → Δ₀ -[ p ∶ (q !⟨ Obs' ⟩) ]→₁ Δp'))
send-step-down-any-≤₁ {Δ₀} {Δ₁} Δ₀≤Δ₁ (LTag {Δ₀ = Δ₁} {p} step)
  with send-step-down-any-≤ₗ (Δ₀≤Δ₁ p) step
... | Obs' , (T' , step') = Obs' , (updateΔ p T' Δ₀ , LTag step')

canSend-up-≤ :
  ∀ {Δ₀ Δ₁ p q}
  → Δ₀ ≤Δ Δ₁
  → S.CanSend₁ Δ₀ p q
  → S.CanSend₁ Δ₁ p q
canSend-up-≤ Δ₀≤Δ₁ (Δp , (Obs , pRed))
  with send-step-up-≤₁ Δ₀≤Δ₁ pRed
... | Δp' , pRed' = Δp' , (Obs , pRed')

canSend-down-any-≤ :
  ∀ {Δ₀ Δ₁ p q}
  → Δ₀ ≤Δ Δ₁
  → S.CanSend₁ Δ₁ p q
  → S.CanSend₁ Δ₀ p q
canSend-down-any-≤ Δ₀≤Δ₁ (Δp , (Obs , pRed))
  with send-step-down-any-≤₁ Δ₀≤Δ₁ pRed
... | Obs' , (Δp' , pRed') = Δp' , (Obs' , pRed')

canRecv-up-any-≤ :
  ∀ {Δ₀ Δ₁ p q}
  → Δ₀ ≤Δ Δ₁
  → S.CanRecv₁ Δ₀ p q
  → S.CanRecv₁ Δ₁ p q
canRecv-up-any-≤ Δ₀≤Δ₁ (Δq , (Obs , qRed))
  with recv-step-up-any-≤₁ Δ₀≤Δ₁ qRed
... | Obs' , (Δq' , qRed') = Δq' , (Obs' , qRed')

canRecv-down-≤ :
  ∀ {Δ₀ Δ₁ p q}
  → Δ₀ ≤Δ Δ₁
  → S.CanRecv₁ Δ₁ p q
  → S.CanRecv₁ Δ₀ p q
canRecv-down-≤ Δ₀≤Δ₁ (Δq , (Obs , qRed))
  with recv-step-down-≤₁ Δ₀≤Δ₁ qRed
... | Δq' , qRed' = Δq' , (Obs , qRed')

update≤ :
  ∀ {Δ₀ Δ₁ p T U}
  → Δ₀ ≤Δ Δ₁
  → T ≤ U
  → updateΔ p T Δ₀ ≤Δ updateΔ p U Δ₁
update≤ {p = p} Δ₀≤Δ₁ T≤U r with r ≟ p
... | yes rp rewrite rp = T≤U
... | no _ = Δ₀≤Δ₁ r

update-self :
  ∀ {Δ₀ p T}
  → updateΔ p T Δ₀ p ≡ T
update-self {p = p} with p ≟ p
... | yes _ = refl
... | no p≢p = ⊥-elim (p≢p refl)

update-head-eq :
  ∀ {Δ₀ p T U}
  → updateΔ p T Δ₀ ≡ updateΔ p U Δ₀
  → T ≡ U
update-head-eq {Δ₀} {p} {T} {U} eq =
  trans (sym (update-self {Δ₀} {p} {T}))
        (trans (cong (λ Δ' → Δ' p) eq) (update-self {Δ₀} {p} {U}))

tag-step-target :
  ∀ {Δ₀ p ζ Δ₁}
  → (red : Δ₀ -[ p ∶ ζ ]→₁ Δ₁)
  → Σ Local₀ (λ T' → (Δ₀ p -[ ζ ]→ₗ T') × (Δ₁ ≡ updateΔ p T' Δ₀))
tag-step-target (LTag step) = _ , (step , refl)

------------------------------------------------------------------------
-- Assumptions connecting subtyping with semantics
------------------------------------------------------------------------

-- One unlabeled two-sided step of a subtype can be matched by the supertype.
stepSim≤ :
  ∀ {Δ₀ Δ₁ Δ₀'}
  → Δ₀ ≤Δ Δ₁
  → SafeState Δ₁
  → Δ₀ →₂ Δ₀'
  → Σ Δ (λ Δ₁' → (Δ₁ →₂ Δ₁') × (Δ₀' ≤Δ Δ₁'))
stepSim≤ {Δ₀ = Δsub} {Δ₁ = Δsup} Δsub≤Δsup sΔsup
  (ι , LEnv {Δ₀ = Δsub} {p = p} {q = q} {U = U} {Tp' = Tp'} {Tq' = Tq'} pRedsub qRedsub)
  with tag-step-target pRedsub | tag-step-target qRedsub
... | Tpsub' , (pLocsub , pCtxEqSub) | Tqsub' , (qLocsub , qCtxEqSub)
  with send-step-up-≤ₗ≤ (Δsub≤Δsup p) pLocsub
... | Tpsup₁' , (pLocsup₁ , pRel)
  with recv-step-up-any-≤₁ Δsub≤Δsup (LTag qLocsub)
... | Obs'' , ΔqAny , qRedAny
  with sΔsup (LTag pLocsup₁) qRedAny
... | Δsup' , syncSup
  with syncSup
... | LEnv {Tp' = Tp''} {Tq' = Tq''} pRedsup qRedsup
  with tag-step-target pRedsup | tag-step-target qRedsup
... | Tpsup₂' , (pLocsup₂ , pCtxEqSup) | Tqsup' , (qLocsup , qCtxEqSup)
  with det-send pLocsup₁ pLocsup₂
... | pEq
  with recv-step-down-≤ₗ≤ (Δsub≤Δsup q) qLocsup
... | Tqsub₁' , (qLocsub₁ , qRel)
  with det-recv qLocsub qLocsub₁
... | qEq =
  Δsup' , ((ι , syncSup) ,
           update≤ (update≤ Δsub≤Δsup relP) relQ)
  where
    relP : Tp' ≤ Tp''
    relP rewrite update-head-eq pCtxEqSub
               | pEq
               | sym (update-head-eq pCtxEqSup) = pRel

    relQ : Tq' ≤ Tq''
    relQ rewrite update-head-eq qCtxEqSub
               | qEq
               | sym (update-head-eq qCtxEqSup) = qRel

stepSim≤-pair :
  ∀ {Δ₀ Δ₁ Δ₀' p q Obs}
  → Δ₀ ≤Δ Δ₁
  → SafeState Δ₁
  → Δ₀ -[ S._↝⟨_⟩_ p Obs q ]→₂ Δ₀'
  → Σ Δ (λ Δ₁' → (Δ₁ -[ S._↝⟨_⟩_ p Obs q ]→₂ Δ₁') × (Δ₀' ≤Δ Δ₁'))
stepSim≤-pair {Δ₀ = Δsub} {Δ₁ = Δsup} {p = p} {q = q} {Obs = Obs} Δsub≤Δsup sΔsup
  (LEnv {Δ₀ = Δsub} {p = p} {q = q} {U = Obs} {Tp' = Tp'} {Tq' = Tq'} pRedsub qRedsub)
  with tag-step-target pRedsub | tag-step-target qRedsub
... | Tpsub' , (pLocsub , pCtxEqSub) | Tqsub' , (qLocsub , qCtxEqSub)
  with send-step-up-≤ₗ≤ (Δsub≤Δsup p) pLocsub
... | Tpsup₁' , (pLocsup₁ , pRel)
  with recv-step-up-any-≤₁ Δsub≤Δsup (LTag qLocsub)
... | Obs'' , ΔqAny , qRedAny
  with sΔsup (LTag pLocsup₁) qRedAny
... | Δsup' , syncSup
  with syncSup
... | LEnv {Tp' = Tp''} {Tq' = Tq''} pRedsup qRedsup
  with tag-step-target pRedsup | tag-step-target qRedsup
... | Tpsup₂' , (pLocsup₂ , pCtxEqSup) | Tqsup' , (qLocsup , qCtxEqSup)
  with det-send pLocsup₁ pLocsup₂
... | pEq
  with recv-step-down-≤ₗ≤ (Δsub≤Δsup q) qLocsup
... | Tqsub₁' , (qLocsub₁ , qRel)
  with det-recv qLocsub qLocsub₁
... | qEq =
  Δsup' , (syncSup ,
           update≤ (update≤ Δsub≤Δsup relP) relQ)
  where
    relP : Tp' ≤ Tp''
    relP rewrite update-head-eq pCtxEqSub
               | pEq
               | sym (update-head-eq pCtxEqSup) = pRel

    relQ : Tq' ≤ Tq''
    relQ rewrite update-head-eq qCtxEqSub
               | qEq
               | sym (update-head-eq qCtxEqSup) = qRel

-- Safe-state predicate is downward closed wrt pointwise context subtyping.
safeStateDownward :
  ∀ {Δ₀ Δ₁}
  → Δ₀ ≤Δ Δ₁
  → SafeState Δ₁
  → SafeState Δ₀
safeStateDownward Δ₀≤Δ₁ sΔ₁ {p} {q} {Obs} {Obs'} {Δp} {Δq} pSend qRecv
  with send-step-up-≤₁ Δ₀≤Δ₁ pSend
     | recv-step-up-any-≤₁ Δ₀≤Δ₁ qRecv
... | Δp₁ , pSend₁ | Obs'' , Δq₁ , qRecv₁
  with sΔ₁ pSend₁ qRecv₁
... | Δsync₁ , LEnv pStep₁ qStep₁
  with recv-step-down-≤₁ Δ₀≤Δ₁ qStep₁
... | Δq₀ , qStep₀ with pSend
...   | LTag pStep₀ with qStep₀
...     | LTag qStep₀' = _ , LEnv (LTag pStep₀) (LTag qStep₀')

pair-down-≤ :
  ∀ {Δ₀ Δ₁ p q}
  → Δ₀ ≤Δ Δ₁
  → SafeState Δ₁
  → S.CanPair₂ Δ₁ p q
  → S.CanPair₂ Δ₀ p q
pair-down-≤ Δ₀≤Δ₁ sΔ₁ (Δ₁' , (Obs , LEnv {p = p} {q = q} pRed₁ qRed₁))
  with send-step-down-any-≤₁ Δ₀≤Δ₁ pRed₁
... | Obs' , (Δp₀ , pRed₀)
  with recv-step-down-≤₁ Δ₀≤Δ₁ qRed₁
... | Δq₀ , qRed₀
  with safeStateDownward Δ₀≤Δ₁ sΔ₁ pRed₀ qRed₀
... | Δsync₀ , sync₀ = Δsync₀ , (Obs' , sync₀)

canStep-down-≤ :
  ∀ {Δ₀ Δ₁}
  → Δ₀ ≤Δ Δ₁
  → SafeState Δ₁
  → S.CanStep₂ Δ₁
  → S.CanStep₂ Δ₀
canStep-down-≤ Δ₀≤Δ₁ sΔ₁ (Δ₁' , (S._↝⟨_⟩_ p Obs q , red₁))
  with pair-down-≤ {p = p} {q = q} Δ₀≤Δ₁ sΔ₁ (Δ₁' , (Obs , red₁))
... | Δ₀' , (Obs' , red₀) = Δ₀' , (_ , red₀)

stuck-up-≤ :
  ∀ {Δ₀ Δ₁}
  → Δ₀ ≤Δ Δ₁
  → SafeState Δ₁
  → S.Stuck₂ Δ₀
  → S.Stuck₂ Δ₁
stuck-up-≤ Δ₀≤Δ₁ sΔ₁ stuck₀ canStep₁ =
  stuck₀ (canStep-down-≤ Δ₀≤Δ₁ sΔ₁ canStep₁)

------------------------------------------------------------------------
-- Lifting step simulation to reflexive-transitive closure
------------------------------------------------------------------------

safe-tail :
  ∀ {Δ₀ Δ₁}
  → safe Δ₀
  → Δ₀ →₂ Δ₁
  → safe Δ₁
safe-tail sΔ₀ step {Δ₂} Δ₁→₂*Δ₂ =
  sΔ₀ (rtc-step step Δ₁→₂*Δ₂)

stepSim-rtc :
  (∀ {Δ₀ Δ₁ Δ₀'}
   → Δ₀ ≤Δ Δ₁
   → SafeState Δ₁
   → Δ₀ →₂ Δ₀'
   → Σ Δ (λ Δ₁' → (Δ₁ →₂ Δ₁') × (Δ₀' ≤Δ Δ₁')))
  → ∀ {Δ₀ Δ₁ Δ₂}
  → Δ₀ ≤Δ Δ₁
  → safe Δ₁
  → Δ₀ →₂* Δ₂
  → Σ Δ (λ Δ₃ → (Δ₁ →₂* Δ₃) × (Δ₂ ≤Δ Δ₃))
stepSim-rtc sim {Δ₁ = Δ₁} Δ₀≤Δ₁ sΔ₁ rtc-refl =
  Δ₁ , (rtc-refl , Δ₀≤Δ₁)
stepSim-rtc sim Δ₀≤Δ₁ sΔ₁ (rtc-step step rest)
  with sim Δ₀≤Δ₁ (sΔ₁ rtc-refl) step
... | Δ₁' , (step' , Δ₀'≤Δ₁')
  with stepSim-rtc sim Δ₀'≤Δ₁' (safe-tail sΔ₁ step') rest
... | Δ₃ , (Δ₁'→₂*Δ₃ , Δ₂≤Δ₃) =
  Δ₃ , (rtc-step step' Δ₁'→₂*Δ₃ , Δ₂≤Δ₃)

------------------------------------------------------------------------
-- Main result: safety is downward closed under context subtyping
------------------------------------------------------------------------

safe-downward-≤-with :
  (∀ {Δ₀ Δ₁ Δ₀'}
   → Δ₀ ≤Δ Δ₁
   → SafeState Δ₁
   → Δ₀ →₂ Δ₀'
   → Σ Δ (λ Δ₁' → (Δ₁ →₂ Δ₁') × (Δ₀' ≤Δ Δ₁')))
  → ∀ {Δ₀ Δ₁}
  → Δ₀ ≤Δ Δ₁
  → safe Δ₁
  → safe Δ₀
safe-downward-≤-with sim Δ₀≤Δ₁ sΔ₁ {Δ₂} Δ₀→₂*Δ₂
  with stepSim-rtc sim Δ₀≤Δ₁ sΔ₁ Δ₀→₂*Δ₂
... | Δ₃ , (Δ₁→₂*Δ₃ , Δ₂≤Δ₃) =
  safeStateDownward Δ₂≤Δ₃ (sΔ₁ Δ₁→₂*Δ₃)

safe-downward-≤ :
  ∀ {Δ₀ Δ₁}
  → Δ₀ ≤Δ Δ₁
  → safe Δ₁
  → safe Δ₀
safe-downward-≤ = safe-downward-≤-with stepSim≤

------------------------------------------------------------------------
-- Main result: liveness is downward closed under context subtyping
------------------------------------------------------------------------

-- Any fair trace of the subtype can be lifted to a fair trace of the
-- supertype, and liveness of that lifted trace implies liveness
-- of the original trace.
mutual
  liftTrace :
    ∀ {Δ₀ Δ₁}
    → Δ₀ ≤Δ Δ₁
    → safe Δ₁
    → Trace Δ₀
    → Trace Δ₁
  unfoldᵗ (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀) with unfoldᵗ τ₀
  ... | S.tstop stuck₀ =
    S.tstop (stuck-up-≤ Δ₀≤Δ₁ (sΔ₁ rtc-refl) stuck₀)
  ... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀'
    with stepSim≤-pair Δ₀≤Δ₁ (sΔ₁ rtc-refl) red₀
  ... | Δ₁' , (red₁ , Δ₀'≤Δ₁') =
    S.tstep (S._↝⟨_⟩_ r Obs s , red₁)
            (liftTrace Δ₀'≤Δ₁' (safe-tail sΔ₁ (S._↝⟨_⟩_ r Obs s , red₁)) τ₀')

  eventuallyPair-lift :
    ∀ {Δ₀ Δ₁ p q}
    → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
    → (sΔ₁ : safe Δ₁)
    → (τ₀ : Trace Δ₀)
    → S.EventuallyPair p q τ₀
    → S.EventuallyPair p q (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀)
  eventuallyPair-lift {p = p} {q = q} Δ₀≤Δ₁ sΔ₁ τ₀ ev with unfoldᵗ τ₀ | ev
  ... | S.tstop stuck₀ | ()
  ... | S.tstep (S._↝⟨_⟩_ p Obs₀ q , red₀) τ₀' | S.ev-here (Obs₀ , red₀)
    =
      let sim = stepSim≤-pair Δ₀≤Δ₁ (sΔ₁ rtc-refl) red₀ in
      S.ev-here (Obs₀ , proj₁ (proj₂ sim))
  ... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀' | S.ev-next ev'
    =
      let sim = stepSim≤-pair Δ₀≤Δ₁ (sΔ₁ rtc-refl) red₀ in
      let red₁ = proj₁ (proj₂ sim) in
      let Δ₀'≤Δ₁' = proj₂ (proj₂ sim) in
      S.ev-next
        (eventuallyPair-lift Δ₀'≤Δ₁'
                             (safe-tail sΔ₁ (S._↝⟨_⟩_ r Obs s , red₁))
                             τ₀'
                             ev')

  fair-lift :
    ∀ {Δ₀ Δ₁}
    → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
    → (sΔ₁ : safe Δ₁)
    → (τ₀ : Trace Δ₀)
    → Fair τ₀
    → Fair (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀)
  S.fair-here (fair-lift Δ₀≤Δ₁ sΔ₁ τ₀ fairτ₀) p q canPair₁ =
    eventuallyPair-lift Δ₀≤Δ₁ sΔ₁ τ₀
      (S.fair-here fairτ₀ p q (pair-down-≤ Δ₀≤Δ₁ (sΔ₁ rtc-refl) canPair₁))
  S.fair-next (fair-lift Δ₀≤Δ₁ sΔ₁ τ₀ fairτ₀) =
    fairV-lift Δ₀≤Δ₁ sΔ₁ τ₀ fairτ₀

  fairV-lift :
    ∀ {Δ₀ Δ₁}
    → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
    → (sΔ₁ : safe Δ₁)
    → (τ₀ : Trace Δ₀)
    → Fair τ₀
    → S.FairV (unfoldᵗ (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀))
  fairV-lift Δ₀≤Δ₁ sΔ₁ τ₀ fairτ₀ with unfoldᵗ τ₀ | S.fair-next fairτ₀
  ... | S.tstop stuck₀ | S.fair-stop = S.fair-stop
  ... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀' | S.fair-step fairτ₀' =
    let sim = stepSim≤-pair Δ₀≤Δ₁ (sΔ₁ rtc-refl) red₀ in
    let red₁ = proj₁ (proj₂ sim) in
    let Δ₀'≤Δ₁' = proj₂ (proj₂ sim) in
    S.fair-step
      (fair-lift Δ₀'≤Δ₁'
                 (safe-tail sΔ₁ (S._↝⟨_⟩_ r Obs s , red₁))
                 τ₀'
                 fairτ₀')

eventuallySend-down :
  ∀ {Δ₀ Δ₁ p q}
  → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
  → (sΔ₁ : safe Δ₁)
  → (τ₀ : Trace Δ₀)
  → S.EventuallySend p q (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀)
  → S.EventuallySend p q τ₀
eventuallySend-down Δ₀≤Δ₁ sΔ₁ τ₀ ev with unfoldᵗ τ₀ | ev
... | S.tstop stuck₀ | S.ev₁-now-stop canSend₁ =
  S.ev₁-now-stop (canSend-down-any-≤ Δ₀≤Δ₁ canSend₁)
... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀' | S.ev₁-now-step canSend₁ =
  S.ev₁-now-step (canSend-down-any-≤ Δ₀≤Δ₁ canSend₁)
... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀' | S.ev₁-next ev' =
  let sim = stepSim≤-pair Δ₀≤Δ₁ (sΔ₁ rtc-refl) red₀ in
  let red₁ = proj₁ (proj₂ sim) in
  let Δ₀'≤Δ₁' = proj₂ (proj₂ sim) in
  S.ev₁-next
    (eventuallySend-down Δ₀'≤Δ₁'
                         (safe-tail sΔ₁ (S._↝⟨_⟩_ r Obs s , red₁))
                         τ₀'
                         ev')

eventuallyRecv-down :
  ∀ {Δ₀ Δ₁ p q}
  → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
  → (sΔ₁ : safe Δ₁)
  → (τ₀ : Trace Δ₀)
  → S.EventuallyRecv p q (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀)
  → S.EventuallyRecv p q τ₀
eventuallyRecv-down Δ₀≤Δ₁ sΔ₁ τ₀ ev with unfoldᵗ τ₀ | ev
... | S.tstop stuck₀ | S.ev₁-now-stop canRecv₁ =
  S.ev₁-now-stop (canRecv-down-≤ Δ₀≤Δ₁ canRecv₁)
... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀' | S.ev₁-now-step canRecv₁ =
  S.ev₁-now-step (canRecv-down-≤ Δ₀≤Δ₁ canRecv₁)
... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀' | S.ev₁-next ev' =
  let sim = stepSim≤-pair Δ₀≤Δ₁ (sΔ₁ rtc-refl) red₀ in
  let red₁ = proj₁ (proj₂ sim) in
  let Δ₀'≤Δ₁' = proj₂ (proj₂ sim) in
  S.ev₁-next
    (eventuallyRecv-down Δ₀'≤Δ₁'
                         (safe-tail sΔ₁ (S._↝⟨_⟩_ r Obs s , red₁))
                         τ₀'
                         ev')

mutual
  live-pull :
    ∀ {Δ₀ Δ₁}
    → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
    → (sΔ₁ : safe Δ₁)
    → (τ₀ : Trace Δ₀)
    → Live (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀)
    → Live τ₀
  S.live-here (live-pull Δ₀≤Δ₁ sΔ₁ τ₀ liveτ₁) =
    liveHere-pull Δ₀≤Δ₁ sΔ₁ τ₀ liveτ₁
  S.live-next (live-pull Δ₀≤Δ₁ sΔ₁ τ₀ liveτ₁) =
    liveV-pull Δ₀≤Δ₁ sΔ₁ τ₀ liveτ₁

  liveHere-pull :
    ∀ {Δ₀ Δ₁}
    → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
    → (sΔ₁ : safe Δ₁)
    → (τ₀ : Trace Δ₀)
    → Live (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀)
    → S.LiveHere τ₀
  S.send-live (liveHere-pull Δ₀≤Δ₁ sΔ₁ τ₀ liveτ₁) p q canSend₀ =
    eventuallySend-down Δ₀≤Δ₁ sΔ₁ τ₀
      (S.send-live (S.live-here liveτ₁) p q (canSend-up-≤ Δ₀≤Δ₁ canSend₀))
  S.recv-live (liveHere-pull Δ₀≤Δ₁ sΔ₁ τ₀ liveτ₁) p q canRecv₀ =
    eventuallyRecv-down Δ₀≤Δ₁ sΔ₁ τ₀
      (S.recv-live (S.live-here liveτ₁) p q (canRecv-up-any-≤ Δ₀≤Δ₁ canRecv₀))

  liveV-pull :
    ∀ {Δ₀ Δ₁}
    → (Δ₀≤Δ₁ : Δ₀ ≤Δ Δ₁)
    → (sΔ₁ : safe Δ₁)
    → (τ₀ : Trace Δ₀)
    → Live (liftTrace Δ₀≤Δ₁ sΔ₁ τ₀)
    → S.LiveV (unfoldᵗ τ₀)
  liveV-pull Δ₀≤Δ₁ sΔ₁ τ₀ liveτ₁ with unfoldᵗ τ₀ | S.live-next liveτ₁
  ... | S.tstop stuck₀ | S.live-stop = S.live-stop
  ... | S.tstep (S._↝⟨_⟩_ r Obs s , red₀) τ₀' | S.live-step liveτ₁' =
    let sim = stepSim≤-pair Δ₀≤Δ₁ (sΔ₁ rtc-refl) red₀ in
    let red₁ = proj₁ (proj₂ sim) in
    let Δ₀'≤Δ₁' = proj₂ (proj₂ sim) in
    S.live-step
      (live-pull Δ₀'≤Δ₁'
                 (safe-tail sΔ₁ (S._↝⟨_⟩_ r Obs s , red₁))
                 τ₀'
                 liveτ₁')

FairTraceLift≤ :
  ∀ {Δ₀ Δ₁}
  → Δ₀ ≤Δ Δ₁
  → safe Δ₁
  → (τ₀ : Trace Δ₀)
  → Fair τ₀
  → Σ (Trace Δ₁) (λ τ₁ → Fair τ₁ × (Live τ₁ → Live τ₀))
FairTraceLift≤ Δ₀≤Δ₁ sΔ₁ τ₀ fairτ₀ =
  liftTrace Δ₀≤Δ₁ sΔ₁ τ₀
  , ( fair-lift Δ₀≤Δ₁ sΔ₁ τ₀ fairτ₀
    , live-pull Δ₀≤Δ₁ sΔ₁ τ₀
    )

live-downward-≤ :
  ∀ {Δ₀ Δ₁}
  → Δ₀ ≤Δ Δ₁
  → safe Δ₁
  → liveContext Δ₁
  → liveContext Δ₀
live-downward-≤ Δ₀≤Δ₁ sΔ₁ liveΔ₁ τ₀ fairτ₀
  with FairTraceLift≤ Δ₀≤Δ₁ sΔ₁ τ₀ fairτ₀
... | τ₁ , fairτ₁ , pullLive =
  pullLive (liveΔ₁ τ₁ fairτ₁)
