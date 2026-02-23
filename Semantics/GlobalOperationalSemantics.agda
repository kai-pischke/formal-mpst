{-# OPTIONS --safe #-}

module Semantics.GlobalOperationalSemantics (ℓ n : _) where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Syntax.GlobalSessionTypes as GTS
import Core.OperationalLabels as OL
import Core.TransitionClosure as TC

module G = GTS ℓ n
module O = OL ℓ n

open G public using
  ( Global
  ; Global₀
  ; end
  ; msg
  ; choice
  ; mu
  ; Branches
  ; lookupB
  ; unfold
  )

open O public using
  ( Label
  ; Participant
  ; Base
  ; Observable
  ; obsBase
  ; obsLabel
  ; Interaction
  ; _↝⟨_⟩_
  ; DisjointEndpoints
  )
open TC public using (RTC; rtc-refl; rtc-step; rtc-single)

------------------------------------------------------------------------
-- Global-type operational semantics
------------------------------------------------------------------------

infix 3 _-[_]→ᵍ_ _-[_]→ᵐ_ _-[_]→ᵇ_

mutual
  data _-[_]→ᵍ_ : Global₀ → Interaction → Global₀ → Set where
    GR1 :
      ∀ {p q b G}
      → msg p q b G -[ p ↝⟨ obsBase b ⟩ q ]→ᵍ G

    GR2 :
      ∀ {p q b G G' r s U}
      → G -[ r ↝⟨ U ⟩ s ]→ᵍ G'
      → DisjointEndpoints r s p q
      → msg p q b G -[ r ↝⟨ U ⟩ s ]→ᵍ msg p q b G'

    GR3 :
      ∀ {body ι G'}
      → unfold (mu body) -[ ι ]→ᵍ G'
      → mu body -[ ι ]→ᵍ G'

    GR4 :
      ∀ {p q bs l G}
      → lookupB l bs ≡ just G
      → choice p q bs -[ p ↝⟨ obsLabel l ⟩ q ]→ᵍ G

    GR5 :
      ∀ {p q bs bs' r s U}
      → bs -[ r ↝⟨ U ⟩ s ]→ᵇ bs'
      → DisjointEndpoints r s p q
      → choice p q bs -[ r ↝⟨ U ⟩ s ]→ᵍ choice p q bs'

  data _-[_]→ᵐ_ : Maybe Global₀ → Interaction → Maybe Global₀ → Set where
    GM-none :
      ∀ {ι}
      → nothing -[ ι ]→ᵐ nothing

    GM-step :
      ∀ {G G' ι}
      → G -[ ι ]→ᵍ G'
      → just G -[ ι ]→ᵐ just G'

  data _-[_]→ᵇ_ : ∀ {m} → Vec (Maybe Global₀) m → Interaction → Vec (Maybe Global₀) m → Set where
    GB-[] :
      ∀ {ι}
      → [] -[ ι ]→ᵇ []

    GB-∷ :
      ∀ {k}
      {x y : Maybe Global₀}
      {xs ys : Vec (Maybe Global₀) k}
      {ι}
      → x -[ ι ]→ᵐ y
      → xs -[ ι ]→ᵇ ys
      → (x ∷ xs) -[ ι ]→ᵇ (y ∷ ys)

------------------------------------------------------------------------
-- Helper relations (existentially quantified interactions/observables)
------------------------------------------------------------------------

infix 3 _→ᵍ_ _→ᵐ_ _→ᵇ_ _-[_,_]→ᵍ_

_→ᵍ_ : Global₀ → Global₀ → Set
G →ᵍ G' = Σ Interaction (λ ι → G -[ ι ]→ᵍ G')

_→ᵐ_ : Maybe Global₀ → Maybe Global₀ → Set
mG →ᵐ mG' = Σ Interaction (λ ι → mG -[ ι ]→ᵐ mG')

_→ᵇ_ : ∀ {m} → Vec (Maybe Global₀) m → Vec (Maybe Global₀) m → Set
bs →ᵇ bs' = Σ Interaction (λ ι → bs -[ ι ]→ᵇ bs')

_-[_,_]→ᵍ_ : Global₀ → Participant → Participant → Global₀ → Set
G -[ p , q ]→ᵍ G' = Σ Observable (λ U → G -[ p ↝⟨ U ⟩ q ]→ᵍ G')

-- Reflexive-transitive closures of unlabeled global transitions.
infix 3 _→ᵍ*_ _→ᵐ*_ _→ᵇ*_

_→ᵍ*_ : Global₀ → Global₀ → Set
G →ᵍ* G' = RTC _→ᵍ_ G G'

_→ᵐ*_ : Maybe Global₀ → Maybe Global₀ → Set
mG →ᵐ* mG' = RTC _→ᵐ_ mG mG'

_→ᵇ*_ : ∀ {m} → Vec (Maybe Global₀) m → Vec (Maybe Global₀) m → Set
bs →ᵇ* bs' = RTC _→ᵇ_ bs bs'
