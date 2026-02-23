{-# OPTIONS --safe #-}

module Core.TransitionClosure where

------------------------------------------------------------------------
-- Reflexive-transitive closure of a binary relation
------------------------------------------------------------------------

data RTC {A : Set} (R : A → A → Set) : A → A → Set where
  rtc-refl : ∀ {x} → RTC R x x
  rtc-step : ∀ {x y z} → R x y → RTC R y z → RTC R x z

rtc-single : ∀ {A : Set} {R : A → A → Set} {x y} → R x y → RTC R x y
rtc-single r = rtc-step r rtc-refl
