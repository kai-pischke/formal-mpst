{-# OPTIONS --safe #-}
module TermLoop where
f : Set → Set
f x = g x

g : Set → Set
g x = f x
