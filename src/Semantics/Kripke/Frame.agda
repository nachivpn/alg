{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (∃; _×_; _,_; -,_) renaming (proj₁ to fst; proj₂ to snd)

module Semantics.Kripke.Frame where

-- Intuitionistic Frame
record IFrame (W : Set) (_⊆_ : W → W → Set) : Set where
  field
    ⊆-trans            : ∀ {w w' w'' : W} → (i : w ⊆ w') → (i' : w' ⊆ w'') → w ⊆ w''
    ⊆-trans-assoc      : ∀ {w w' w'' w''' : W} (i : w ⊆ w') (i' : w' ⊆ w'') (i'' : w'' ⊆ w''') → ⊆-trans (⊆-trans i i') i'' ≡ ⊆-trans i (⊆-trans i' i'')
    ⊆-refl             : ∀ {w : W} → w ⊆ w
    ⊆-refl-unit-right  : ∀ {w w' : W} (i : w ⊆ w') → ⊆-trans ⊆-refl i ≡ i
    ⊆-refl-unit-left   : ∀ {w w' : W} (i : w ⊆ w') → ⊆-trans i ⊆-refl ≡ i

