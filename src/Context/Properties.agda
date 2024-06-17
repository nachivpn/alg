{-# OPTIONS --safe --without-K #-}
module Context.Properties (Ty : Set) where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
  
open import Context.Base Ty

open import Semantics.Kripke.Frame

private
  variable
    a b c d : Ty
  
⊆-refl-unit-left : (w : Γ' ⊆ Γ) → ⊆-trans ⊆-refl w ≡ w
⊆-refl-unit-left w = refl

⊆-refl-unit-right : (w : Γ' ⊆ Γ) → ⊆-trans w ⊆-refl  ≡ w
⊆-refl-unit-right w = refl

⊆-trans-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ4 ⊆ Γ3) (w2 : Γ3 ⊆ Γ2) → (w1 : Γ2 ⊆ Γ1)
  → ⊆-trans (⊆-trans w3 w2) w1 ≡ ⊆-trans w3 (⊆-trans w2 w1)
⊆-trans-assoc w3 w2 w1 = refl

𝒲 : IFrame Ctx _⊆_
𝒲 = record
      { ⊆-trans           = ⊆-trans
      ; ⊆-trans-assoc     = ⊆-trans-assoc
      ; ⊆-refl            = ⊆-refl
      ; ⊆-refl-unit-right = ⊆-refl-unit-left
      ; ⊆-refl-unit-left  = ⊆-refl-unit-right
      }

wkVar-pres-⊆-refl : (x : Var Γ a) → wkVar ⊆-refl x ≡ x
wkVar-pres-⊆-refl v0       = refl
wkVar-pres-⊆-refl (succ x) = cong succ (wkVar-pres-⊆-refl x)

wkVar-pres-⊆-trans : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Δ) (x : Var Γ a)
  → wkVar (⊆-trans w w') x ≡ wkVar w' (wkVar w x)
wkVar-pres-⊆-trans w w' x = refl

-- weakening a variable increments its index
wkIncr : (x : Var Γ a) → wkVar ⊆-fresh[ Γ , b ] x ≡ succ x
wkIncr zero     = refl
wkIncr (succ x) = cong succ (cong succ (wkVar-pres-⊆-refl x))



