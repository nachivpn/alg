{-# OPTIONS --safe --without-K #-}
module Context.Base (Ty : Set) where

private
  variable
    a b c d : Ty

infix  5 _⊆_
infixl 5 _,,_

-----------
-- Contexts
-----------

data Ctx : Set where
  []   : Ctx
  _`,_ : (Γ : Ctx) → (a : Ty) → Ctx

[_] : Ty → Ctx
[_] a = [] `, a

variable
  Γ Γ' Γ'' ΓL ΓL' ΓL'' ΓLL ΓLR ΓR ΓR' ΓR'' : Ctx
  Δ Δ' Δ'' ΔL ΔL' ΔL'' ΔLL ΔLR ΔR ΔR' ΔR'' ΔRL ΔRR : Ctx
  Θ Θ' Θ'' ΘL ΘL' ΘL'' ΘLL ΘLR ΘR ΘR' ΘR'' ΘRL ΘRR : Ctx
  Ξ Ξ' Ξ'' ΞL ΞL' ΞL'' ΞLL ΞLR ΞR ΞR' ΞR'' ΞRL ΞRR : Ctx

-- append contexts (++)
_,,_ : Ctx → Ctx → Ctx
Γ ,, []       = Γ
Γ ,, (Δ `, x) = (Γ ,, Δ) `, x


------------
-- Variables
------------

data Var : Ctx → Ty → Set where
  zero : Var (Γ `, a) a
  succ : (v : Var Γ a) → Var (Γ `, b) a

pattern v0 = zero
pattern v1 = succ v0
pattern v2 = succ v1

-------------
-- Renamings
-------------

data _⊆_  : Ctx → Ctx → Set where
  []   : [] ⊆ Γ
  _`,_ : Γ ⊆ Γ' → Var Γ' a → (Γ `, a) ⊆ Γ'

variable
  w w' w'' : Γ ⊆ Γ'

wkVar : Γ ⊆ Γ' → Var Γ a → Var Γ' a
wkVar (r `, x) v0       = x
wkVar (r `, x) (succ v) = wkVar r v

⊆-trans : Θ ⊆ Δ → Δ ⊆ Γ → Θ ⊆ Γ
⊆-trans []        r1 = []
⊆-trans (r2 `, x) r1 = (⊆-trans r2 r1) `, (wkVar r1 x)

⊆-drop : Γ ⊆ Γ' → Γ ⊆ Γ' `, a
⊆-drop []       = []
⊆-drop (r `, x) = ⊆-drop r `, succ x

⊆-keep : Γ ⊆ Γ' → Γ `, a ⊆ Γ' `, a
⊆-keep r = ⊆-drop r `, v0

⊆-refl[_] : (Γ : Ctx) → Γ ⊆ Γ
⊆-refl[ [] ]     = []
⊆-refl[ Γ `, a ] = ⊆-drop ⊆-refl[ Γ ] `, v0

⊆-refl : Γ ⊆ Γ
⊆-refl {Γ} = ⊆-refl[ Γ ]

⊆-fresh[_,_] : (Γ : Ctx) → (a : Ty) → Γ ⊆ (Γ `, a)
⊆-fresh[ Γ , a ] = ⊆-drop ⊆-refl[ Γ ]

⊆-fresh : Γ ⊆ (Γ `, a)
⊆-fresh = ⊆-fresh[ _ , _ ]
