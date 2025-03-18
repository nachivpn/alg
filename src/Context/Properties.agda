{-# OPTIONS --safe --without-K #-}
module Context.Properties (Ty : Set) where

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)
  
open import Context.Base Ty

open import Frame.IFrame

private
  variable
    a b c d : Ty

--
-- ⊆-drop properties
--

⊆-drop-nat : (w : Γ ⊆ Γ') (x : Var Γ a)  → wkVar (⊆-drop {a = b} w) x ≡ succ (wkVar w x)
⊆-drop-nat (w `, x) v0       = refl
⊆-drop-nat (w `, _) (succ x) = ⊆-drop-nat w x

-- TODO: rename!
lemma1 : (r : Γ ⊆ Γ') (r' : Γ' ⊆ Γ'') (x : Var Γ'' a)
  → ⊆-trans (⊆-drop r) (r' `, x) ≡ ⊆-trans r r'
lemma1 [] r' x = refl
lemma1 (r `, x₁) r' x = cong (_`, _) (lemma1 r r' x)

--TODO: rename!
lemma2 : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'')
  → ⊆-drop {a = a} (⊆-trans w w') ≡ ⊆-trans w (⊆-drop w')
lemma2 [] w' = refl
lemma2 (w `, x) w' = cong₂ _`,_ (lemma2 w w') (≡-sym (⊆-drop-nat w' x))

--TODO: rename!
lemma3 : (w : Γ ⊆ Γ') (w' : Γ' ⊆ Γ'')
  → ⊆-drop {a = a} (⊆-trans w w') ≡ ⊆-trans (⊆-drop w) (⊆-keep w')
lemma3 w w' = ≡-trans (lemma2 w w') (≡-sym (lemma1 w (⊆-drop w') zero))

--
-- Var is a presheaf (indexed by below defined category 𝒲)
--

mutual

  wkIncr : (x : Var Γ a) → wkVar ⊆-fresh[ Γ , b ] x ≡ succ x
  wkIncr x = ≡-trans (⊆-drop-nat ⊆-refl x) (cong succ (wkVar-pres-refl x))

  wkVar-pres-refl : (x : Var Γ a) → wkVar ⊆-refl x ≡ x
  wkVar-pres-refl v0       = refl
  wkVar-pres-refl (succ x) = wkIncr x

wkVar-pres-trans : (r : Γ ⊆ Γ') (r' : Γ' ⊆ Δ) (x : Var Γ a)
  → wkVar (⊆-trans r r') x ≡ wkVar r' (wkVar r x)
wkVar-pres-trans (r `, x₁) r' v0       = refl
wkVar-pres-trans (r `, x₁) r' (succ x) = wkVar-pres-trans r r' x

--
-- Ctx and _⊆_ form an IFrame (category) 𝒲
--

⊆-trans-unit-left : (r : Γ' ⊆ Γ) → ⊆-trans ⊆-refl r ≡ r
⊆-trans-unit-left []       = refl
⊆-trans-unit-left (r `, x) = cong (_`, _) (≡-trans (lemma1 ⊆-refl r x) (⊆-trans-unit-left r))

⊆-trans-unit-right : (r : Γ' ⊆ Γ) → ⊆-trans r ⊆-refl ≡ r
⊆-trans-unit-right []       = refl
⊆-trans-unit-right (r `, x) = cong₂ _`,_ (⊆-trans-unit-right r) (wkVar-pres-refl x)

⊆-trans-assoc : {Γ1 Γ2 Γ3 Γ4 : Ctx} → (w3 : Γ4 ⊆ Γ3) (w2 : Γ3 ⊆ Γ2) → (w1 : Γ2 ⊆ Γ1)
  → ⊆-trans (⊆-trans w3 w2) w1 ≡ ⊆-trans w3 (⊆-trans w2 w1)
⊆-trans-assoc []        w2 w1 = refl
⊆-trans-assoc (w3 `, x) w2 w1 = cong₂ _`,_ (⊆-trans-assoc w3 w2 w1) (≡-sym (wkVar-pres-trans w2 w1 x))

𝒲 : IFrame Ctx _⊆_
𝒲 = record
      { ⊆-trans            = ⊆-trans
      ; ⊆-trans-assoc      = ⊆-trans-assoc
      ; ⊆-refl             = ⊆-refl
      ; ⊆-trans-unit-right = ⊆-trans-unit-right
      ; ⊆-trans-unit-left  = ⊆-trans-unit-left
      }

--
-- ⊆-keep is an endofunctor on 𝒲
--

⊆-keep-pres-refl : ⊆-keep ⊆-refl ≡ ⊆-refl[ Γ `, a ]
⊆-keep-pres-refl = refl

⊆-keep-pres-trans : (r : Γ ⊆ Γ') (r' : Γ' ⊆ Γ'') → ⊆-keep {a = a} (⊆-trans r r') ≡ ⊆-trans (⊆-keep r) (⊆-keep r')
⊆-keep-pres-trans []       r' = refl
⊆-keep-pres-trans (r `, x) r' = cong (_`, zero) (cong₂ _`,_ (lemma3 r r') (≡-sym (⊆-drop-nat r' x )))




