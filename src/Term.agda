{-# OPTIONS --safe --without-K #-}

module Term where

open import Type
open import Context Ty

open import Semantics.Presheaf.Base 𝒲 public
open import Semantics.Presheaf.CartesianClosure 𝒲 public

open import Data.Product using (Σ; _×_; _,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

Var' : Ty → Psh
Var' τ = record
          { Fam           = λ Γ → Var Γ τ
          ; _≋_           = _≡_
          ; ≋-equiv       = λ _ → ≡-equiv
          ; wk            = wkVar
          ; wk-pres-≋     = λ w x≋y → cong (wkVar w) x≋y
          ; wk-pres-refl  = wkVar-pres-refl
          ; wk-pres-trans = wkVar-pres-trans
          }
  where
  wkVar-pres-refl : (x : Var Γ τ) → wkVar ⊆-refl x ≡ x
  wkVar-pres-refl x = refl

  wkVar-pres-trans : (r : Γ ⊆ Γ') (r' : Γ' ⊆ Γ'') (x : Var Γ τ)
    → wkVar (⊆-trans r r') x ≡ wkVar r' (wkVar r x)
  wkVar-pres-trans r r' x = refl

-- TODO: completing proof of `wk-pres-refl` below requires
-- that `⊆-keep ⊆-refl ≡ ⊆-refl`, which doesn't appear
-- provable without extensionality. does this mean
-- we should already switch to OPEs (where this holds)?
-- Similarly, to prove `wk-pres-trans`, we need
-- `⊆-keep (⊆-trans r r') ≡ ⊆-trans (⊆-keep r) (⊆-keep r')`
ε[_]_ : Ty → Psh → Psh
ε[ τ ] 𝒫 = record
       { Fam           = λ Γ → 𝒫 ₀ (Γ `, τ)
       ; _≋_           = λ x y → x ≋[ 𝒫 ] y
       ; ≋-equiv       = λ Γ → Psh.≋-equiv 𝒫 (Γ `, τ)
       ; wk            = λ r → wk[ 𝒫 ] (⊆-keep r)
       ; wk-pres-≋     = λ r → wk[ 𝒫 ]-pres-≋ (⊆-keep r)
       ; wk-pres-refl  = λ x → {!!}
       ; wk-pres-trans = λ w w' x → {!!}
       }

-- TODO: after ε[_]_
ε[_]-map : {𝒫 𝒬 : Psh} (τ : Ty) → (𝒫 →̇ 𝒬) → ε[ τ ] 𝒫 →̇ ε[ τ ] 𝒬
ε[_]-map = {!!}

record TmAlg (𝒯 : Ty → Psh) : Set₁ where
  field
    var : Var' τ →̇ 𝒯 τ
    lam : ε[ σ ] (𝒯 τ) →̇ 𝒯 (σ ⇒ τ)
    app : 𝒯 (σ ⇒ τ) ×' 𝒯 σ →̇ 𝒯 τ

  Tm : Ctx → Ty → Set
  Tm Γ τ = 𝒯 τ ₀ Γ

  -- write Sub Γ Δ for Γ ⊢ₛ Δ
  Sub : Ctx → Ctx → Set
  Sub Γ Δ = {τ : Ty} → Var Δ τ → 𝒯 τ ₀ Γ

  _⊢ₛ_ = Sub

  wkSub : Γ ⊆ Γ' → Sub Γ Δ → Sub Γ' Δ
  wkSub r δ {τ} = λ x → wk[ 𝒯 τ ] r (δ x)

  wkSub-pres-refl : (δ : Sub Γ Δ) {τ : Ty} (x : Var Δ τ) → wkSub ⊆-refl δ x ≋[ 𝒯 τ ] δ x
  wkSub-pres-refl δ {τ} x = wk[ 𝒯 τ ]-pres-refl _

  wkSub-pres-trans : (r : Γ ⊆ Γ') (r' : Γ' ⊆ Γ'') (δ : Sub Γ Δ) {τ : Ty} (x : Var Δ τ)               
                   → wkSub (⊆-trans r r') δ x ≋[ 𝒯 τ ] wkSub r' (wkSub r δ) x
  wkSub-pres-trans r r' δ {τ} x = wk[ 𝒯 τ ]-pres-trans r r' (δ x)
  
  Sub' : Ctx → Psh
  Sub' Δ = record
            { Fam           = λ Γ → Sub Γ Δ
            ; _≋_           = λ {Γ : Ctx} (δ δ' : Sub Γ Δ) → {τ : Ty} (x : Var Δ τ) → δ x ≋[ 𝒯 τ ] δ' x
            ; ≋-equiv       = λ Γ → record
              { refl   = λ _ → ≋[ 𝒯 _ ]-refl
              ; sym    = λ δ≋δ' x → ≋[ 𝒯 _ ]-sym (δ≋δ' x)
              ; trans  = λ δ≋δ' δ'≋δ'' x → ≋[ 𝒯 _ ]-trans (δ≋δ' x) (δ'≋δ'' x)
              }
            ; wk            = wkSub
            ; wk-pres-≋     = λ r δ≋δ' {τ} x → wk[ 𝒯 τ ]-pres-≋ r (δ≋δ' x)
            ; wk-pres-refl  = wkSub-pres-refl
            ; wk-pres-trans = wkSub-pres-trans
            }

  trimSub-fun : Δ ⊆ Δ' → Sub Γ Δ' → Sub Γ Δ
  trimSub-fun r δ {τ} = λ x → δ (wkVar r x)

  -- TODO: is trimSub a contravariant functor on 𝒲?
  -- TODO: rename (?) and complete
  trimSub : Δ ⊆ Δ' → Sub' Δ' →̇ Sub' Δ
  trimSub r = record
    { fun     = trimSub-fun r
    ; pres-≋  = λ p≋p' x → p≋p' (r _ x)
    ; natural = λ w p x → ≋[ 𝒯 _ ]-refl
    }

  -- TODO:
  ◼_ : Psh → Psh
  ◼ 𝒫 = record
         { Fam           = λ Δ → Sub' Δ →̇ 𝒫
         ; _≋_           = _≈̇_
         ; ≋-equiv       = λ Γ → ≈̇-equiv
         ; wk            = λ r f → f ∘ trimSub r
         ; wk-pres-≋     = λ r f≋g → ∘-pres-≈̇-left f≋g (trimSub r)
         ; wk-pres-refl  = id'-unit-right _
         ; wk-pres-trans = λ w w' x → {!!}
         }

  -- TODO: define after fixing ◼'s definition 
  substVar : Var' τ →̇ ◼ (𝒯 τ)
  substVar = {!!}
 
  field
    μ       : 𝒯 τ →̇ ◼ (𝒯 τ)

  ⊢ₛ-refl : Sub Γ Γ 
  ⊢ₛ-refl = var .apply

  ⊢ₛ-trans : Sub Γ Δ →  Sub Δ Δ' → Sub Γ Δ'
  ⊢ₛ-trans δ δ' {τ} = λ x → μ .apply (δ' x) .apply δ

  -- TODO: all laws should be stated using ≈̇ after definig counit and cojoin of ■
  field
    -- think "substTm"
    μ-lunit : μ {τ} ∘ var ≈̇ substVar
    
    -- think "substTm-pres-refl"
    μ-runit : {x : Var Γ τ} {t : 𝒯 τ ₀ Γ} → μ .apply t .apply ⊢ₛ-refl ≋[ 𝒯 τ ] t

    -- think "substTm-pres-trans"
    μ-assoc : {x : Var Γ τ} {t : 𝒯 τ ₀ Δ'} {δ : Sub Γ Δ} {δ' : Sub Δ Δ'}
      → μ .apply (μ .apply t .apply δ') .apply δ ≋[ 𝒯 τ ] μ .apply t .apply (⊢ₛ-trans δ δ')

  extₛ-fun : Sub Γ Δ → 𝒯 τ ₀ Γ → Sub Γ (Δ `, τ)
  extₛ-fun s t v0       = t
  extₛ-fun s t (succ x) = s x

  _`,ₛ_ = extₛ-fun

  -- TODO:
  extₛ : (Sub' Δ ×' 𝒯 τ) →̇ Sub' (Δ `, τ)
  extₛ = record
    { fun     = λ { (elem (s , t)) → extₛ-fun s t }
    ; pres-≋  = {!!}
    ; natural = {!!}
    }

  -- TODO:
  subst1 : (ε[ σ ] 𝒯 τ) ×' 𝒯 σ →̇ 𝒯 τ
  subst1 = {!!}
  
  -- TODO: using subst1, define β and η laws
