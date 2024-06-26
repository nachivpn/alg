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

ε[_]_ : Ty → Psh → Psh
ε[ τ ] 𝒫 = record
       { Fam           = λ Γ → 𝒫 ₀ (Γ `, τ)
       ; _≋_           = λ x y → x ≋[ 𝒫 ] y
       ; ≋-equiv       = λ Γ → Psh.≋-equiv 𝒫 (Γ `, τ)
       ; wk            = λ r → wk[ 𝒫 ] (⊆-keep r)
       ; wk-pres-≋     = λ r → wk[ 𝒫 ]-pres-≋ (⊆-keep r)
       ; wk-pres-refl  = λ x → wk[ 𝒫 ]-pres-refl x
       ; wk-pres-trans = λ w w' x → ≋[ 𝒫 ]-trans
         (≋[ 𝒫 ]-reflexive (cong (λ r → wk[ 𝒫 ] r x) (⊆-keep-pres-trans w w')))
         (wk[ 𝒫 ]-pres-trans (⊆-keep w) (⊆-keep w') x)
       }

ε[_]-map : {𝒫 𝒬 : Psh} (τ : Ty) → (𝒫 →̇ 𝒬) → ε[ τ ] 𝒫 →̇ ε[ τ ] 𝒬
ε[_]-map τ f = record
  { fun     = f .apply
  ; pres-≋  = f .apply-≋
  ; natural = λ w p → f .natural (⊆-keep w) p
  }

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
  wkSub-pres-refl δ {τ} x = wk[ 𝒯 τ ]-pres-refl (δ x)

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
  -- TODO: rename (?)
  trimSub : Δ ⊆ Δ' → Sub' Δ' →̇ Sub' Δ
  trimSub r = record
    { fun     = trimSub-fun r
    ; pres-≋  = λ p≋p' x → p≋p' (wkVar r x)
    ; natural = λ _w _p _x → ≋[ 𝒯 _ ]-refl
    }

  trimSub-pres-refl : trimSub ⊆-refl ≈̇ id'[ Sub' Δ ]
  trimSub-pres-refl = record { proof = λ δ x → ≋[ 𝒯 _ ]-reflexive (cong δ (wkVar-pres-refl x)) }

  trimSub-pres-trans : (r : Δ ⊆ Δ') (r' : Δ' ⊆ Δ'') → trimSub (⊆-trans r r') ≈̇ trimSub r ∘ trimSub r'
  trimSub-pres-trans r r' = record { proof = λ δ x → ≋[ 𝒯 _ ]-reflexive (cong δ (wkVar-pres-trans r r' x)) }

  ◼_ : Psh → Psh
  ◼ 𝒫 = record
         { Fam           = λ Δ → Sub' Δ →̇ 𝒫
         ; _≋_           = _≈̇_
         ; ≋-equiv       = λ Γ → ≈̇-equiv
         ; wk            = λ r f → f ∘ trimSub r
         ; wk-pres-≋     = λ r f≋g → ∘-pres-≈̇-left f≋g (trimSub r)
         ; wk-pres-refl  = λ f → ≈̇-trans
           (∘-pres-≈̇-right f trimSub-pres-refl)
           (id'-unit-right (Sub' _) f)
         ; wk-pres-trans = λ r r' f → ≈̇-trans
           (∘-pres-≈̇-right f (trimSub-pres-trans r r'))
           (≈̇-sym (∘-assoc f (trimSub r) (trimSub r')))
         }

  lookup-fun : Var Δ τ → Sub Γ Δ → 𝒯 τ ₀ Γ
  lookup-fun x f = f x

  lookup : Var Δ τ → Sub' Δ →̇ 𝒯 τ
  lookup x = record
    { fun     = lookup-fun x
    ; pres-≋  = λ δ≋δ' → δ≋δ' x
    ; natural = λ w δ → ≋[ 𝒯 _ ]-refl
    }

  substVar-fun = lookup

  substVar : Var' τ →̇ ◼ (𝒯 τ)
  substVar = record
    { fun     = substVar-fun
    ; pres-≋  = λ p≡p' → record { proof = λ δ → ≋[ 𝒯 _ ]-reflexive (cong δ p≡p') }
    ; natural = λ w x → record { proof = λ _δ → ≋[ 𝒯 _ ]-refl }
    }
 
  field
    μ       : 𝒯 τ →̇ ◼ (𝒯 τ)

  ⊢ₛ-refl : Sub Γ Γ 
  ⊢ₛ-refl = var .apply

  ⊢ₛ-trans : Sub Γ Δ →  Sub Δ Δ' → Sub Γ Δ'
  ⊢ₛ-trans δ δ' {τ} = λ x → μ .apply (δ' x) .apply δ

  ◼-map : {𝒫 𝒬 : Psh} → (𝒫 →̇ 𝒬) → (◼ 𝒫 →̇ ◼ 𝒬)
  ◼-map {𝒫} {𝒬} f = record
    { fun     = f ∘_
    ; pres-≋  = ∘-pres-≈̇-right f
    ; natural = λ r p → record { proof = λ δ → ≋[ 𝒬 ]-refl }
    }

  ◼-ϵ : {𝒫 : Psh} → ◼ 𝒫 →̇ 𝒫
  ◼-ϵ {𝒫} = record
    { fun     = λ bp → bp .apply ⊢ₛ-refl
    ; pres-≋  = λ bp≋bp' → bp≋bp' .apply-≋ ⊢ₛ-refl
    ; natural = λ r bp → ≋[ 𝒫 ]-trans (bp .natural r ⊢ₛ-refl) (bp .apply-≋ (var .natural r))
    }

  -- pricey!
  ◼-δ : {𝒫 : Psh} → ◼ 𝒫 →̇ ◼ ◼ 𝒫
  ◼-δ {𝒫} = record
    { fun     = λ bp → record
      { fun     = λ δ → record
        { fun     = λ δ' → bp .apply (⊢ₛ-trans δ' δ)
        ; pres-≋  = λ δ≋δ' → bp .apply-≋ (λ x → μ .apply (δ x) .apply-≋ δ≋δ')
        ; natural = λ r δ' → ≋[ 𝒫 ]-trans
          (bp .natural r (⊢ₛ-trans δ' δ))
          (bp .apply-≋ λ x → μ .apply (δ x) .natural r δ') }
      ; pres-≋  = λ δ≋δ' → record { proof = λ δ → bp .apply-≋ (λ x → μ .apply-≋ (δ≋δ' x) .apply-≋ δ) }
      ; natural = λ r δ → record { proof = λ δ' → bp .apply-≋ (λ x → μ .natural r (δ x) .apply-≋ δ') } }
    ; pres-≋  = λ bp≋bp' → record { proof = λ δ → record { proof = λ δ' → bp≋bp' .apply-≋ (⊢ₛ-trans δ' δ) } }
    ; natural = λ r bp → record { proof = λ δ → record { proof = λ δ' → ≋[ 𝒫 ]-refl } }
    }

  field
    -- think "substTm"
    μ-lunit : μ ∘ var ≈̇ substVar {τ}
    
    -- think "substTm-pres-refl"
    μ-runit : ◼-ϵ ∘ μ ≈̇ id' {𝒯 τ}

    -- think "substTm-pres-trans"
    μ-assoc : {x : Var Γ τ} {t : 𝒯 τ ₀ Δ'} {δ : Sub Γ Δ} {δ' : Sub Δ Δ'}
      → μ .apply (μ .apply t .apply δ') .apply δ ≋[ 𝒯 τ ] μ .apply t .apply (⊢ₛ-trans δ δ')

    -- this version is pricey!
    --μ-assoc : ◼-map μ ∘ μ ≈̇ ◼-δ ∘ μ {τ}

  -- TODO:
  subst1 : (ε[ σ ] 𝒯 τ) ×' 𝒯 σ →̇ 𝒯 τ
  subst1 = {!!}
  
  -- TODO: using subst1, define β and η laws

