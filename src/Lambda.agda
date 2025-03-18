{-# OPTIONS --safe --without-K #-}

module Lambda where

open import Type public
open import Context Ty public

open import Presheaf.Base 𝒲 public
open import Presheaf.CartesianClosure 𝒲 public

open import Data.Product using (Σ; _×_; _,_ ; proj₁ ; proj₂)

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

-- Variable presheaf
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

-- Extension functor
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

record LambdaAlgebra (𝒯 : Ty → Psh) : Set₁ where
  field
    var : Var' τ →̇ 𝒯 τ
    lam : ε[ σ ] (𝒯 τ) →̇ 𝒯 (σ ⇒ τ)
    app : 𝒯 (σ ⇒ τ) ×' 𝒯 σ →̇ 𝒯 τ

  Tm : Ctx → Ty → Set
  Tm Γ τ = 𝒯 τ ₀ Γ

  _≈_ : {τ : Ty} → (t t' : Tm Γ τ) → Set
  t ≈ t' = t ≋[ 𝒯 _ ] t'

  ≈-refl : {t : Tm Γ τ} → t ≈ t
  ≈-refl = ≋[ 𝒯 _ ]-refl

  ≈-sym : {t t' : Tm Γ τ} → t ≈ t' → t' ≈ t
  ≈-sym = ≋[ 𝒯 _ ]-sym

  ≈-trans : {t t' t'' : Tm Γ τ} → t ≈ t' → t' ≈ t'' → t ≈ t''
  ≈-trans = ≋[ 𝒯 _ ]-trans
  
