{-# OPTIONS --safe --without-K #-}

open import Lambda

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; refl ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

module Substitution
  (𝒯 : Ty → Psh)
  (𝒯-alg : LambdaAlgebra 𝒯)
  where

open LambdaAlgebra 𝒯-alg

data _⊢ₛ_  : Ctx → Ctx → Set where
  []   : Γ ⊢ₛ []
  _`,_ : Γ ⊢ₛ Δ → Tm Γ τ → Γ ⊢ₛ (Δ `, τ)

⊆-to-ₛ⊣ : Γ ⊆ Γ' → Γ' ⊢ₛ Γ
⊆-to-ₛ⊣ []       = []
⊆-to-ₛ⊣ (r `, x) = (⊆-to-ₛ⊣ r) `, (var .apply x)

Sub : Ctx → Ctx → Set
Sub Γ Δ = Γ ⊢ₛ Δ

data _≈ₛ_ : Sub Γ Δ → Sub Γ Δ → Set where
  []   : [] ≈ₛ [] {Γ}
  _`,_ : {δ δ' : Sub Γ Δ} {t t' : Tm Γ τ} → δ ≈ₛ δ' → t ≈ t' → (δ `, t) ≈ₛ (δ' `, t') 

wkSub : Γ ⊆ Γ' → Sub Γ Δ → Sub Γ' Δ
wkSub r []       = []
wkSub r (s `, t) = (wkSub r s) `, wk[ 𝒯 _ ] r t

⊢ₛ-refl[_] : (Γ : Ctx) → Sub Γ Γ
⊢ₛ-refl[ []     ] = []
⊢ₛ-refl[ Γ `, a ] = wkSub ⊆-fresh ⊢ₛ-refl[ Γ ] `, var .apply zero

⊢ₛ-refl : {Γ : Ctx} → Sub Γ Γ
⊢ₛ-refl = ⊢ₛ-refl[ _ ]

≈ₛ-refl : Reflexive {A = Sub Γ Δ} _≈ₛ_
≈ₛ-refl {x = []}     = []
≈ₛ-refl {x = δ `, t} = ≈ₛ-refl `, ≈-refl

≈ₛ-sym : Symmetric {A = Sub Γ Δ} _≈ₛ_
≈ₛ-sym []             = []
≈ₛ-sym (φ≋φ' `, t≈t') = (≈ₛ-sym φ≋φ') `, ≈-sym t≈t'

≈ₛ-trans : Transitive {A = Sub Γ Δ} _≈ₛ_
≈ₛ-trans []            ψ≋ω             = ψ≋ω
≈ₛ-trans (φ≋ψ `, t≈t') (ψ≋ω `, t'≈t'') = (≈ₛ-trans φ≋ψ ψ≋ω) `, ≈-trans t≈t' t'≈t''

≈ₛ-equiv : IsEquivalence {A = Sub Γ Δ} _≈ₛ_
≈ₛ-equiv = record
  { refl  = ≈ₛ-refl
  ; sym   = ≈ₛ-sym
  ; trans = ≈ₛ-trans
  }
            
wkSub-pres-≈ₛ : (r : Γ ⊆ Γ') {δ δ' : Sub Γ Δ} → δ ≈ₛ δ' → wkSub r δ ≈ₛ wkSub r δ'
wkSub-pres-≈ₛ r []             = []
wkSub-pres-≈ₛ r (δ≈ₛδ' `, t≋t') = (wkSub-pres-≈ₛ r δ≈ₛδ') `, (wk[ 𝒯 _ ]-pres-≋ r t≋t')

wkSub-pres-refl : (δ : Sub Γ Δ) → wkSub ⊆-refl δ ≈ₛ δ
wkSub-pres-refl []       = []
wkSub-pres-refl (δ `, t) = (wkSub-pres-refl δ) `, wk[ 𝒯 _ ]-pres-refl t

wkSub-pres-trans : (r : Γ ⊆ Γ') (r' : Γ' ⊆ Γ'') (δ : Sub Γ Δ)
  → wkSub (⊆-trans r r') δ ≈ₛ wkSub r' (wkSub r δ)
wkSub-pres-trans r r' []       = []
wkSub-pres-trans r r' (δ `, t) = (wkSub-pres-trans r r' δ) `, wk[ 𝒯 _ ]-pres-trans r r' t

Sub' : Ctx → Psh
Sub' Δ = record
          { Fam           = λ Γ → Sub Γ Δ
          ; _≋_           = _≈ₛ_
          ; ≋-equiv       = λ Γ → ≈ₛ-equiv
          ; wk            = wkSub
          ; wk-pres-≋     = wkSub-pres-≈ₛ
          ; wk-pres-refl  = wkSub-pres-refl
          ; wk-pres-trans = wkSub-pres-trans
          }          

lookup-fun : Var Δ τ → Sub Γ Δ → 𝒯 τ ₀ Γ
lookup-fun zero     (s `, t) = t
lookup-fun (succ x) (s `, _) = lookup-fun x s

lookup-pres-≋ : (x : Var Δ τ) → Pres-≋ (Sub' Δ) (𝒯 τ) (lookup-fun x)
lookup-pres-≋ zero     (_ `, t≋t') = t≋t'
lookup-pres-≋ (succ x) (p `, _)    = lookup-pres-≋ x p

lookup-nat : (x : Var Δ τ) → Natural (Sub' Δ) (𝒯 τ) (lookup-fun x)
lookup-nat zero     w (_ `, _) = ≈-refl
lookup-nat (succ x) w (δ `, _) = lookup-nat x w δ

lookup : Var Δ τ → Sub' Δ →̇ 𝒯 τ
lookup x = record
    { fun     = lookup-fun x
    ; pres-≋  = lookup-pres-≋ x
    ; natural = lookup-nat x
    }
    
trimSub-fun : Δ ⊆ Δ' → Sub Γ Δ' → Sub Γ Δ
trimSub-fun []       δ = []
trimSub-fun (r `, x) δ = (trimSub-fun r δ) `, lookup-fun x δ

trimSub-pres-≋ : (r : Δ ⊆ Δ') → Pres-≋ (Sub' Δ') (Sub' Δ) (trimSub-fun r)
trimSub-pres-≋ []       δ≋δ' = []
trimSub-pres-≋ (r `, x) δ≋δ' = trimSub-pres-≋ r δ≋δ' `, lookup-pres-≋ x δ≋δ'

trimSub-nat : (r : Δ ⊆ Δ') → Natural (Sub' Δ') (Sub' Δ) (trimSub-fun r)
trimSub-nat r r' δ = {!!}

trimSub : Δ ⊆ Δ' → Sub' Δ' →̇ Sub' Δ
trimSub r = record
  { fun     = trimSub-fun r
  ; pres-≋  = trimSub-pres-≋ r
  ; natural = trimSub-nat r
  }

trimSub-pres-refl : trimSub ⊆-refl ≈̇ id'[ Sub' Δ ]
_≈̇_.proof trimSub-pres-refl []       = []
_≈̇_.proof trimSub-pres-refl (δ `, x) = {!!} `, ≋[ 𝒯 _ ]-refl

trimSub-pres-trans : (r : Δ ⊆ Δ') (r' : Δ' ⊆ Δ'') → trimSub (⊆-trans r r') ≈̇ trimSub r ∘ trimSub r'
_≈̇_.proof (trimSub-pres-trans [] r')       δ = []
_≈̇_.proof (trimSub-pres-trans (r `, x) r') δ = (_≈̇_.proof (trimSub-pres-trans r r') δ) `, {!!}

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
    ; natural = λ r bp → ≋[ 𝒫 ]-trans (bp .natural r ⊢ₛ-refl) (bp .apply-≋ {!!})
    }

substVar-fun = lookup

substVar : Var' τ →̇ ◼ (𝒯 τ)
substVar = record
    { fun     = substVar-fun
    ; pres-≋  = λ { refl → record { proof = λ δ → ≋[ 𝒯 _ ]-refl } }
    ; natural = λ r x → record { proof = λ δ → {!!} } 
    }

module Action
  (μ  : {τ : Ty} → 𝒯 τ →̇ ◼ (𝒯 τ)) where

  ⊢ₛ-trans : Sub Γ Δ → Sub Δ Δ' → Sub Γ Δ'
  ⊢ₛ-trans δ []        = []
  ⊢ₛ-trans δ (δ' `, t) = ⊢ₛ-trans δ δ' `, μ .apply t .apply δ

  ◼-δ : {𝒫 : Psh} → ◼ 𝒫 →̇ ◼ ◼ 𝒫
  ◼-δ = {!!}
  
  record SubLaws : Set₁ where
  
   field
    -- think "substTm (var x) δ = lookup x δ"
    μ-lunit : μ ∘ var ≈̇ substVar {τ}
    
    -- think "substTm-pres-refl"
    μ-runit : ◼-ϵ ∘ μ ≈̇ id' {𝒯 τ}

    -- think "substTm-pres-trans"
    μ-assoc : ◼-map μ ∘ μ ≈̇ ◼-δ ∘ μ {τ}
