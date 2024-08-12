{-# OPTIONS --safe --without-K #-}

open import Lambda

open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsEquivalence; Setoid)

import Relation.Binary.Reasoning.Setoid as EqReasoning

open import Relation.Binary.PropositionalEquality
  using    (_≡_ ; cong ; cong₂ ; module ≡-Reasoning ; subst ; subst₂)
  renaming (refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans ; isEquivalence to ≡-equiv)

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

≡-to-≈ₛ : {δ δ' : Sub Γ Δ} → δ ≡ δ' → δ ≈ₛ δ'
≡-to-≈ₛ ≡-refl = ≈ₛ-refl

wkSub-pres-≈ₛ : (r : Γ ⊆ Γ') {δ δ' : Sub Γ Δ} → δ ≈ₛ δ' → wkSub r δ ≈ₛ wkSub r δ'
wkSub-pres-≈ₛ r []             = []
wkSub-pres-≈ₛ r (δ≈ₛδ' `, t≋t') = (wkSub-pres-≈ₛ r δ≈ₛδ') `, (wk[ 𝒯 _ ]-pres-≋ r t≋t')

wkSub-pres-refl : (δ : Sub Γ Δ) → wkSub ⊆-refl δ ≈ₛ δ
wkSub-pres-refl []       = []
wkSub-pres-refl (δ `, t) = (wkSub-pres-refl δ) `, wk[ 𝒯 _ ]-pres-refl t

wkSub-unit-left = wkSub-pres-refl

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

wkSub-unit-right : (r : Γ ⊆ Γ') → wkSub r ⊢ₛ-refl[ Γ ] ≈ₛ ⊆-to-ₛ⊣ r
wkSub-unit-right []           = ≈ₛ-refl
wkSub-unit-right {Γ} (r `, x) = let open EqReasoning ≋[ Sub' Γ ]-setoid in begin
  wkSub (r `, x) (wkSub ⊆-fresh ⊢ₛ-refl) `, wk[ 𝒯 _ ] (r `, x) (var .apply zero)
    ≈⟨ ≈ₛ-sym (wkSub-pres-trans ⊆-fresh (r `, x) ⊢ₛ-refl) `, var .natural (r `, x) zero ⟩
  wkSub (⊆-trans ⊆-fresh (r `, x)) ⊢ₛ-refl `, var .apply (wkVar (r `, x) zero)
    ≡⟨ cong (_`, _) (cong₂ wkSub (≡-trans (lemma1 _ _ _) (⊆-refl-unit-left r)) ≡-refl) ⟩
  wkSub r ⊢ₛ-refl `, var .apply (wkVar (r `, x) zero)
    ≈⟨ (wkSub-unit-right r `, ≈-refl) ⟩
  ⊆-to-ₛ⊣ r `, var .apply (wkVar (r `, x) zero)
    ≡⟨⟩
  ⊆-to-ₛ⊣ r `, var .apply x ∎

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

lookup-unit-right : (x : Var Δ τ) → lookup-fun x ⊢ₛ-refl[ Δ ] ≈ var .apply x
lookup-unit-right zero     = ≈-refl
lookup-unit-right (succ x) = let open EqReasoning ≋[ 𝒯 _ ]-setoid in begin
  lookup-fun x (wkSub ⊆-fresh ⊢ₛ-refl)
    ≈˘⟨ lookup-nat x ⊆-fresh ⊢ₛ-refl ⟩
  wk[ 𝒯 _ ] ⊆-fresh (lookup-fun x ⊢ₛ-refl)
    ≈⟨ wk[ 𝒯 _ ]-pres-≋ ⊆-fresh (lookup-unit-right x) ⟩
  wk[ 𝒯 _ ] ⊆-fresh (var .apply x)
    ≈⟨ var .natural ⊆-fresh x ⟩
  var .apply (wkVar ⊆-fresh x)
    ≈⟨ var .apply-≋ (wkIncr x) ⟩
  var .apply (succ x) ∎

trimSub-fun : Δ ⊆ Δ' → Sub Γ Δ' → Sub Γ Δ
trimSub-fun []       δ = []
trimSub-fun (r `, x) δ = (trimSub-fun r δ) `, lookup-fun x δ

-- observe that trimSub does indeed "trim" a substitution
trimSub-fun-drop-action : (r : Δ ⊆ Δ') (δ : Sub Γ Δ') {t : Tm Γ τ}
  → trimSub-fun (⊆-drop r) (δ `, t) ≡ trimSub-fun r δ
trimSub-fun-drop-action []       δ = ≡-refl
trimSub-fun-drop-action (r `, x) δ = cong₂ _`,_ (trimSub-fun-drop-action r δ) ≡-refl

trimSub-pres-≋ : (r : Δ ⊆ Δ') → Pres-≋ (Sub' Δ') (Sub' Δ) (trimSub-fun r)
trimSub-pres-≋ []       δ≋δ' = []
trimSub-pres-≋ (r `, x) δ≋δ' = trimSub-pres-≋ r δ≋δ' `, lookup-pres-≋ x δ≋δ'

trimSub-nat : (r : Δ ⊆ Δ') → Natural (Sub' Δ') (Sub' Δ) (trimSub-fun r)
trimSub-nat []       r' δ = ≈ₛ-refl
trimSub-nat (r `, x) r' δ = trimSub-nat r r' δ `, lookup-nat x r' δ

trimSub : Δ ⊆ Δ' → Sub' Δ' →̇ Sub' Δ
trimSub r = record
  { fun     = trimSub-fun r
  ; pres-≋  = trimSub-pres-≋ r
  ; natural = trimSub-nat r
  }

trimSub-pres-refl : trimSub ⊆-refl ≈̇ id'[ Sub' Δ ]
_≈̇_.proof trimSub-pres-refl []       = []
_≈̇_.proof trimSub-pres-refl (δ `, x) =
  ≈ₛ-trans
    (≡-to-≈ₛ (trimSub-fun-drop-action ⊆-refl δ))
    (trimSub-pres-refl .apply-≋ δ)
  `, ≋[ 𝒯 _ ]-refl

-- TODO: rename
assoc-lookup-wkVar : (x : Var Δ' τ) (r' : Δ' ⊆ Δ'') (δ : Sub' Δ'' ₀ Γ)
  → lookup-fun (wkVar r' x) δ ≈ lookup-fun x (trimSub-fun r' δ)
assoc-lookup-wkVar zero     (r' `, x) δ = ≈-refl
assoc-lookup-wkVar (succ x) (r' `, y) δ = assoc-lookup-wkVar x r' δ

trimSub-pres-trans : (r : Δ ⊆ Δ') (r' : Δ' ⊆ Δ'')
  → trimSub (⊆-trans r r') ≈̇ trimSub r ∘ trimSub r'
_≈̇_.proof (trimSub-pres-trans [] r')       δ
  = []
_≈̇_.proof (trimSub-pres-trans (r `, x) r') δ
  = (_≈̇_.proof (trimSub-pres-trans r r') δ) `, assoc-lookup-wkVar x r' δ

trimSub-unit-right : (r : Γ ⊆ Γ') → trimSub-fun r ⊢ₛ-refl ≈ₛ ⊆-to-ₛ⊣ r
trimSub-unit-right []       = ≈ₛ-refl
trimSub-unit-right (r `, x) = trimSub-unit-right r `, lookup-unit-right x

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
    ; natural = λ r bp → let open EqReasoning ≋[ 𝒫 ]-setoid in begin
      wk[ 𝒫 ] r (bp .apply ⊢ₛ-refl)
        ≈⟨ bp .natural r ⊢ₛ-refl ⟩
      bp .apply (wkSub r ⊢ₛ-refl)
        ≈⟨ bp .apply-≋ (wkSub-unit-right r) ⟩
      bp .apply (⊆-to-ₛ⊣ r)
        ≈˘⟨ bp .apply-≋ (trimSub-unit-right r) ⟩
      bp .apply (trimSub-fun r ⊢ₛ-refl) ∎
    }

substVar-fun = lookup

substVar : Var' τ →̇ ◼ (𝒯 τ)
substVar = record
    { fun     = substVar-fun
    ; pres-≋  = λ { ≡-refl → record { proof = λ δ → ≋[ 𝒯 _ ]-refl } }
    ; natural = λ r x → record { proof = λ δ → ≈-sym (assoc-lookup-wkVar x r δ) }
    }

module Action
  (μ  : {τ : Ty} → 𝒯 τ →̇ ◼ (𝒯 τ)) where

  ⊢ₛ-trans : Sub Γ Δ → Sub Δ Δ' → Sub Γ Δ'
  ⊢ₛ-trans δ []        = []
  ⊢ₛ-trans δ (δ' `, t) = ⊢ₛ-trans δ δ' `, μ .apply t .apply δ

  ◼-δ : {𝒫 : Psh} → ◼ 𝒫 →̇ ◼ ◼ 𝒫
  ◼-δ {𝒫} = record
    { fun     = λ bp → record
      { fun     = λ δ → record
        { fun     = λ δ' → bp .apply (⊢ₛ-trans δ' δ)
        ; pres-≋  = λ δ'≋γ' → bp .apply-≋ {!!}
        ; natural = λ r δ' → ≋[ 𝒫 ]-trans (bp .natural r (⊢ₛ-trans δ' δ)) (bp .apply-≋ {!!})
        }
      ; pres-≋  = λ δ≋γ → record { proof = λ δ' → bp .apply-≋ {!!} }
      ; natural = λ r δ' → record { proof = {!!} } }
    ; pres-≋  = λ bp≋bp' → record { proof = λ δ → record { proof = λ δ' → bp≋bp' .apply-≋ (⊢ₛ-trans δ' δ) } }
    ; natural = λ r bp → record { proof = λ p → record { proof = λ p₁ → bp .apply-≋ {!!} } } }
  
  record SubLaws : Set₁ where
  
   field
    -- think "substTm (var x) δ = lookup x δ"
    μ-lunit : μ ∘ var ≈̇ substVar {τ}
    
    -- think "substTm-pres-refl"
    μ-runit : ◼-ϵ ∘ μ ≈̇ id' {𝒯 τ}

    -- think "substTm-pres-trans"
    μ-assoc : ◼-map μ ∘ μ ≈̇ ◼-δ ∘ μ {τ}
