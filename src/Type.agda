{-# OPTIONS --safe --without-K #-}
module Type where

infixr 7 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : (τ : Ty) → (σ : Ty) → Ty

variable
  τ τ' τ'' σ σ' σ'' : Ty
