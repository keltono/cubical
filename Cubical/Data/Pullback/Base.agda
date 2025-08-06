{-# OPTIONS --safe #-}
module Cubical.Data.Pullback.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout

module _  {ℓ ℓ' ℓ''} where
    Pullback : ∀ (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'') → (A → C)  → (B → C) →  Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    Pullback  A B C f g = Σ A (λ a → Σ B (λ b → f a ≡ g b))

    pₗ : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → C} {g : B → C} →  Pullback A B C f g → A
    pₗ (a , _ , _) = a

    pᵣ : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}  {f : A → C} {g : B → C} → Pullback A B C f g → B
    pᵣ (_ , b , _) = b


    CospanCone : ∀ {ℓ₃} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}  → (f : A → C) →  (g  : B → C) → (D : Type ℓ₃) → Type _ 
    CospanCone {A = A} {B = B} f g D =  Σ (D → A)  (λ p → Σ (D → B) (λ q → f ∘ p  ≡ g ∘ q))

    pullbackFormsCocone : ∀ {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}  (f : A → C) → (g : B → C) → spanCocone pₗ pᵣ C
    pullbackFormsCocone  f g = (  f ,  g ,  funExt  coconeCoherence )
      where
        coconeCoherence : ∀ x → f (pₗ x) ≡ g (pᵣ x)
        coconeCoherence (a , b , coh) =  coh  

