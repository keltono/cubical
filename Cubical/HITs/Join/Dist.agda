{-# OPTIONS  --cubical #-}
module Cubical.HITs.Join.Dist where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence 
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.Join renaming (inl to inlj ; inr to inrj ; push to pushj)
open import Cubical.Data.Sigma renaming (fst to π₁; snd to π₂)
open import Cubical.HITs.Wedge
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout 
open import Cubical.Data.Unit renaming (Unit to ⊤)


module _ {ℓ ℓ' ℓ''} ((A , ⋆a) : Pointed ℓ) ((B , ⋆b) : Pointed ℓ') ((C , ⋆c) : Pointed ℓ'') where
  c→AC : C → A × C
  c→AC c = ⋆a , c
  c→BC : C → B × C
  c→BC c = ⋆b , c
  π₁AC : A × C → A
  π₁AC = π₁
  π₂AC : A × C → C
  π₂AC = π₂

  π₁BC : B × C → B
  π₁BC = π₁
  π₂BC : B × C → C
  π₂BC = π₂
  
  span : 3x3-span
  span = record {
        A00 =  A;  A02 = A × C;   A04 =  C;
        A20 = ⊤;  A22 =  C;  A24 =  C;
        A40 =  B;  A42 = B × C;  A44 =  C;
        f10 =  λ x → ⋆a;
        f12 =  c→AC; f14 =  λ x → x;
        f30 = λ x → ⋆b; f32 =  c→BC; f34 =  λ x → x; 
        f01 =  π₁;   f21 =  λ x → tt; f41 =  π₁; 
        f03 =  π₂;   f23 =  λ x → x;  f43 =  π₂; 
        H11 =  λ x → refl;    H13 =  λ x → refl;    H31 =  λ x → refl;    H33 =  λ x → refl
    }
    
  f1□' : 3x3-span.A2□ span  → 3x3-span.A0□ span
  f1□' (inl tt) =  inl ⋆a
  f1□' (inr c) =  inr c
  f1□' (push c i) =  push (⋆a , c) i

  f1□≡f1□' : 3x3-span.f1□ span ≡ f1□'
  f1□≡f1□' = funExt f1□-retract
    where
        f1□-retract : ∀ x → 3x3-span.f1□ span x ≡ f1□' x
        f1□-retract (inl tt)   = refl
        f1□-retract (inr c)    = refl
        f1□-retract (push c i) = congS (λ x → x i) (sym (doubleCompPath-filler refl (push (⋆a , c)) refl))

  f3□' : 3x3-span.A2□ span → 3x3-span.A4□ span
  f3□' (inl tt) =  inl ⋆b
  f3□' (inr c) = inr c
  f3□' (push c i) = push (⋆b , c ) i

  f3□-retract : ∀ x →  3x3-span.f3□ span x ≡ f3□' x
  f3□-retract (inl tt)   = refl
  f3□-retract (inr c)    = refl
  f3□-retract (push c i) = congS (λ x → x i) (sym (doubleCompPath-filler refl (push (⋆b , c)) refl))
  f3□≡f3□' : 3x3-span.f3□ span ≡ f3□'
  f3□≡f3□' = funExt f3□-retract

  f□1' :  3x3-span.A□2  span  → 3x3-span.A□0 span
  f□1' (inl (a  , c)) = inl a
  f□1' (inr (a , c)) = inr a
  f□1'  (push a j) = push tt j

  f□3' : 3x3-span.A□2 span → 3x3-span.A□4 span
  f□3' (inl ( _ , c)) = inl c
  f□3' (inr ( _ , c )) = inr c
  f□3' (push c j) =  push c j

  f□3≡f□3' : 3x3-span.f□3 span ≡ f□3'
  f□3≡f□3' = funExt f□3-retract
     where
      f□3-retract : ∀ x → 3x3-span.f□3 span x ≡ f□3' x
      f□3-retract (inl _)    = refl
      f□3-retract (inr _)    = refl
      f□3-retract (push c i) = congS (λ x → x i) (sym (doubleCompPath-filler refl (push c) refl))

  f□1≡f□1' : 3x3-span.f□1 span ≡ f□1'
  f□1≡f□1' = funExt f□1-retract 
     where 
      f□1-retract : ∀ x → 3x3-span.f□1 span x ≡ f□1' x
      f□1-retract (inl _)    =  refl
      f□1-retract (inr _)    =  refl
      f□1-retract (push c i) =  congS (λ x → x i) (sym (doubleCompPath-filler refl (push tt) refl)) 


  A0□≃A*C : 3x3-span.A0□ span ≃ joinPushout A C
  A0□≃A*C =  pathToEquiv refl
  A2□≃Lift⊤ : 3x3-span.A2□ span ≃ Lift {ℓ-zero} {ℓ''} ⊤
  A2□≃Lift⊤ = isoToEquiv (iso  toLift fromLift lLiftCancel rLiftCancel)
     where
       toLift : 3x3-span.A2□ span → Lift {ℓ-zero} {ℓ''} ⊤
       toLift (inl tt)   = lift tt
       toLift (inr c)    = lift tt
       toLift (push c i) = lift tt
       fromLift : Lift {ℓ-zero} {ℓ''} ⊤ → 3x3-span.A2□ span 
       fromLift (lift tt) = inl tt
       lLiftCancel : ∀ x → toLift (fromLift x) ≡ x
       lLiftCancel (lift tt) =  refl
       rLiftCancel : ∀ x → fromLift (toLift x) ≡ x
       rLiftCancel (inl tt) =  refl
       rLiftCancel (inr c) =  push c
       rLiftCancel (push c i) j =  push c (i ∧ j) 

  A4□≃B*C : 3x3-span.A4□ span ≃ joinPushout B C
  A4□≃B*C = pathToEquiv refl
  A□0≡A∨B : 3x3-span.A□0  span ≡ ((A , ⋆a) ⋁ (B , ⋆b))
  A□0≡A∨B = refl

  A⋁B×C→AC⊔BC :  (((A , ⋆a) ⋁ (B , ⋆b)) × C) →  (Pushout c→AC c→BC)
  A⋁B×C→AC⊔BC (inl a , c) = inl ( a ,  c)
  A⋁B×C→AC⊔BC (inr b , c) = inr ( b , c)
  A⋁B×C→AC⊔BC (push tt i , c) =  push c i

  A⋁B×C≃A□2 : ((A , ⋆a) ⋁ (B , ⋆b)) × C ≃ 3x3-span.A□2  span 
  A⋁B×C≃A□2 =  isoToEquiv thm
          where
                thm : Iso (((A , ⋆a) ⋁ (B , ⋆b)) × C) (Pushout c→AC c→BC) 
                thm  =  iso  A⋁B×C→AC⊔BC f f⁻f ff⁻
                    where
                    f :  (Pushout c→AC c→BC) → (((A , ⋆a) ⋁ (B , ⋆b)) × C)
                    f (inl (a , c)) =  (inl a) , c
                    f (inr (b , c)) =  inr b , c
                    f (push c i) =  (push tt i) , c

                    ff⁻ : ∀ x → f (A⋁B×C→AC⊔BC x) ≡ x
                    ff⁻ (inl x , c) =  refl
                    ff⁻ (inr x , c) =  refl
                    ff⁻ (push a i , c) =  refl
                    f⁻f : ∀ x → A⋁B×C→AC⊔BC (f x) ≡ x
                    f⁻f (inl (a , c)) =  refl
                    f⁻f (inr (b , c)) =  refl
                    f⁻f (push c i) =  refl
  C≃A□4 : C ≃ 3x3-span.A□4  span 
  C≃A□4 =  pushoutIdfunEquiv (idfun C)  -- pushoutIdfunEquiv 

  p₂ : ((A , ⋆a) ⋁ (B , ⋆b)) × C → C
  p₂ = π₂
  p₁ : ((A , ⋆a) ⋁ (B , ⋆b)) × C → ((A , ⋆a) ⋁ (B , ⋆b))
  p₁ = π₁

  joinPushout∙ : ∀ {ℓ₁ ℓ₂} → (A : Pointed ℓ₁) → (B : Pointed ℓ₂) → Pointed (ℓ-max ℓ₁ ℓ₂)
  joinPushout∙ A B =  joinPushout (typ A) (typ B) , inl (pt A) 

  joinPushout∙≡join∙ : ∀ {ℓ₁ ℓ₂} (A' : Pointed ℓ₁) → (B' : Pointed ℓ₂) → joinPushout∙ A' B' ≡ join∙ A' B'
  joinPushout∙≡join∙ A B = ua∙ (joinPushout≃join (typ A) (typ B)) refl

  A□○ : 3-span
  A□○ = 3span f□1' f□3'
  A∨B*C-span : 3-span
  A∨B*C-span = 3span p₁ p₂

  f□1'f⁻¹≡p₁ : ∀ x → f□1' (A⋁B×C→AC⊔BC x) ≡ p₁ x
  f□1'f⁻¹≡p₁ (inl a , c) =  refl
  f□1'f⁻¹≡p₁ (inr b , c) =  refl
  f□1'f⁻¹≡p₁ (push tt i , c) =  refl

  f□1'f⁻¹≡inlp₂ : ∀ (x : ((A , ⋆a) ⋁ (B , ⋆b)) × C) → f□3' (A⋁B×C→AC⊔BC x) ≡ inl (p₂ x)
  f□1'f⁻¹≡inlp₂ (inl a , c) =  refl
  f□1'f⁻¹≡inlp₂ (inr b , c) =  sym (push c) 
  f□1'f⁻¹≡inlp₂ (push tt i , c) j =  push c (~ j ∧ i )  
  A□○=A∨B*C-span : 3-span-equiv A∨B*C-span A□○ 
  A□○=A∨B*C-span = record { 
       e0 = pathToEquiv refl ;
       e2 = A⋁B×C≃A□2  ;
       e4 = C≃A□4 ;
       H1 = λ x → (f□1'f⁻¹≡p₁ x ∙ sym (transportRefl (p₁ x))) ;
       H3 = f□1'f⁻¹≡inlp₂
       }
        
  Lift⊤→A*C : Lift {ℓ-zero} {ℓ''} ⊤ → joinPushout A C
  Lift⊤→A*C (lift tt) = inl ⋆a
  Lift⊤→B*C : Lift {ℓ-zero} {ℓ''} ⊤ → joinPushout B C
  Lift⊤→B*C (lift tt) = inl ⋆b

  A○□ : 3-span
  A○□ = 3span f1□' f3□'
  AC∨BC-span : 3-span
  AC∨BC-span = record
   { A0 =  joinPushout A C ; A2 =  Lift {ℓ-zero} {ℓ''} ⊤ ; A4 =  joinPushout B C ; f1 = Lift⊤→A*C  ; f3 = Lift⊤→B*C }

  A○□=AC∨BC-span : 3-span-equiv A○□ AC∨BC-span
  A○□=AC∨BC-span = record {
                e0 = A0□≃A*C ;
                e2 = A2□≃Lift⊤ ;
                e4 = A4□≃B*C ;
                H1 = λ x → inl⋆a≡f1□' x ∙ sym (transportRefl (f1□' x))   ;
                H3 = λ x → inl⋆b≡f3□' x ∙ sym (transportRefl (f3□' x))
            }
             where
               inl⋆a≡f1□' : ∀ x → inl ⋆a ≡ f1□' x
               inl⋆a≡f1□' (inl tt) =  refl
               inl⋆a≡f1□' (inr c) =  push (⋆a , c)
               inl⋆a≡f1□' (push c i) j =  push (⋆a , c) (i ∧ j) 
               inl⋆b≡f3□' : ∀ x → inl ⋆b ≡ f3□' x
               inl⋆b≡f3□' (inl tt) =  refl
               inl⋆b≡f3□' (inr c) = push (⋆b , c) 
               inl⋆b≡f3□' (push c i) j =  push (⋆b , c) (i ∧ j)


  ⊤→A*C : ⊤ → joinPushout A C
  ⊤→A*C tt = inl ⋆a
  ⊤→B*C : ⊤ → joinPushout B C
  ⊤→B*C tt = inl ⋆b
  
  A○□'≡A*C∨B*C' : (Pushout f1□' f3□') ≡ (Pushout Lift⊤→A*C Lift⊤→B*C)
  A○□'≡A*C∨B*C' = (spanEquivToPushoutPath  A○□=AC∨BC-span )

  A○□'≡A*C∨B*C'∙ : (Pushout f1□' f3□' , inl (inl ⋆a)) ≡ (Pushout Lift⊤→A*C Lift⊤→B*C  , inl (inl ⋆a))
  A○□'≡A*C∨B*C'∙ =  ua∙ ( pushoutEquiv f1□' f3□' Lift⊤→A*C Lift⊤→B*C A2□≃Lift⊤  A0□≃A*C A4□≃B*C
                           (sym (funExt (λ x → inl⋆a≡f1□' x ∙ sym (transportRefl (f1□' x)))) )
                           (sym (funExt (λ x → inl⋆b≡f3□' x ∙ sym (transportRefl (f3□' x))))))
                         ( 
                          (pushoutIso→ f1□' f3□' Lift⊤→A*C Lift⊤→B*C A2□≃Lift⊤ A0□≃A*C
                           A4□≃B*C
                           (λ i →
                              funExt
                              (λ x → inl⋆a≡f1□' x ∙ (λ i₁ → transportRefl (f1□' x) (~ i₁)))
                              (~ i))
                           (λ i →
                              funExt
                              (λ x → inl⋆b≡f3□' x ∙ (λ i₁ → transportRefl (f3□' x) (~ i₁)))
                              (~ i)))
                          (inl (inl ⋆a))
                         ≡⟨ refl ⟩
                          inl (π₁ A0□≃A*C (inl ⋆a)) 
                         ≡⟨ refl ⟩
                          inl (transport refl (inl ⋆a)) 
                         ≡⟨ congS (λ x → inl x) (transportRefl (inl ⋆a)) ⟩
                         inl (inl ⋆a)
                         ∎
                         )
             where
               inl⋆a≡f1□' : ∀ x → inl ⋆a ≡ f1□' x
               inl⋆a≡f1□' (inl tt) =  refl
               inl⋆a≡f1□' (inr c) =  push (⋆a , c)
               inl⋆a≡f1□' (push c i) j =  push (⋆a , c) (i ∧ j) 
               inl⋆b≡f3□' : ∀ x → inl ⋆b ≡ f3□' x
               inl⋆b≡f3□' (inl tt) =  refl
               inl⋆b≡f3□' (inr c) = push (⋆b , c) 
               inl⋆b≡f3□' (push c i) j =  push (⋆b , c) (i ∧ j)

  AP*C⋁BP*C≡A*C⋁B*C∙ : (Pushout ⊤→A*C ⊤→B*C , inl (inl ⋆a)) ≡ join∙ (A , ⋆a) (C , ⋆c) ⋁∙ₗ join∙ (B , ⋆b) (C , ⋆c) 
  AP*C⋁BP*C≡A*C⋁B*C∙ =
    Pushout ⊤→A*C ⊤→B*C , inl (inl ⋆a)
    ≡⟨ refl ⟩
    (joinPushout A C , inl ⋆a)  ⋁ (joinPushout B C , inl ⋆b) , inl (inl ⋆a) 
    ≡⟨ refl ⟩
    (joinPushout A C , inl ⋆a)  ⋁∙ₗ (joinPushout B C , inl ⋆b) 
    ≡⟨  congS (λ x → (x  ⋁∙ₗ (joinPushout B C , inl ⋆b)))
        (joinPushout∙≡join∙ (A , ⋆a) (C , ⋆c))     ⟩
    ( join∙ (A , ⋆a) (C , ⋆c)  ⋁∙ₗ (joinPushout B C , inl ⋆b) )
    ≡⟨  congS (λ x → ( join∙ (A , ⋆a) (C , ⋆c) ⋁∙ₗ x )) (joinPushout∙≡join∙ (B , ⋆b) (C , ⋆c))  ⟩
    ( join∙ (A , ⋆a) (C , ⋆c)  ⋁∙ₗ join∙  (B , ⋆b) (C , ⋆c))
    ∎ 

  AP*C⋁BP*C≡A*C⋁B*C : (Pushout ⊤→A*C ⊤→B*C) ≡ join∙ (A , ⋆a) (C , ⋆c) ⋁ join∙ (B , ⋆b) (C , ⋆c) 
  AP*C⋁BP*C≡A*C⋁B*C = (Pushout ⊤→A*C ⊤→B*C)
                       ≡⟨  refl ⟩
                       ( (joinPushout A C , inl ⋆a)  ⋁ (joinPushout B C , inl ⋆b) )
                       ≡⟨  congS (λ x → (x  ⋁ (joinPushout B C , inl ⋆b)))
                           (joinPushout∙≡join∙ (A , ⋆a) (C , ⋆c))     ⟩
                       ( join∙ (A , ⋆a) (C , ⋆c)  ⋁ (joinPushout B C , inl ⋆b) )
                       ≡⟨  congS (λ x → ( join∙ (A , ⋆a) (C , ⋆c) ⋁ x ))
                           (joinPushout∙≡join∙ (B , ⋆b) (C , ⋆c))  ⟩
                        join∙ (A , ⋆a) (C , ⋆c) ⋁ join∙ (B , ⋆b) (C , ⋆c)  ∎

  A*C∨B*C'IsoAP*C∨BP*C : Iso (Pushout Lift⊤→A*C Lift⊤→B*C) (Pushout ⊤→A*C ⊤→B*C)
  A*C∨B*C'IsoAP*C∨BP*C = iso foo foo⁻ foofoo⁻ foo⁻foo
    where
    foo : (Pushout Lift⊤→A*C Lift⊤→B*C) → (Pushout ⊤→A*C ⊤→B*C)
    foo (inl x) = inl x
    foo (inr x) = inr x
    foo (push (lift tt) i) = push tt i
    foo⁻ : (Pushout ⊤→A*C ⊤→B*C) → (Pushout Lift⊤→A*C Lift⊤→B*C)
    foo⁻ (inl x) = inl x
    foo⁻ (inr x) = inr x
    foo⁻ (push tt i) = push (lift tt) i 
    foo⁻foo : ∀ x → foo⁻ (foo x) ≡ x
    foo⁻foo (inl x) =  refl
    foo⁻foo (inr x) =  refl
    foo⁻foo (push a i) =  refl
    foofoo⁻ : ∀ x → foo (foo⁻ x) ≡ x
    foofoo⁻ (inl x) = refl
    foofoo⁻ (inr x) = refl
    foofoo⁻ (push a i) =  refl

  A*C∨B*C'≡AP*C∨BP*C∙ : (Pushout Lift⊤→A*C Lift⊤→B*C , inl (inl ⋆a) ) ≡ (Pushout ⊤→A*C ⊤→B*C , inl (inl ⋆a))
  A*C∨B*C'≡AP*C∨BP*C∙ =  ua∙ (isoToEquiv A*C∨B*C'IsoAP*C∨BP*C) refl

  A*C∨B*C'≡AP*C∨BP*C : (Pushout Lift⊤→A*C Lift⊤→B*C) ≡ (Pushout ⊤→A*C ⊤→B*C)
  A*C∨B*C'≡AP*C∨BP*C = isoToPath A*C∨B*C'IsoAP*C∨BP*C

  A○□≡A○□' : (Pushout (3x3-span.f1□ span) (3x3-span.f3□ span) ) ≡ (Pushout f1□' f3□') 
  A○□≡A○□' = congS (λ x → Pushout  (3x3-span.f1□ span) x) (f3□≡f3□') ∙ congS (λ x → Pushout  x f3□') (f1□≡f1□')

  A○□≡A○□'∙ : (_≡_) {A = Pointed _} (Pushout (3x3-span.f1□ span) (3x3-span.f3□ span) , inl (inl ⋆a)) (Pushout f1□' f3□' , inl (inl ⋆a))
  A○□≡A○□'∙ =  ua∙
                 (pushoutEquiv (3x3-span.f1□ span) (3x3-span.f3□ span) f1□' f3□' (idEquiv _) (idEquiv _) (idEquiv _)
                 ((∘-idʳ _) ∙ f1□≡f1□' ∙ sym (∘-idˡ _))
                 ((∘-idʳ _) ∙ f3□≡f3□' ∙ sym (∘-idˡ _))
                 )
                 refl 

  A□○≡A□○' : (Pushout (3x3-span.f□1 span) (3x3-span.f□3 span) ) ≡ (Pushout f□1' f□3') 
  A□○≡A□○' =  Pushout (3x3-span.f□1 span) (3x3-span.f□3 span)
              ≡⟨  congS (λ x → Pushout  (3x3-span.f□1 span) x) (f□3≡f□3')  ⟩
               Pushout (3x3-span.f□1 span) f□3' 
              ≡⟨  congS (λ x → Pushout  x f□3') (f□1≡f□1')  ⟩
              Pushout f□1' f□3' ∎

  A□○≡A□○'∙ : (_≡_) {A = Pointed _ } (Pushout (3x3-span.f□1 span) (3x3-span.f□3 span) , inl (inl ⋆a))  (Pushout f□1' f□3' , inl (inl ⋆a)) 
  A□○≡A□○'∙ = ua∙ ( pushoutEquiv (3x3-span.f□1 span) (3x3-span.f□3 span) f□1' f□3' (idEquiv _) (idEquiv _) (idEquiv _)
                    ((∘-idʳ _) ∙ f□1≡f□1' ∙ sym (∘-idˡ _))
                    ((∘-idʳ _) ∙ f□3≡f□3' ∙ sym (∘-idˡ _))
                    )
                   refl 


  A□○'≡A∨BP*C : (Pushout f□1' f□3' ) ≡  (Pushout p₁ p₂)
  A□○'≡A∨BP*C =  
   sym (spanEquivToPushoutPath  A□○=A∨B*C-span )

  A□○'≡A∨BP*C∙ :  (Pushout p₁ p₂ , inl (inl ⋆a)) ≡ (Pushout f□1' f□3' , inl (inl ⋆a)) 
  A□○'≡A∨BP*C∙  = ua∙ (pushoutEquiv  p₁ p₂ f□1' f□3' A⋁B×C≃A□2 (idEquiv _) C≃A□4
                   (sym (funExt (λ x → (f□1'f⁻¹≡p₁ x)))) ( sym (funExt f□1'f⁻¹≡inlp₂)))
                   refl


  A∨BP*C≡A∨B*C : (Pushout p₁ p₂) ≡ (join ((A , ⋆a) ⋁ (B , ⋆b)) C)
  A∨BP*C≡A∨B*C =   joinPushout≡join ((A , ⋆a) ⋁ (B , ⋆b)) C
  A∨BP*C≡A∨B*C∙ : (Pushout p₁ p₂ , inl (inl ⋆a)) ≡ (join ((A , ⋆a) ⋁ (B , ⋆b)) C , inlj (inl ⋆a))
  A∨BP*C≡A∨B*C∙ = ua∙ (joinPushout≃join (((A , ⋆a) ⋁ (B , ⋆b))) C)  refl 

  3x3∙ : (Pushout (3x3-span.f□1 span) (3x3-span.f□3 span) , inl (inl ⋆a))  ≡ (Pushout (3x3-span.f1□ span) (3x3-span.f3□ span) , inl (inl ⋆a))
  3x3∙ = ua∙ (isoToEquiv (3x3-span.3x3-Iso span))  refl
  A*C⋁B*C≡A⋁B*C : join∙ (A , ⋆a) (C , ⋆c) ⋁ join∙ (B , ⋆b) (C , ⋆c) ≡ (join ((A , ⋆a) ⋁ (B , ⋆b)) C)
  A*C⋁B*C≡A⋁B*C =  join∙ (A , ⋆a) (C , ⋆c) ⋁ join∙ (B , ⋆b) (C , ⋆c) 
                   ≡⟨ sym (AP*C⋁BP*C≡A*C⋁B*C)  ⟩
                    Pushout ⊤→A*C ⊤→B*C
                   ≡⟨ sym (A*C∨B*C'≡AP*C∨BP*C)  ⟩
                    Pushout Lift⊤→A*C Lift⊤→B*C
                   ≡⟨ sym (A○□'≡A*C∨B*C')  ⟩
                    Pushout f1□' f3□'
                   ≡⟨ sym (A○□≡A○□') ⟩
                     Pushout (3x3-span.f1□ span) (3x3-span.f3□ span) 
                   ≡⟨  sym (3x3-span.3x3-lemma span)  ⟩
                    Pushout (3x3-span.f□1 span) (3x3-span.f□3 span) 
                   ≡⟨ A□○≡A□○' ⟩
                    Pushout f□1' f□3'
                   ≡⟨  A□○'≡A∨BP*C   ⟩
                    Pushout p₁ p₂
                   ≡⟨  A∨BP*C≡A∨B*C  ⟩
                    join ((A , ⋆a) ⋁ (B , ⋆b)) C ∎
  A*C⋁B*C≡A⋁B*C∙ : join∙ (A , ⋆a) (C , ⋆c) ⋁∙ₗ join∙ (B , ⋆b) (C , ⋆c) ≡ join∙  ((A , ⋆a) ⋁∙ₗ (B , ⋆b)) (C , ⋆c)
  A*C⋁B*C≡A⋁B*C∙ = join∙ (A , ⋆a) (C , ⋆c) ⋁∙ₗ join∙ (B , ⋆b) (C , ⋆c)
                    ≡⟨ sym AP*C⋁BP*C≡A*C⋁B*C∙ ⟩
                     Pushout ⊤→A*C ⊤→B*C , inl (inl ⋆a)
                    ≡⟨ sym A*C∨B*C'≡AP*C∨BP*C∙ ⟩
                     Pushout Lift⊤→A*C Lift⊤→B*C , inl (inl ⋆a)
                    ≡⟨  sym A○□'≡A*C∨B*C'∙ ⟩
                    Pushout f1□' f3□' , inl (inl ⋆a)
                    ≡⟨  sym A○□≡A○□'∙  ⟩
                     Pushout (3x3-span.f1□ span) (3x3-span.f3□ span) , inl (inl ⋆a)
                    ≡⟨ sym 3x3∙ ⟩
                     Pushout (3x3-span.f□1 span) (3x3-span.f□3 span) , inl (inl ⋆a)
                    ≡⟨ A□○≡A□○'∙ ⟩
                     Pushout f□1' f□3' , inl (inl ⋆a)
                    ≡⟨  sym A□○'≡A∨BP*C∙ ⟩
                    Pushout p₁ p₂ , inl (inl ⋆a)
                    ≡⟨  A∨BP*C≡A∨B*C∙ ⟩
                    join∙  ((A , ⋆a) ⋁∙ₗ (B , ⋆b)) (C , ⋆c)
                     ∎


