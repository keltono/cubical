module Cubical.Cohomology.GroupCohomology where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Functions.Image
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat renaming ( _·_  to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty renaming (rec to rec⊥)
open import Cubical.Data.Fin
open import Cubical.Data.Bool hiding (isProp≤)
open import Cubical.Data.Unit renaming (Unit to ⊤; Unit* to ⊤*)
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Algebra.Group.Base
open import Cubical.Data.Pullback
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SequentialColimit renaming (elim to elim-SeqColim)
open import Cubical.Data.Sequence
open import Cubical.HITs.PropositionalTruncation renaming (rec to rec∥∥ ; rec2 to rec2∥∥ ; rec3 to rec3∥∥ ; map to map∥∥)
open import Cubical.HITs.Join
open import Cubical.HITs.Sn
open import Cubical.Data.Sigma 
open import Cubical.HITs.Join.Dist
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Data.Sum
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary

private
  variable ℓᵧ : Level

module _ (Group@(G , str) : Group ℓᵧ) where
  open GroupStr str
  -- I'm going to put everything I need in here without thinking, can be moved around later


  f∙ : ∀ {ℓ ℓ'} (A : Pointed ℓ) → ⊤* {ℓ'}  → (typ A)
  f∙ (A , a) tt* = a

  _*ⁿ_ : ∀ {ℓ} (A : Type ℓ) → (n : ℕ) → Type ℓ
  _*ⁿ_  A zero = A
  _*ⁿ_  A (suc n') =  join A (A *ⁿ n') 

  *-incl : ∀ {ℓ} (A : Type ℓ) → (n : ℕ) → A *ⁿ n → A *ⁿ (suc n)
  *-incl A n aj =  inr aj 

  *-seq : ∀ {ℓ} (A : Type ℓ) →  Sequence ℓ
  *-seq A = sequence (λ n →  A *ⁿ n) λ {n} → *-incl A n 

  --future work :) (proven in Rijke's PhD thesis)
  *-seq-prop : ∀ {ℓ} (A : Type ℓ) → SeqColim (*-seq A) ≡  ∥ A ∥₁  
  *-seq-prop A = _


   
  domain : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type ℓ
  domain {A = A} f = A

  liftDomain :  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Lift {j = ℓ''} A → B
  liftDomain f (lift a) = f a

  -- could also lift A 
  interleaved mutual
    imⁿ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (n : ℕ) → Type ℓ
    _f*ⁿ_ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) → (n : ℕ) → imⁿ f n → B

    imⁿ {A = A} f zero =  A

    f f*ⁿ zero =  f

    imⁿ {A = A} {B = B} f (suc n) = Pushout (pₗ {f = f} {g = f f*ⁿ  n} ) (pᵣ {f = f} {f f*ⁿ  n})

    _f*ⁿ_ {A = A} {B = B} f (suc n) = →join f (f f*ⁿ  n)
  
  im⁺ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) (n : ℕ) → imⁿ f n → imⁿ f  (suc n)
  im⁺ {A = A} {B = B} f n = inr


  im-seq : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) →  Sequence ℓ
  im-seq f = sequence (imⁿ f)  λ {n} → im⁺ f n

   

  im∞ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) → Type ℓ
  im∞ f =  SeqColim (im-seq f) 

 
  f*∞ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) → im∞ f → B
  f*∞ {ℓ} {A} {B} f = elim-SeqColim (im-seq f)(λ _ → B) elimData 
     where
       coheres : {n : ℕ} (x : imⁿ f n) → (f f*ⁿ n) x ≡ (f f*ⁿ (suc n)) (im⁺ f n x)
       coheres {zero} x =  refl
       coheres {suc n} x =  refl
       elimData : ElimData (im-seq f) (λ _ → B)
       elimData = elimdata (λ {n} →  f f*ⁿ n) coheres

  -- for now, just assume 
  -- should not overly difficult to prove with the fiber sequence things, just some complexity with convergance (wrt formalizing 5.4, see below)
  f∞-equiv : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B)  → isEquiv (f*∞ f )
  f∞-equiv = _



  -- proven in the hott book
  im∞≡im : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} (f : A → B) → im∞ f ≡ Image f
  im∞≡im f = _

  

  Ker∙ : ∀ {ℓ ℓ'} {A : Type ℓ} (B : Pointed ℓ') (f : A → typ B) → Type (ℓ-max ℓ ℓ')
  Ker∙ B f =  fiber f (pt B) 



  Ker∙P : ∀ {ℓ ℓ'} {A : Type ℓ} (B : Pointed ℓ') (f : A → typ B) → Type (ℓ-max ℓ ℓ')
  Ker∙P {ℓ} {ℓ'} {A} B f =  Pullback A (⊤* {ℓ}) (typ B) f (f∙ B) 

                                                                                                                      
  theorem5 : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → C} {g : B → C} {x : C} → fiber (→join f g) x ≡ join (fiber f x) (fiber g x)
  theorem5 = {!!}


  join⊥≡id : ∀ {ℓ} (F :  Type ℓ) → join F (⊥* {ℓ}) ≡ F
  join⊥≡id F = isoToPath (iso foo foo- (λ x → refl) invf)
    where
     foo : join F ⊥* → F
     foo (inl x) =  x
     foo- : F → join F ⊥*
     foo- x = inl x
     invf : ∀ x → foo- (foo x) ≡ x
     invf (inl x) = refl


  



  ΩP : ∀ {ℓ} →  Pointed ℓ → Pointed ℓ
  ΩP {ℓ} A = (Pullback (⊤* {ℓ}) (⊤* {ℓ}) (typ A) (f∙ A) (f∙ A) , (tt* , tt* , refl))

  ΩP≡Ω : ∀ {ℓ} {A : Pointed ℓ} → typ (ΩP A) ≡ typ (Ω A)
  ΩP≡Ω {A = A} = isoToPath (iso ( λ (tt* , tt* , x) → x) ( λ x → (tt* , tt* , x)) ( λ x → refl)  λ x → refl )

  
                                                                                     -- equivalent to being 2-connected (or 0-conn. in book terminology)
  lemma9 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Pointed ℓ'} (f : A → typ B) → isContr (Ker∙ B f) → Σ[ x ∈ typ B ] (∀ y → ∥ x ≡ y ∥₁)  → isEquiv f
  lemma9 {A = A} {B = B} f kerIsContr (ptB' , bConn)  =
    record { equiv-proof =  λ y → rec∥∥ {A = y ≡ (pt B)}
                                        (isPropIsContr {A = fiber f y})
                                        (λ y≡ptB →  subst (λ b → isContr (fiber f b)) (sym y≡ptB) kerIsContr)
                                        (rec2∥∥ (isPropPropTrunc {A = (y ≡ pt B)}) (λ y≡ptB' ptB'≡ptB →  ∣ y≡ptB' ∙ ptB'≡ptB ∣₁ ) (map∥∥ sym (bConn y)) ( bConn (pt B)))
                                        }

  
  

  Ker∙≡Pull : ∀ {ℓ ℓ'}  {A : Type ℓ} {B : Pointed ℓ'} (f : A → typ B) → Ker∙ B f ≡ Ker∙P B f
  Ker∙≡Pull {B = B} f = isoToPath ( iso foo  foo⅋ ( λ x → refl)  λ x → refl)
     where
       foo : Ker∙ B f → Ker∙P B f
       foo (a , fa≡⋆b) =  (a , tt* , fa≡⋆b )
       foo⅋ : Ker∙P B f → Ker∙ B f
       foo⅋ (a , tt* , p) =  a , p


  -- there are a few holes above, but the only relate to correctness proofs, nothing about the actual computations.

  BG : Pointed ℓᵧ
  BG = (EM₁ Group , embase) 

  f : ⊤* {ℓᵧ} → EM₁ Group
  f  = f∙ BG

  kerf≡G : Ker∙ BG f ≡ G
  kerf≡G = Ker∙ BG f   ≡⟨ Ker∙≡Pull f ⟩
           Ker∙P BG f  ≡⟨ refl ⟩
           typ (ΩP BG) ≡⟨ ΩP≡Ω ⟩
           typ (Ω BG)  ≡⟨ ΩEM₁≡ Group ⟩
           G ∎

  Ker∙⊥≡⊥ : ∀ {ℓ} {A : Pointed ℓ} → Ker∙ {ℓ} {ℓ} A (rec* {ℓ}) ≡ ⊥* 

  Ker∙⊥≡⊥ {A = A} = isoToPath  (iso (λ ()) (λ ()) (λ ()) λ ())

  kerf*ⁿSn≡kerfn*G : ∀ n → Ker∙ BG (f f*ⁿ (suc n)) ≡ join (Ker∙ BG (f f*ⁿ n)) G
  kerf*ⁿSn≡kerfn*G n =  Ker∙ BG (→join f (f f*ⁿ n))
                        ≡⟨ refl ⟩
                        fiber (→join f (f f*ⁿ n)) (pt BG) 
                        ≡⟨ theorem5 ⟩
                        join (fiber f (pt BG)) (fiber (f f*ⁿ n) (pt BG))
                        ≡⟨  congS (λ x → join x (fiber (f f*ⁿ n) (pt BG))) kerf≡G ⟩
                        join G (fiber (f f*ⁿ n) (pt BG))
                        ≡⟨  isoToPath join-comm ⟩
                        join (Ker∙ BG (f f*ⁿ n)) G ∎
  -- induction proof! wowee
  kerf*ⁿSn≡G*n : ∀ n → Ker∙ BG (f f*ⁿ n) ≡ G *ⁿ n
  kerf*ⁿSn≡G*n zero = kerf≡G
  kerf*ⁿSn≡G*n (suc n) =  Ker∙ BG (f f*ⁿ suc n) ≡⟨ kerf*ⁿSn≡kerfn*G n ⟩
                          join (Ker∙ BG (f f*ⁿ n)) G ≡⟨  congS (λ x → join x G) (kerf*ⁿSn≡G*n n) ⟩
                          join (G *ⁿ n) G ≡⟨  isoToPath join-comm ⟩
                          (G *ⁿ suc n) ∎


  ⋁ᵐ : ∀ {ℓ} (m : ℕ) → Pointed ℓ → Pointed ℓ
  -- m = 1
  ⋁ᵐ 0 A = A
  -- m = m' + 1
  ⋁ᵐ (suc m) A =  A ⋁∙ₗ (⋁ᵐ m A)

  -- A*C⋁B*C≡A⋁B*C : join∙ (A , ⋆a) (C , ⋆c) ⋁ join∙ (B , ⋆b) (C , ⋆c) ≡ (join ((A , ⋆a) ⋁ (B , ⋆b)) C)
  repeatedDist : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} {m : ℕ} → join∙  (⋁ᵐ m A) B ≡  (⋁ᵐ m (join∙ A B))
  repeatedDist {A = A} {B} {zero} =  refl
  repeatedDist {A = A} {B} {suc m} =
    join∙ (⋁ᵐ (suc m) A)  B
    ≡⟨ refl ⟩
    join∙ (A ⋁∙ₗ (⋁ᵐ m A))  B
    ≡⟨ {!!} ⟩
    (join∙ A B) ⋁∙ₗ join∙ (⋁ᵐ m A)  B
    ≡⟨ {!!} ⟩
    {!!}
    ∎


  notF≡Empty : ∀ (F : Type) → ¬ F → F ≡ ⊥
  notF≡Empty F ¬F =  ua ( ¬F , record { equiv-proof = λ () })

  FinSm≡⊤+Finm : ∀ m → Fin (suc m) ≡ ⊤ ⊎ Fin m
  FinSm≡⊤+Finm m =  isoToPath (iso  bleh bleh' bb' b'b)
    where
      bleh : Fin (suc m) → ⊤ ⊎ Fin m
      bleh (zero , p) = inl tt
      bleh (suc n , p) = inr (n ,  pred-≤-pred p )
      bleh' :  ⊤ ⊎ Fin m → Fin (suc m)
      bleh' (inl x) =  (zero , suc-≤-suc  zero-≤)
      bleh' (inr x) =  fsuc x
      bb' : ∀ x → bleh (bleh' x) ≡ x
      bb' (inl tt) = refl
      bb' (inr (n , p)) i =  inr (n , isProp≤ ( pred-≤-pred (suc-≤-suc p)) p i)
      b'b : ∀ x → bleh' (bleh x) ≡ x
      b'b (zero , p) i =  zero , isProp≤ (suc-≤-suc zero-≤) p i
      b'b (suc n , p) i =  suc n , isProp≤ (suc-≤-suc (pred-≤-pred p)) p i
  foo : (F : Pointed₀) → ⊤ ⊎ (typ F) ≡ S₊∙ 0 ⋁ F
  foo F = isoToPath (iso juan juan' jj' j'j)
    where
      juan : ⊤ ⊎ (typ F) → S₊∙ 0 ⋁ F
      juan (inl tt) = inl false
      juan (inr x) =  inr x
      juan' : S₊∙ 0 ⋁ F → ⊤ ⊎ (typ F)
      juan' (inl false) =  inl tt
      juan' (inl true) =  inr (pt F)
      juan' (inr x) =  inr x
      juan' (push tt i) =  refl {x = inr (pt F)} i
      jj' : ∀ x → juan (juan' x) ≡ x
      jj' (inl false) = refl
      jj' (inl true) =  sym (push tt)
      jj' (inr x) = refl
      jj' (push tt i) j =  push tt ( ~ j ∨ i)
      j'j : ∀ x → juan' (juan x) ≡ x
      j'j (inl tt) = refl
      j'j (inr x) = refl

  Fin≡⋁S0 : ∀ m → Fin (m + 2) ≡ typ (⋁ᵐ m (S₊∙ 0))
  Fin≡⋁S0 zero =  isoToPath (iso  guh  guh' gg' g'g)
    where
      guh : Fin 2 → S₊ 0
      guh (zero , p) =   false
      guh (suc m , p) =  true
      guh' : S₊ 0 → Fin 2
      guh' false =  zero ,  suc-≤-suc (zero-≤ {1}) 
      guh' true =  1 ,  ≤-refl  
      g'g : ∀ x → guh' (guh x) ≡ x
      g'g (0 , p) i = zero ,  isProp≤ (suc-≤-suc zero-≤) p i
      g'g (1 , p) i =  1 , isProp≤ ≤-refl p i 
      g'g (suc (suc n) , p) =  rec⊥ (¬m+n<m p) 
      gg' : ∀ x → guh (guh' x) ≡ x
      gg' false = refl
      gg' true = refl

  Fin≡⋁S0 (suc m) =  Fin (suc (m + 2))
    ≡⟨ FinSm≡⊤+Finm (m + 2) ⟩
    ⊤ ⊎ Fin (m + 2)
    ≡⟨ congS (λ x → ⊤ ⊎ x) (Fin≡⋁S0 m) ⟩
    ⊤ ⊎ typ (⋁ᵐ m (S₊∙ 0))
    ≡⟨  foo (⋁ᵐ m (S₊∙ 0)) ⟩
    S₊∙ 0 ⋁ ⋁ᵐ m (S₊∙ 0)
    ≡⟨ refl ⟩
    typ (⋁ᵐ (suc m) (S₊∙ 0)) ∎

  Lift-trivial : ∀ {ℓ} (G : Type ℓ) → G ≡ Lift {ℓ} {ℓ} G
  Lift-trivial {ℓ} G =  isoToPath (iso lift (λ (lift x) → x) (λ x → refl)  λ x → refl)
  -- cellular model for finite groups
  finite-G-spheres : ∀ n m  →  G ≡ Lift (Fin (m + 2)) → Lift {_} {ℓᵧ} (G *ⁿ  n) ≡ Lift (typ (⋁ᵐ (m ^ (suc n)) (S₊∙ n)))
  finite-G-spheres zero m GFinite = sym (
    Lift (typ (⋁ᵐ (m ^ 1) (S₊∙ 0)))
    ≡⟨ congS  (λ x → Lift (typ (⋁ᵐ x (S₊∙ 0 )))) ( ·-identityʳ m) ⟩
    Lift (typ (⋁ᵐ m (S₊∙ 0)))
    ≡⟨  congS (λ x → Lift x) (sym (Fin≡⋁S0 m))  ⟩
    Lift (Fin (m + 2))
    ≡⟨ sym GFinite ⟩
    G 
    ≡⟨ Lift-trivial G ⟩
    Lift G 
    ∎)
  finite-G-spheres (suc n) m GFinite =
    Lift (G *ⁿ suc n)
    ≡⟨ refl ⟩
    Lift (join G (G *ⁿ n))
    ≡⟨ {!!} ⟩
    {!!}
    ∎

  

  

  
    
  -- -- got a little stuck on how to best formalize the contents of 5.4...
  -- -- how to set up the definition of fiber sequence / the sequence of fiber sequences to lead to a doable convergence proof is not immediately clear
  -- -- this certainly doesn't seem right though...
  -- fiberSequence :  ∀ {ℓ} (F : Type ℓ) (E : Type ℓ) (B : Pointed ℓ)  (f : E → typ B) →  Type (ℓ-suc ℓ)
  -- fiberSequence {ℓ} F E B f  =  F × E × typ B × ∥ F ≡ Ker∙ B f ∥₁ 


  -- fiberSequence⁺ : ∀ {ℓ} {F : Type ℓ} {A : Type ℓ} {B : Pointed ℓ} {f : A → typ B} → fiberSequence F A B f  → (n : ℕ) → fiberSequence (F *ⁿ n) (imⁿ f n) B (f f*ⁿ n)
  --                       → fiberSequence (F *ⁿ suc n) (imⁿ f (suc n)) B (f f*ⁿ suc n)
  -- fiberSequence⁺ {F = F} {A = A} {B = B} {f = f} fS n fSn =  rec2∥∥ {P = fiberSequence (F *ⁿ suc n) (imⁿ f (suc n)) B (f f*ⁿ suc n)} {!!}  (weh n) (fS .snd .snd .snd) (fSn .snd .snd .snd)
  --     where
  --       weh : ∀ n → F ≡ Ker∙ B f → F *ⁿ n ≡ Ker∙ B (f f*ⁿ n) → fiberSequence (F *ⁿ suc n) (imⁿ f (suc n)) B (f f*ⁿ suc n) 
  --       weh zero fIsKer fnIsKer =  subst (λ x → fiberSequence x A B f) (sym (join⊥≡id F))  fS
  --       weh (suc n) fIsKer fnIsKer = {!!} -- ∣ join F (F *ⁿ n) ≡⟨ ? ⟩ ? ≡⟨ ? ⟩ Ker∙ B (f f*ⁿ suc n) ∎ ∣₁
  
  -- -- fiberSequence*Seq : ∀ {ℓ} (E : Type ℓ) (B : Pointed ℓ) (F : Type ℓ) (f : E → typ B) (p : F ≡ Ker∙ B f)  → Sequence (ℓ-suc ℓ)
  -- -- fiberSequence*Seq E B F f p = sequence (λ n → fiberSequence (F *ⁿ n) (imⁿ f n) B (f f*ⁿ n)) awawa 
  -- --   where
  -- --     guf : ∀ n → fiberSequence (F *ⁿ n) (imⁿ f n) B (f f*ⁿ n) →  join F (F *ⁿ n) ≡ Ker∙ B (f f*ⁿ suc n)
  -- --     guf n (F*n≡Ker , i , i≡fst) =  join F (F *ⁿ n) ≡⟨ {!!} ⟩ Ker∙ B (f f*ⁿ suc n) ∎
  -- --     awawa : ∀ {n : ℕ} →  fiberSequence (F *ⁿ n) (imⁿ f n) B (f f*ⁿ n) → fiberSequence (F *ⁿ (suc n)) (imⁿ f (suc n)) B (f f*ⁿ (suc n))
  -- --     awawa {n} fs@(F*n≡Ker , i , i≡fst) =  guf n fs , {!!} , {!!}
  -- -- --     guf zero (F*n≡Ker , i , i≡fst) =  join F ⊥* ≡⟨ join⊥≡id  F ⟩  F ≡⟨ p ⟩  Ker∙ B f ∎
  -- -- --     guf (suc n)(F*n≡Ker , i , i≡fst)  = {!!}
        

  



