{-# OPTIONS  --cubical #-}

module Cubical.HITs.Join.Horn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

data Horn : Type where
  Ha Hb Hc Hd : Horn
  Hp : Hb ≡ Ha
  Hq : Hb ≡ Hc
  Hr : Hc ≡ Hd

data Sqr : Type where
  Sa Sb Sc Sd : Sqr
  Sp : Sb ≡ Sa
  Sq : Sb ≡ Sc
  Sr : Sc ≡ Sd
  St : Sa ≡ Sd
  Sf : Square Sp Sr Sq St

data Tri : Type where
  Ta Tb Tc : Tri
  Tp : Tb ≡ Ta
  Tq : Tb ≡ Tc
  Tr : Tc ≡ Ta
  Tf : Square Tp Tr Tq refl
Tri-elim : ∀ {ℓ} (P : Tri → Type ℓ)
  (Pa : P Ta) (Pb : P Tb) (Pc : P Tc) 
  (Pp : PathP (λ i → P (Tp i)) Pb Pa)
  (Pq : PathP (λ i → P (Tq i)) Pb Pc)
  (Pr : PathP (λ i → P (Tr i)) Pc Pa)
  (Pf : SquareP (λ i j → P (Tf i j)) Pp Pr Pq refl) →
  (x : Tri) → P x
Tri-elim P pa pb pc pp pq pr pf Ta =  pa
Tri-elim P pa pb pc pp pq pr pf Tb =  pb
Tri-elim P pa pb pc pp pq pr pf Tc =  pc
Tri-elim P pa pb pc pp pq pr pf (Tp i) =  pp i
Tri-elim P pa pb pc pp pq pr pf (Tq i) =  pq i
Tri-elim P pa pb pc pp pq pr pf (Tr i) =  pr i
Tri-elim P pa pb pc pp pq pr pf (Tf i j) =  pf i j


prefl : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) → Square p refl p refl
prefl p i j =  p (i ∨ j)

foo' :  Square   Sq  refl   Sq  refl
foo' i j =  prefl Sq i j

weh :  Square Sp  ( Sr ∙ sym St)  Sq  refl
weh j i = 
  hcomp
   ( λ k → λ
            { (i = i0) →  Sq (j ∨ ~ k)
            ; (i = i1) →  St (~ k)
            ; (j = i0) →  Sf (~ k) i 
           })
   ( Sr i)
tts : Tri → Sqr
tts = Tri-elim (λ _ → Sqr)
 Sa
 Sb
 Sc
 Sp
 Sq
 (Sr ∙ sym St)
 weh

stt : Sqr → Tri
stt Sa =  Ta
stt Sb =  Tb
stt Sc =  Tc
stt Sd = Ta
stt (Sp i) =  Tp i
stt (Sq i) = Tq i
stt (Sr i) = Tr i
stt (St i) =  Ta
stt (Sf i j) =  Tf i j  


weh' : Square  refl  St ( Sr ∙ sym St)  Sr
weh' j k = 
    hcomp ( λ i → 
       λ { (j = i0) →  Sq i
         ; (j = i1) →  St (i ∧ k)
         ; (k = i0) →  weh i j
         ; (k = i1) →  Sf i j
         }
     )
     (Sp j)
SqrtTri : ∀ x → tts (stt x) ≡ x
SqrtTri Sa = refl
SqrtTri Sb = refl 
SqrtTri Sc = refl
SqrtTri Sd =  St
SqrtTri (Sp i) =  refl
SqrtTri (Sq i) =  refl
SqrtTri (Sr j) k =  weh' j k

SqrtTri (St i) j =  St ( i ∧  j)
SqrtTri (Sf i j)  k =
    hfill ( λ i → 
       λ { (j = i0) →  Sq i
         ; (j = i1) →  St (i ∧ k)
         ; (k = i0) →  weh i j
         ; (k = i1) →  Sf i j
         }
     )
     (inS (Sp j)) i

weg : ∀ x → stt (tts x) ≡ x
weg Ta =  refl
weg Tb =  refl
weg Tc =  refl
weg (Tp i) =  refl
weg (Tq i) =  refl
weg (Tr j) k =
  hcomp (λ i →  λ { (j = i0) →  Tq i
                   ; (j = i1) →  Ta
                   ; (k = i0) →  stt (weh i j)  
                   ; (k = i1) →  Tf i j
                   } ) ( Tp j)
weg (Tf i j) k = 
  hfill (λ i →  λ { (j = i0) →  Tq i
                   ; (j = i1) →  Ta
                   ; (k = i0) →  stt (weh i j)  
                   ; (k = i1) →  Tf i j
                   } )
                   (inS (Tp j)) i

 
Sqr-elim : ∀ {ℓ} (P : Sqr → Type ℓ)
  (Pa : P Sa) (Pb : P Sb) (Pc : P Sc) (Pd : P Sd)
  (Pp : PathP (λ i → P (Sp i)) Pb Pa)
  (Pq : PathP (λ i → P (Sq i)) Pb Pc)
  (Pr : PathP (λ i → P (Sr i)) Pc Pd)
  (Pt : PathP (λ i → P (St i)) Pa Pd)
  (Pf : SquareP (λ i j → P (Sf i j)) Pp Pr Pq Pt) →
  (x : Sqr) → P x
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf Sa = Pa
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf Sb = Pb
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf Sc = Pc
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf Sd = Pd
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf (Sp i) = Pp i
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf (Sq i) = Pq i
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf (Sr i) = Pr i
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf (St i) = Pt i
Sqr-elim P Pa Pb Pc Pd Pp Pq Pr Pt Pf (Sf i j) = Pf i j

-- -- roughly Square≃doubleComp
-- toSquare : {ℓ : Level} {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} → (sym a₋₀ ∙∙ a₀₋ ∙∙ a₋₁ ≡ a₁₋) → Square a₀₋ a₁₋ a₋₀ a₋₁
-- toSquare eq = {! flipSquare (compPathL→PathP eq)!}

-- TODO: find a better proof?
fromSquare : {ℓ : Level} {A : Type ℓ} {a₀₀ a₀₁ a₁₀ a₁₁ : A} {a₀₋ : a₀₀ ≡ a₀₁} {a₁₋ : a₁₀ ≡ a₁₁} {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} → Square a₋₀ a₋₁ a₀₋ a₁₋ → (sym a₋₀ ∙∙ a₀₋ ∙∙ a₋₁ ≡ a₁₋)
fromSquare s = equivFun (Square≃doubleComp _ _ _ _) (flipSquare s)

globe-to-square : {ℓ : Level} {A : Type ℓ} {x y : A} {p q : x ≡ y} → (p ≡ q) → Square refl refl p q
globe-to-square α i j = α j i


-- refl∙∙refl : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → refl ∙∙ p ∙∙ refl ≡ p
-- refl∙∙refl = {!!}

-- TODO: this is cong-∙∙
-- cong-hcomp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) → cong f (p ∙∙ q ∙∙ r) ≡ (cong f p ∙∙ cong f q ∙∙ cong f r)
-- cong-hcomp f p q r = J2 (λ a p' d r → cong f (sym p' ∙∙ q ∙∙ r) ≡ (cong f (sym p') ∙∙ cong f q ∙∙ cong f r)) (cong (cong f) (refl∙∙refl q) ∙ sym (refl∙∙refl (cong f q))) (sym p) r

-- cong-hcomp' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {a b c d : A} (p : b ≡ a) (q : b ≡ c) (r : c ≡ d) →
  -- Square (cong f p) (cong f r) (cong f q) (cong f (sym p ∙∙ q ∙∙ r))
-- cong-hcomp' f p q r = {!!}

thm : Iso Horn Sqr
thm = iso f g f-g g-f
  where
  f : Horn → Sqr
  f Ha = Sa
  f Hb = Sb
  f Hc = Sc
  f Hd = Sd
  f (Hp i) = Sp i
  f (Hq i) = Sq i
  f (Hr i) = Sr i

  g : Sqr → Horn
  g Sa = Ha
  g Sb = Hb
  g Sc = Hc
  g Sd = Hd
  g (Sp i) = Hp i
  g (Sq i) = Hq i
  g (Sr i) = Hr i
  g (St i) = (sym Hp ∙∙ Hq ∙∙ Hr) i
  g (Sf i j) = doubleCompPath-filler (sym Hp) Hq Hr j i

  g-f : (x : Horn) → g (f x) ≡ x
  g-f Ha = refl
  g-f Hb = refl
  g-f Hc = refl
  g-f Hd = refl
  g-f (Hp i) = refl
  g-f (Hq i) = refl
  g-f (Hr i) = refl

  -- f-g : (x : Sqr) → f (g x) ≡ x
  -- f-g Sa = refl
  -- f-g Sb = refl
  -- f-g Sc = refl
  -- f-g Sd = refl
  -- f-g (Sp i) = refl
  -- f-g (Sq i) = refl
  -- f-g (Sr i) = refl
  -- f-g (St i) = lem i
    -- where
    -- lem : Square (refl {x = Sa}) (refl {x = Sd}) (cong f (sym Hp ∙∙ Hq ∙∙ Hr)) St
    -- lem = globe-to-square (cong-hcomp f (sym Hp) Hq Hr ∙ fromSquare Sf)
  -- f-g (Sf i j) = {!lem i j!}
    -- where
    -- lem' : {!!}
    -- lem' = {!!}
    -- lem : Cube (λ j k → Sp j) (λ j k → Sr j) (λ i k → Sq i) (λ i k → (cong-hcomp f (sym Hp) Hq Hr ∙ fromSquare Sf) i i) {!!} {!!} -- (λ i j → f (doubleCompPath-filler (sym Hp) Hq Hr j i)) (λ i j → Sf i j)
    -- lem = {!!}

-- Goal: comp
      -- (λ i₁ .o →
         -- f
         -- ((λ { ((i ∨ ~ i) = i1)
                 -- → doubleComp-faces (λ i₂ → Hp (~ i₂)) Hr i (j ∧ i₁) _
             -- ; (j = i0) → outS (inS (Hq i))
             -- })
          -- _))
      -- (Sq i)
      -- ≡ Sf i j
-- ———— Boundary (wanted) —————————————————————————————————————
-- i = i0 ⊢ λ i₁ → Sp j
-- i = i1 ⊢ λ i₁ → Sr j
-- j = i0 ⊢ λ i₁ → Sq i
-- j = i1 ⊢ Horn.lem i i

  f-g : (x : Sqr) → f (g x) ≡ x
  f-g = Sqr-elim (λ x → f (g x) ≡ x)
    refl
    refl
    refl
    refl
    (λ i → refl)
    (λ i → refl)
    (λ i → refl)
    -- lem1
    -- lem2
    -- where
    -- lem1 : Square (refl {x = Sa}) (refl {x = Sd}) (cong f (sym Hp ∙∙ Hq ∙∙ Hr)) St
    -- lem1 = globe-to-square (cong-∙∙ f (sym Hp) Hq Hr ∙ fromSquare Sf)
    -- -- lem1 = {!!}
    -- lem2 : SquareP (λ i j → f (doubleCompPath-filler (sym Hp) Hq Hr j i) ≡ Sf i j) (λ j k → Sp j) (λ j k → Sr j) (λ i k → Sq i) lem1
    -- lem2 = {!!}
    top
    (λ i j k → inside j i k)
    where
    -- top : cong f (sym Hp ∙∙ Hq ∙∙ Hr) ≡ St
    -- top k i =
      -- hfill
        -- (λ k →
          -- {!λ { (i = i0) → ? }!})
        -- {!!}
        -- k
    top : Square refl refl (cong f (sym Hp ∙∙ Hq ∙∙ Hr)) St
    top i k =
      hcomp
        (λ { j (i = i0) → Sp j
           ; j (i = i1) → Sr j
           ; j (k = i0) → f (doubleCompPath-filler (sym Hp) Hq Hr j i)
           ; j (k = i1) → Sf i j
           })
        (Sq i)
    inside : PathP (λ j → Square (λ k → Sp j) (λ k → Sr j) (λ i → {!!}) {!!}) (λ i k → Sq i) (λ i k → top i k)
    inside j i k =
      hfill
        (λ { j (i = i0) → Sp j
           ; j (i = i1) → Sr j
           ; j (k = i0) → f (doubleCompPath-filler (sym Hp) Hq Hr j i)
           ; j (k = i1) → Sf i j
           })
        (inS (Sq i))
        j

-- SquareP
      -- (λ i j →
         -- comp
         -- (λ i₁ .o →
            -- f
            -- ((λ { ((i ∨ ~ i) = i1)
                    -- → doubleComp-faces (λ i₂ → Hp (~ i₂)) Hr i (j ∧ i₁) _
                -- ; (j = i0) → outS (inS (Hq i))
                -- })
             -- _))
         -- (Sq i)
         -- ≡ Sf i j)
      -- (λ i _ → Sp i) (λ i _ → Sr i) (λ i _ → Sq i) lem1
