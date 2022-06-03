module TAPL.Chapter3.NB-Language where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
open import Function using (_∘_)
import TAPL.Step.Step as Step

--------------------------------------------------------------------------------
--                                                                            
-- Language Definition                                                        
--                                                                            
--------------------------------------------------------------------------------

-- We define our language with these terms
data Term : Set where
  true          : Term
  false         : Term
  if_then_else_ : Term → Term → Term → Term
  𝟘             : Term
  succ          : Term → Term
  pred          : Term → Term
  iszero        : Term → Term


-- This language now includes numerical values
data NumericValue : Term → Set where
  NV-𝟘    : NumericValue 𝟘
  NV-succ : ∀ {t} → NumericValue t → NumericValue (succ t)


-- We now have more values
data Value : Term → Set where
  V-true  : Value true
  V-false : Value false
  V-nv    : ∀ {nv} → NumericValue nv → Value nv

{-

Defining our evaluation rules:

------------------------------------------------- [E-IFTRUE]
          if true then t₂ else t₃ ⟶ t₂


------------------------------------------------- [E-IFFALSE]
          if false then t₂ else t₃ ⟶ t₃


                    t₁ ⟶ t₁'
------------------------------------------------- [E-IF]
  if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃


                    t₁ ⟶ t₁'
------------------------------------------------- [E-SUCC]
               succ t₁ ⟶ succ t₁'


------------------------------------------------- [E-PREDZERO]
                 pred 0 ⟶ 0
 

------------------------------------------------- [E-PREDSUCC]
             pred (succ nv₁) ⟶ nv₁



                    t₁ ⟶ t₁'
------------------------------------------------- [E-PRED]
               pred t₁ ⟶ pred t₁'



------------------------------------------------- [E-ISZEROZERO]
              iszero 0 ⟶ true



------------------------------------------------- [E-ISZEROZERO]
              iszero 0 ⟶ true



------------------------------------------------- [E-ISZEROSUCC]
          iszero (succ nv₁) ⟶ false



                    t₁ ⟶ t₁'
------------------------------------------------- [E-ISZERO]
               iszero t₁ ⟶ iszero t₁'


-}

data _⟶_ : Term → Term → Set where
 E-IF         : ∀ {t₁ t₁` t₂ t₃} → t₁ ⟶ t₁` → (if t₁ then t₂ else t₃) ⟶ (if t₁` then t₂ else t₃)
 E-IFTRUE     : ∀ {t₂ t₃} → (if true then t₂ else t₃) ⟶ t₂
 E-IFFALSE    : ∀ {t₂ t₃} → (if false then t₂ else t₃) ⟶ t₃
 E-SUCC       : ∀ {t t'} → t ⟶ t' → succ t ⟶ succ t'
 E-PREDZERO   : pred 𝟘 ⟶ 𝟘
 E-PREDSUCC   : ∀ {numv} → (NumericValue numv) → pred (succ numv) ⟶ numv
 E-PRED       : ∀ {t t'} → t ⟶ t' → pred t ⟶ pred t'
 E-ISZEROZERO : iszero 𝟘 ⟶ true
 E-ISZEROSUCC : ∀ {numv} → (NumericValue numv) → iszero (succ numv) ⟶ false
 E-ISZERO     : ∀ {t t'} → t ⟶ t' → iszero t ⟶ iszero t'

-- Opening the step module with our defined evalutation rules
open Step Term (_⟶_) 

--------------------------------------------------------------------------------
--                                                                           
-- Single Step Proofs                                                         
--                                                                            
--------------------------------------------------------------------------------

-- Defining a stuck term
Stuck : Term → Set
Stuck t = (t ⇥) × (¬ (Value t))

-- Showing that every numeric value is in normal form
nv-value→⇥ : ∀ {t} → NumericValue t → t ⇥
nv-value→⇥ NV-𝟘 ()
nv-value→⇥ (NV-succ a) = λ{ (E-SUCC x) → nv-value→⇥ a x}

-- Showing that every value is in normal form
value→⇥ : ∀ {t} → Value t → t ⇥
value→⇥ V-true ()
value→⇥ V-false ()
value→⇥ (V-nv x) = nv-value→⇥ x

-- Showing that the successor of a numeric value is again a numeric value
nv-succ→nv : ∀ {t} → NumericValue t → NumericValue (succ t)
nv-succ→nv nvt = NV-succ nvt

-- Theorem 3.5.14
-- Showing that ⟶ is deterministic
⟶-det : ∀ {t t' t''} → t ⟶ t' → t ⟶ t'' → t' ≡ t''
⟶-det (E-IF {t₂ = t₂} {t₃ = t₃} t⟶t') (E-IF t⟶t'') = cong (if_then t₂ else t₃) (⟶-det t⟶t' t⟶t'')
⟶-det E-IFTRUE E-IFTRUE = refl
⟶-det E-IFFALSE E-IFFALSE = refl
⟶-det (E-SUCC a) (E-SUCC b) rewrite ⟶-det a b = refl
⟶-det E-PREDZERO E-PREDZERO = refl
⟶-det (E-PREDSUCC x) (E-PREDSUCC x₁) = refl
⟶-det (E-PREDSUCC x) (E-PRED b) with (nv-value→⇥ ∘ nv-succ→nv) x
... | succ⇥ = ⊥-elim ( succ⇥ b)
⟶-det (E-PRED a) (E-PREDSUCC x) with (nv-value→⇥ ∘ nv-succ→nv) x
... | succ⇥ = ⊥-elim ( succ⇥ a)
⟶-det (E-PRED a) (E-PRED b) rewrite ⟶-det a b = refl
⟶-det E-ISZEROZERO E-ISZEROZERO = refl
⟶-det (E-ISZEROSUCC x) (E-ISZEROSUCC x₁) = refl
⟶-det (E-ISZEROSUCC {numv} x) (E-ISZERO b) with (nv-value→⇥ ∘ nv-succ→nv) x
... | succ⇥ = ⊥-elim ( succ⇥ b)
⟶-det (E-ISZERO a) (E-ISZEROSUCC x) with (nv-value→⇥ ∘ nv-succ→nv) x
... | succ⇥ = ⊥-elim ( succ⇥ a)
⟶-det (E-ISZERO a) (E-ISZERO b) rewrite ⟶-det a b = refl


--------------------------------------------------------------------------------
--                                                                           
-- Multi Step Proofs                                                         
--                                                                            
--------------------------------------------------------------------------------

-- Showing the uniqueness of multi step evaluation
↠-uniqueness : ∀ {t u u' : Term} → (u ⇥) → (u' ⇥) → t ↠ u → t ↠ u' → u ≡ u'
↠-uniqueness nfu nfu' t↠u t↠u' = ⟶-DeterminacyProofs.⇥-uniq ⟶-det nfu nfu' t↠u t↠u'

--------------------------------------------------------------------------------
--                                                                           
-- Big Step Proofs                                                         
--                                                                            
--------------------------------------------------------------------------------

data _⇓_ : Term → Term → Set where
  B-VALUE : ∀ {v} → (Value v) → v ⇓ v
  B-IFTRUE : ∀ {t₁ t₂ t₃ v₂} → t₁ ⇓ true → t₂ ⇓ v₂ → (if t₁ then t₂ else t₃) ⇓ v₂
  B-IFFALSE : ∀ {t₁ t₂ t₃ v₃} → t₁ ⇓ false → t₃ ⇓ v₃ → (if t₁ then t₂ else t₃) ⇓ v₃
  B-SUCC : ∀ {t nv} → NumericValue nv → t ⇓ nv → succ t ⇓ succ nv
  B-PREDZERO : ∀ {t} → t ⇓ 𝟘 → pred t ⇓ 𝟘
  B-PREDSUCC : ∀ {t nv} → NumericValue nv → t ⇓ succ nv → pred t ⇓ nv
  B-ISZEROZERO : ∀ {t} → t ⇓ 𝟘 → iszero t ⇓ true
  B-ISZEROSUCC : ∀ {t nv} → NumericValue nv → t ⇓ succ nv → iszero t ⇓ false


l2 : ∀ {t v} → t ⇓ v → Value v
l2 (B-VALUE x) = x
l2 (B-IFTRUE a a₁) = l2 a₁
l2 (B-IFFALSE a a₁) = l2 a₁
l2 (B-SUCC x a) = V-nv (NV-succ x)
l2 (B-PREDZERO a) = l2 a
l2 (B-PREDSUCC x a) = V-nv x
l2 (B-ISZEROZERO a) = V-true
l2 (B-ISZEROSUCC x a) = V-false

-- TODO: Show that ↠ ⇔ ⇓
{-
l1 : ∀ {t v} → Value v → t ⟶ v → t ⇓ v
l1 {t} V-true a = {!!}
l1 V-false a = {!!}
l1 (V-nv x) a = {!!}

l3 : ∀ {t t' v} → t ↠ t' → t' ⇓ v → t ⇓ v
l3 (↠step x) b = {!b!}
l3 ↠reflex b = {!!}
l3 (↠trans a a₁) b = {!!}

↠→⇓ : ∀ {t v} → Value v → t ↠ v → t ⇓ v
↠→⇓ v (↠step x) = {!!}
↠→⇓ v ↠reflex = B-VALUE v
↠→⇓ v (↠trans a a₁) with ↠→⇓ v a₁
... | p = {!!}
-}  
