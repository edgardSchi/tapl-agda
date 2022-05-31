module TAPL.Chapter3.B-Language where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
import TAPL.Step.Step as Step

--------------------------------------------------------------------------------
--                                                                            
-- Language Definition                                                        
--                                                                            
--------------------------------------------------------------------------------

-- We define our simple language with these terms
data Term : Set where
  true          : Term
  false         : Term
  if_then_else_ : Term → Term → Term → Term

-- We only have two values
data Value : Term → Set where
  V-true  : Value true
  V-false : Value false

{-

Defining our evaluation rules:

       ------------------------------- [E-IFTRUE]
         if true then t₂ else t₃ ⟶ t₂

       ------------------------------- [E-IFFALSE]
         if false then t₂ else t₃ ⟶ t₃

                   t₁ ⟶ t₁'
------------------------------------------------- [E-IF]
if t₁ then t₂ else t₃ ⟶ if t₁' then t₂ else t₃

-}

data _⟶_ : Term → Term → Set where
 E-IF      : ∀ {t₁ t₁` t₂ t₃} → t₁ ⟶ t₁` → (if t₁ then t₂ else t₃) ⟶ (if t₁` then t₂ else t₃)
 E-IFTRUE  : ∀ {t₂ t₃} → (if true then t₂ else t₃) ⟶ t₂
 E-IFFALSE : ∀ {t₂ t₃} → (if false then t₂ else t₃) ⟶ t₃

-- Opening the step module with our defined evalutation rules
open Step Term (_⟶_) 

--------------------------------------------------------------------------------
--                                                                           
-- Single Step Proofs                                                         
--                                                                            
--------------------------------------------------------------------------------


-- Showing that the single step evaluation is deterministic
⟶-det : ∀ {t t' t''} → t ⟶ t' → t ⟶ t'' → t' ≡ t''
⟶-det E-IFTRUE                      E-IFTRUE      = refl
⟶-det E-IFFALSE                     E-IFFALSE     = refl
⟶-det (E-IF {t₂ = t₂} {t₃ = t₃} t⟶t') (E-IF t⟶t'') = cong (if_then t₂ else t₃) (⟶-det t⟶t' t⟶t'')

-- Showing that t ⟶ t can not be constructed
⟶¬-refl : ∀ t → ¬ (t ⟶ t)
⟶¬-refl true ()
⟶¬-refl false ()
⟶¬-refl (if t then t₁ else t₂) = λ{ (E-IF t⟶t) → ⟶¬-refl t t⟶t}

-- Showing the uniqueness of the single step evaluation
⟶-unique : ∀ {t u} → t ⟶ u → ¬ (u ⟶ t)
⟶-unique (E-IF a) = λ{ (E-IF x) → ⟶-unique a x}
⟶-unique E-IFTRUE ()
⟶-unique E-IFFALSE ()

-- Showing substitution of the single step evaluation
⟶-sub : ∀ {t u v} → t ⟶ u → u ≡ v → t ⟶ v
⟶-sub (E-IF t⟶u) refl = E-IF t⟶u
⟶-sub E-IFTRUE   refl = E-IFTRUE
⟶-sub E-IFFALSE  refl = E-IFFALSE

-- Defining the size of a term
size : Term → ℕ
size true = 1
size false = 1
size (if t then t₁ else t₂) = size t + size t₁ + size t₂

-- Showing that every value is also in normal form
value→⇥ : ∀ {t} → Value t → t ⇥
value→⇥ V-true ()
value→⇥ V-false ()

-- Showing that if_then_else can not be in normal form
if-not-⇥ : ∀ {t₁ t₂ t₃} → ¬ ((if t₁ then t₂ else t₃) ⇥)
if-not-⇥ {true} {t₂} {t₃} = λ z → z E-IFTRUE
if-not-⇥ {false} {t₂} {t₃} = λ z → z E-IFFALSE
if-not-⇥ {t₁ = if t then t₄ else t₅} {t₂} {t₃} with if-not-⇥ {t}
...| z = λ x → z (λ z → x (E-IF z)) 

-- Showing that every term in normal form is a value
⇥→value : ∀ {t} → t ⇥ → Value t
⇥→value {t = true} t⇥ = V-true
⇥→value {t = false} t⇥ = V-false
⇥→value {t = if t then t₁ else t₂} t⇥ = ⊥-elim (if-not-⇥ t⇥)

--------------------------------------------------------------------------------
--                                                                            
-- Multi Step Proofs                                                          
--                                                                            
--------------------------------------------------------------------------------

-- Showing that E-IF also holds for multi step
E-IF* : ∀ {t₁ t₁` t₂ t₃} → t₁ ↠ t₁` → (if t₁ then t₂ else t₃) ↠ (if t₁` then t₂ else t₃)
E-IF* (↠step x) = ↠step (E-IF x)
E-IF* ↠reflex = ↠reflex
E-IF* (↠trans a a₁) = _↠_.↠trans (E-IF* a) (E-IF* a₁)

-- Using the proof that ⟶ is determinant to show that ↠ is also determinant
↠-uniqueness : ∀ {t u u' : Term} → (u ⇥) → (u' ⇥) → t ↠ u → t ↠ u' → u ≡ u'
↠-uniqueness nfu nfu' t↠u t↠u' = ⟶-DeterminacyProofs.⇥-uniq ⟶-det nfu nfu' t↠u t↠u'

-- Showing that ↠ terminates
↠-termin : ∀ {t : Term} → ∃[ u ] (u ⇥ × t ↠ u)
↠-termin {true} = true , (λ ()) , ↠reflex
↠-termin {false} = false , (λ ()) , ↠reflex
↠-termin {if t then t₁ else t₂} with ↠-termin {t}
... | tu , tu⇥ , t↠u with ↠-termin {t₁}
... | t₁u , t₁u⇥ , t₁↠u with ↠-termin {t₂}
↠-termin {if t then t₁ else t₂} | true , tu⇥ , t↠u | t₁u , t₁u⇥ , t₁↠u | t₂u , t₂u⇥ , t₂↠u = t₁u , (t₁u⇥ ,
  (↠begin
     (if t then t₁ else t₂)
   ↠⟨ E-IF* t↠u ⟩
     (if true then t₁ else t₂)
   ↠⟨ ↠trans (↠step E-IFTRUE) t₁↠u ⟩
     t₁u
   ↠∎
  ))
↠-termin {if t then t₁ else t₂} | false , tu⇥ , t↠u | t₁u , t₁u⇥ , t₁↠u | t₂u , t₂u⇥ , t₂↠u = t₂u , (t₂u⇥ ,
  (↠begin 
    (if t then t₁ else t₂)
   ↠⟨ E-IF* t↠u ⟩
     (if false then t₁ else t₂)
   ↠⟨ ↠trans (↠step E-IFFALSE) t₂↠u ⟩
     t₂u
   ↠∎
  ))
↠-termin {if t then t₁ else t₂} | (if tu then tu₁ else tu₂) , tu⇥ , t↠u | t₁u , t₁u⇥ , t₁↠u | t₂u , t₂u⇥ , t₂↠u = ⊥-elim (if-not-⇥ tu⇥)
