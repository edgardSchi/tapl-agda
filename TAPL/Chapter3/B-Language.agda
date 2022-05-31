module TAPL.Chapter3.B-Language where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
import TAPL.Step.Step as Step

--------------------------------------------------------------------------------
--                                                                            --
-- Language Definition                                                        --
--                                                                            --
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
--                                                                            --
-- Single Step Proofs                                                         --
--                                                                            --
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


--------------------------------------------------------------------------------
--                                                                            --
-- Multi Step Proofs                                                          --
--                                                                            --
--------------------------------------------------------------------------------

-- Using the proof that ⟶ is determinant to show that ↠ is also determinant
↠-uniqueness : ∀ {t u u' : Term} → (u ⇥) → (u' ⇥) → t ↠ u → t ↠ u' → u ≡ u'
↠-uniqueness nfu nfu' t↠u t↠u' = ⟶-DeterminacyProofs.⇥-uniq ⟶-det nfu nfu' t↠u t↠u'
