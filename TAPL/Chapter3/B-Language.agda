module TAPL.Chapter3.B-Language where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
import TAPL.Step.Step as Step
import TAPL.Step.StepReasoning

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
open TAPL.Step.StepReasoning Term (_⟶_)


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


-- Concatination of a multi and a single step evaluation
_↠+⟶_ : ∀ {t u v} → t ↠ u → u ⟶ v → t ↠ v
_↠+⟶_ (↠step t⟶u)        u⟶v = ↠trans (↠step t⟶u) (↠step u⟶v)
_↠+⟶_ ↠reflex            u⟶v = ↠step u⟶v
_↠+⟶_ (↠trans t↠t' t'↠u) u⟶v = ↠trans t↠t' (_↠+⟶_ t'↠u u⟶v)

-- Showing that only reflexivity is possible, if t ↠ u holds and t is in normal form
⇥↠ : ∀ {t u} → (t ⇥) → t ↠ u → t ≡ u
⇥↠ nft (↠step t⟶u) = ⊥-elim (nft t⟶u)
⇥↠ nft ↠reflex     = refl
⇥↠ nft (↠trans t↠t' t'↠u) with ⇥↠ nft t↠t'
...| refl = ⇥↠ nft t'↠u

-- Showing that if t ⟶ u and t ↠ u' hold and u is in normal form then either u ≡ u' or u' ≡ t must hold 
x : ∀ {t u u' : Term} → (u ⇥) → t ⟶ u → t ↠ u' → u ≡ u' ⊎ u' ≡ t
x nfu t⟶u (↠step t⟶u') = inj₁ (⟶-det t⟶u t⟶u')
x nfu t⟶u ↠reflex      = inj₂ refl
x nfu t⟶u (↠trans t↠t' t'↠u') with x nfu t⟶u t↠t'
...| inj₁ refl rewrite sym (⇥↠ nfu t'↠u') = x nfu t⟶u t↠t'
...| inj₂ refl = x nfu t⟶u t'↠u'


-- Showing that if t ⟶ u and t ↠ v hold, then either u ↠ v or v ≡ t must hold
⟶↠-diff : ∀ {t u v} → t ⟶ u → t ↠ v → u ↠ v ⊎ v ≡ t 
⟶↠-diff a (↠step x₁) rewrite ⟶-det x₁ a = inj₁ ↠reflex
⟶↠-diff a ↠reflex = inj₂ refl 
⟶↠-diff a (↠trans b b₁) with ⟶↠-diff a b
...| inj₁ x₁ = inj₁ (↠trans x₁ b₁)
...| inj₂ refl = ⟶↠-diff a b₁

-- Showing that if t ↠ t' and t ↠ t'' hold, then either t' ↠ t'' or t'' ↠ t' must hold
↠-conn : ∀ {t t' t''} → t ↠ t' → t ↠ t'' → t' ↠ t'' ⊎ t'' ↠ t'
↠-conn t↠t' (↠step t⟶t'') with ⟶↠-diff t⟶t'' t↠t'
...| inj₁ t''↠t' = inj₂ t''↠t'
...| inj₂ refl   = inj₁ (↠step t⟶t'')
↠-conn t↠t' ↠reflex = inj₂ t↠t'
↠-conn t↠t' (↠trans t↠t''' t'''↠t') with ↠-conn t↠t' t↠t'''
...| inj₁ r₁ = inj₁ (↠trans r₁ t'''↠t')
...| inj₂ r₂ = ↠-conn r₂ t'''↠t'

-- Showing that the multi step reduction is deterministic
↠-det : ∀ {t u u' : Term} → (u ⇥) → (u' ⇥) → t ↠ u → t ↠ u' → u ≡ u'
↠-det nfu nfu' ↠reflex              ↠reflex                = refl
↠-det _   _    (↠step t⟶u)         (↠step t⟶u')            = ⟶-det t⟶u t⟶u'
↠-det nfu nft  (↠step t⟶u)          ↠reflex                = ⊥-elim (nft t⟶u)
↠-det nfu nfu'  ↠reflex            (↠step x)               = ⊥-elim (nfu x)
↠-det nfu nfu' (↠step t⟶u)         (↠trans t↠t' t'↠u') with x nfu t⟶u (↠trans t↠t' t'↠u')
...| inj₁ refl = refl
...| inj₂ refl = ⊥-elim (nfu' t⟶u)
↠-det nfu nfu' (↠trans t↠t' t'↠u') (↠step t⟶u')        with x nfu' t⟶u' (↠trans t↠t' t'↠u')
...| inj₁ refl = refl
...| inj₂ refl = ⊥-elim (nfu t⟶u')
↠-det nft nfu'  ↠reflex            (↠trans t↠t' t'↠u') with ⇥↠ nft t↠t'
...| refl = ⇥↠ nft t'↠u'
↠-det nfu nft  (↠trans t↠t' t'↠u)   ↠reflex            with ⇥↠ nft t↠t'
...| refl = sym (⇥↠ nft t'↠u)
↠-det nfu nfu' (↠trans t↠t' t'↠u)  (↠trans t↠t'' t''↠u')  with ↠-conn t↠t' t↠t''
... | inj₁ t'↠t'' = ↠-det nfu nfu' t'↠u (↠trans t'↠t'' t''↠u')
... | inj₂ t'↠t'' with ↠-conn t'↠t'' t''↠u'
... | inj₁ t'↠u' = ↠-det nfu nfu' t'↠u t'↠u'
... | inj₂ u'↠t' with ⇥↠ nfu' u'↠t'
... | refl rewrite ⇥↠ nfu' t'↠u = refl

