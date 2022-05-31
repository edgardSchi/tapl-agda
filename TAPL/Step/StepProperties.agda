--------------------------------------------------------------------------------
--
-- Properties of the multi step evaluation
--
--------------------------------------------------------------------------------

module TAPL.Step.StepProperties (Term : Set) (_⟶_ : Term → Term → Set) where

open import TAPL.Step.StepDefinition Term _⟶_

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

--------------------------------------------------------------------------------
-- General properties

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

--------------------------------------------------------------------------------
-- Properties requiring that _⟶_ is deterministic

module ⟶-DeterminacyProofs (⟶-det : ∀ {t t' t''} → t ⟶ t' → t ⟶ t'' → t' ≡ t'') where

  -- Showing that if t ⟶ u and t ↠ u' hold and u is in normal form then either u ≡ u' or u' ≡ t must hold 
  ⟶↠-det : ∀ {t u u' : Term} → (u ⇥) → t ⟶ u → t ↠ u' → u ≡ u' ⊎ u' ≡ t
  ⟶↠-det nfu t⟶u (↠step t⟶u') = inj₁ (⟶-det t⟶u t⟶u')
  ⟶↠-det nfu t⟶u ↠reflex      = inj₂ refl
  ⟶↠-det nfu t⟶u (↠trans t↠t' t'↠u') with ⟶↠-det nfu t⟶u t↠t'
  ...| inj₁ refl rewrite sym (⇥↠ nfu t'↠u') = ⟶↠-det nfu t⟶u t↠t'
  ...| inj₂ refl = ⟶↠-det nfu t⟶u t'↠u'

  -- Showing that if t ⟶ u and t ↠ v hold, then either u ↠ v or v ≡ t must hold
  ⟶↠-diff : ∀ {t u v} → t ⟶ u → t ↠ v → u ↠ v ⊎ v ≡ t 
  ⟶↠-diff t⟶u (↠step t⟶v) rewrite ⟶-det t⟶v t⟶u = inj₁ ↠reflex
  ⟶↠-diff t⟶u ↠reflex = inj₂ refl 
  ⟶↠-diff t⟶u (↠trans t↠t' t'↠v) with ⟶↠-diff t⟶u t↠t'
  ...| inj₁ u↠t' = inj₁ (↠trans u↠t' t'↠v)
  ...| inj₂ refl = ⟶↠-diff t⟶u t'↠v

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
  ⇥-uniq : ∀ {t u u' : Term} → (u ⇥) → (u' ⇥) → t ↠ u → t ↠ u' → u ≡ u'
  ⇥-uniq nfu nfu' ↠reflex              ↠reflex                = refl
  ⇥-uniq _   _    (↠step t⟶u)         (↠step t⟶u')            = ⟶-det t⟶u t⟶u'
  ⇥-uniq nfu nft  (↠step t⟶u)          ↠reflex                = ⊥-elim (nft t⟶u)
  ⇥-uniq nfu nfu'  ↠reflex            (↠step t⟶u')            = ⊥-elim (nfu t⟶u')
  ⇥-uniq nfu nfu' (↠step t⟶u)         (↠trans t↠t' t'↠u') with ⟶↠-det nfu t⟶u (↠trans t↠t' t'↠u')
  ...| inj₁ refl = refl
  ...| inj₂ refl = ⊥-elim (nfu' t⟶u)
  ⇥-uniq nfu nfu' (↠trans t↠t' t'↠u') (↠step t⟶u')        with ⟶↠-det nfu' t⟶u' (↠trans t↠t' t'↠u')
  ...| inj₁ refl = refl
  ...| inj₂ refl = ⊥-elim (nfu t⟶u')
  ⇥-uniq nft nfu'  ↠reflex            (↠trans t↠t' t'↠u') with ⇥↠ nft t↠t'
  ...| refl = ⇥↠ nft t'↠u'
  ⇥-uniq nfu nft  (↠trans t↠t' t'↠u)   ↠reflex            with ⇥↠ nft t↠t'
  ...| refl = sym (⇥↠ nft t'↠u)
  ⇥-uniq nfu nfu' (↠trans t↠t' t'↠u)  (↠trans t↠t'' t''↠u')  with ↠-conn t↠t' t↠t''
  ... | inj₁ t'↠t'' = ⇥-uniq nfu nfu' t'↠u (↠trans t'↠t'' t''↠u')
  ... | inj₂ t'↠t'' with ↠-conn t'↠t'' t''↠u'
  ... | inj₁ t'↠u' = ⇥-uniq nfu nfu' t'↠u t'↠u'
  ... | inj₂ u'↠t' with ⇥↠ nfu' u'↠t'
  ... | refl rewrite ⇥↠ nfu' t'↠u = refl

open ⟶-DeterminacyProofs public
