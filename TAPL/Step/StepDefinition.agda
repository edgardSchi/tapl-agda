--------------------------------------------------------------------------------
--
-- Definitions of step evaluation
--
--------------------------------------------------------------------------------

module TAPL.Step.StepDefinition (Term : Set) (_⟶_ : Term → Term → Set) where

open import Relation.Nullary using (¬_)

-- single step: → \-->
-- normal form: ⇥
-- multi step:  ↠ \rr-

-- We define a term t as being in normal form, if no u exists such that t ⟶ u 
_⇥ : Term → Set
t ⇥ = ∀ {u} → ¬ (t ⟶ u)

-- Defining the multi-step evaluation as the reflexive, transitive closure of ⟶
data _↠_ : Term → Term → Set where
  ↠step   : ∀ {t t'}     → t ⟶ t' → t ↠ t'
  ↠reflex : ∀ {t}        → t ↠ t
  ↠trans  : ∀ {t t' t''} → t ↠ t' → t' ↠ t'' → t ↠ t''

