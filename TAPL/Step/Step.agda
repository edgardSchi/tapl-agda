--------------------------------------------------------------------------------
--
-- Public module for the step relations
--
--------------------------------------------------------------------------------

module TAPL.Step.Step (Term : Set) (_⟶_ : Term → Term → Set) where

open import TAPL.Step.StepDefinition Term _⟶_ public
open import TAPL.Step.StepProperties Term _⟶_ public
open import TAPL.Step.StepReasoning Term _⟶_ public
