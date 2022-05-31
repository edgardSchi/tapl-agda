module TAPL.Step.StepReasoning (Term : Set) (_⟶_ : Term → Term → Set) where
open import TAPL.Step.StepDefinition Term (_⟶_)

infix 1 ↠begin_
infix 2 _↠⟨_⟩_
infix 2 _⟶⟨_⟩_
infix 3 _↠∎

↠begin_ : ∀ {t u : Term} → t ↠ u → t ↠ u
↠begin t⟶u = t⟶u

_↠⟨_⟩_ : ∀ {t u v} → t ↠ u → u ↠ v → t ↠ v
_↠⟨_⟩_ t↠u u↠v = ↠trans t↠u u↠v

_⟶⟨_⟩_ : ∀ {t u v} → t ↠ u → u ⟶ v → t ↠ v
_⟶⟨_⟩_ t↠u u⟶v = ↠trans t↠u (↠step u⟶v)

_↠∎ : ∀ (t : Term) → t ↠ t
_↠∎ t = ↠reflex
