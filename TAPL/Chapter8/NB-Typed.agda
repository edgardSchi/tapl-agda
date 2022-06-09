module TAPL.Chapter8.NB-Typed where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
import TAPL.Step.Step as Step


--------------------------------------------------------------------------------
--                                                                            
-- Language Definition                                                        
--                                                                            
--------------------------------------------------------------------------------

-- Terms and evaluation rules same as in TAPL.Chapter3.NB-Language
open import TAPL.Chapter3.NB-Language

-- Defining our new typing rules
data Type : Set where
  Bool : Type
  Nat  : Type

data _꞉_ : Term → Type → Set where
  T-TRUE   : true ꞉ Bool
  T-FALSE  : false ꞉ Bool
  T-IF     : ∀ {t₁ t₂ t₃} {T : Type} → t₁ ꞉ Bool → t₂ ꞉ T → t₃ ꞉ T → (if t₁ then t₂ else t₃) ꞉ T
  T-ZERO   : 𝟘 ꞉ Nat
  T-SUCC   : ∀ {t} → t ꞉ Nat → succ t ꞉ Nat
  T-PRED   : ∀ {t} → t ꞉ Nat → pred t ꞉ Nat
  T-ISZERO : ∀ {t} → t ꞉ Nat → iszero t ꞉ Bool

--------------------------------------------------------------------------------
--                                                                            
-- Proofs
--                                                                            
--------------------------------------------------------------------------------

꞉-elim : ∀ {t} {T} → t ꞉ T → Term
꞉-elim {t} t꞉T = t

nv-elim : ∀ {t} → NumericValue t → Term
nv-elim {t} _ = t

-- Showing that every numeric value has type Nat
nv→Nat : ∀ {t} → NumericValue t → t ꞉ Nat
nv→Nat NV-𝟘 = T-ZERO
nv→Nat (NV-succ nvt) = T-SUCC (nv→Nat nvt)


-- Lemma 8.2.2
-- Inversion of the typing relation
itr1 : ∀ {R : Type} → true ꞉ R → R ≡ Bool
itr1 T-TRUE = refl

itr2 : ∀ {R : Type} → false ꞉ R → R ≡ Bool
itr2 T-FALSE = refl

itr3 : ∀ {t₁ t₂ t₃} {R : Type} → (if t₁ then t₂ else t₃) ꞉ R → (t₁ ꞉ Bool) × (t₂ ꞉ R) × (t₃ ꞉ R)
itr3 (T-IF t₁ t₂ t₃) = t₁ , t₂ , t₃

itr4 : ∀ {R : Type} → 𝟘 ꞉ R → R ≡ Nat
itr4 T-ZERO = refl

itr5 : ∀ {t} {R : Type} → succ t ꞉ R → (R ≡ Nat) × (t ꞉ Nat)
itr5 (T-SUCC t') = refl , t'

itr6 : ∀ {t} {R : Type} → pred t ꞉ R → (R ≡ Nat) × (t ꞉ Nat)
itr6 (T-PRED t') = refl , t'

itr7 : ∀ {t} {R : Type} → iszero t ꞉ R → (R ≡ Bool) × (t ꞉ Nat)
itr7 (T-ISZERO t') = refl , t'


-- Theorem 8.2.4
-- Uniqueness of types
꞉-uniq : ∀ {t} {T R} → t ꞉ T → t ꞉ R → T ≡ R
꞉-uniq T-TRUE         T-TRUE         = refl
꞉-uniq T-FALSE        T-FALSE        = refl
꞉-uniq (T-IF u₁ u₂ u₃) (T-IF v₁ v₂ v₃) = ꞉-uniq u₂ v₂ -- ꞉-uniq u₃ v₃ also works because they must have the same type
꞉-uniq T-ZERO         T-ZERO         = refl
꞉-uniq (T-SUCC u)     (T-SUCC v)     = refl
꞉-uniq (T-PRED u)     (T-PRED v)     = refl
꞉-uniq (T-ISZERO u)   (T-ISZERO v)   = refl


-- Lemma 8.3.1
-- Canonical Forms
can-form-bool : ∀ {v} → Value v → v ꞉ Bool → (v ≡ true) ⊎ (v ≡ false)
can-form-bool V-true   v꞉Bool = inj₁ refl
can-form-bool V-false  v꞉Bool = inj₂ refl
can-form-bool (V-nv u) v꞉Bool with ꞉-uniq (nv→Nat u) v꞉Bool
... | ()

can-form-nat : ∀ {v} → Value v → v ꞉ Nat → NumericValue v
can-form-nat (V-nv u) v꞉Nat = u


-- Theorem 8.3.2
-- Progess
progress : ∀ {t} {T} → t ꞉ T → (Value t) ⊎ (∃[ t' ] t ⟶ t')
progress T-TRUE              = inj₁ V-true
progress T-FALSE             = inj₁ V-false
progress (T-IF t t₁ t₂) with progress t
... | inj₁ V-true             = inj₂ ((꞉-elim t₁) , E-IFTRUE)
... | inj₁ V-false            = inj₂ ((꞉-elim t₂) , E-IFFALSE)
... | inj₂ (fst , snd)        = inj₂ ((if fst then (꞉-elim t₁) else (꞉-elim t₂)) , E-IF snd)
... | inj₁ (V-nv v) with ꞉-uniq (nv→Nat v) t
... | ()
progress T-ZERO = inj₁ (V-nv NV-𝟘)
progress (T-SUCC t) with progress t
... | inj₁ (V-nv v)           = inj₁ (V-nv (NV-succ v))
... | inj₂ (fst , snd)        = inj₂ (succ fst , E-SUCC snd)
progress (T-PRED t) with progress t
... | inj₁ (V-nv NV-𝟘)        = inj₂ (𝟘 , E-PREDZERO)
... | inj₁ (V-nv (NV-succ v)) = inj₂ ((nv-elim v) , E-PREDSUCC v)
... | inj₂ (fst , snd)        = inj₂ (pred fst , E-PRED snd)
progress (T-ISZERO t) with progress t
... | inj₁ (V-nv NV-𝟘)        = inj₂ (true , E-ISZEROZERO)
... | inj₁ (V-nv (NV-succ v)) = inj₂ (false , E-ISZEROSUCC v)
... | inj₂ (fst , snd)        = inj₂ (iszero fst , E-ISZERO snd)


-- Theorem 8.3.3
-- Preservation
preservation : ∀ {t t'} {T} → t ꞉ T → t ⟶ t' → t' ꞉ T
preservation T-TRUE ()
preservation T-FALSE ()
preservation (T-IF t₁ t₂ t₃) (E-IF u) with preservation t₁ u
... | t₁'꞉T = T-IF t₁'꞉T t₂ t₃
preservation (T-IF t₁ t₂ t₃) E-IFTRUE         = t₂
preservation (T-IF t₁ t₂ t₃) E-IFFALSE        = t₃
preservation T-ZERO ()
preservation (T-SUCC u)     (E-SUCC v)       = T-SUCC (preservation u v)
preservation (T-PRED u)     E-PREDZERO       = u
preservation (T-PRED u)     (E-PREDSUCC v)   = nv→Nat v
preservation (T-PRED u)     (E-PRED v)       = T-PRED (preservation u v)
preservation (T-ISZERO u)   E-ISZEROZERO     = T-TRUE
preservation (T-ISZERO u)   (E-ISZEROSUCC v) = T-FALSE
preservation (T-ISZERO u)   (E-ISZERO v)     = T-ISZERO (preservation u v)
