module TAPL.Chapter9.Simply-Typed-Lambda where

open import Data.String using (String; _≈?_; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Product
open import Data.Sum

-- Identifiers are just strings
Id : Set
Id = String
infixr 7 _⇒_

data Type : Set where
  _⇒_     : Type → Type → Type
  Boolean : Type

-- We define our language with these terms
data Term : Set where
  true : Term
  false : Term
  if_then_else_ : Term → Term → Term → Term
  `_   : Id → Term
  ƛ_∶_⇒_ : Id → Type → Term → Term
  _·_  : Term → Term → Term

--------------------------------------------------------------------------------
--                                                                            
-- Helper Functions
--                                                                            
--------------------------------------------------------------------------------


module Helper-Functions where
  open import Data.Bool using (if_then_else_; Bool; true; false)
  open import Data.List hiding (deduplicate)
  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Nullary.Decidable using (⌊_⌋)

  private
    _∈?ᵇ_ : (e : Id) → (set : List Id) → Bool
    e ∈?ᵇ [] = false
    e ∈?ᵇ (x ∷ set) with e ≈? x
    ... | yes _ = true
    ... | no  _ = e ∈?ᵇ set
  
    remove : List Id → Id → List Id
    remove [] id = []
    remove (x ∷ xs) id = Data.Bool.if ⌊ x ≈? id ⌋ then xs else (remove xs id)
  
    deduplicate : List Id → List Id
    deduplicate [] = []
    deduplicate (x ∷ xs) with x ∈?ᵇ xs
    ... | false = x ∷ deduplicate xs
    ... | true = deduplicate xs

  -- Defining free variables in a term
  FV : Term → List Id
  FV (` x) = [ x ]
  FV (true) = []
  FV (false) = []
  FV (ƛ x ∶ T ⇒ t) = remove (FV t) x
  FV (t₁ · t₂) = deduplicate ((FV t₁) ++ (FV t₂))
  FV (if t₁ then t₂ else t₃) = deduplicate ((FV t₁) ++ (FV t₂) ++ (FV t₃))
  
  -- Defining subsitution
  [_↦_]_ : Id → Term → Term → Term
  [ x ↦ s ] (` y) with x ≈? y
  ... | yes _ = s
  ... | no  _ = ` y
  [ x ↦ s ] (true) = true
  [ x ↦ s ] (false) = false
  [ x ↦ s ] (ƛ y ∶ T ⇒ t) with x ≈? y
  ... | yes x≈y = (ƛ y ∶ T ⇒ t)
  ... | no  x≉y = Data.Bool.if (y ∈?ᵇ FV(s)) then (ƛ y ∶ T ⇒ t) else (ƛ y ∶ T ⇒ ([ x ↦ s ] t))
  [ x ↦ s ] (t₁ · t₂) = ([ x ↦ s ] t₁) · ([ x ↦ s ] t₂)
  [ x ↦ s ] (if t₁ then t₂ else t₃) = Term.if ([ x ↦ s ] t₁) then ([ x ↦ s ] t₂) else ([ x ↦ s ] t₃)

open Helper-Functions

--------------------------------------------------------------------------------
--                                                                            
-- Language Definition                                                        
--                                                                            
--------------------------------------------------------------------------------

data Value : Term → Set where
  λ-Abstraction : ∀ {x t} {T} → Value (ƛ x ∶ T ⇒ t)
  V-True        : Value true
  V-False       : Value false


-- Defining the evaluation rules
data _⟶_ : Term → Term → Set where
  E-IF      : ∀ {t₁ t₁` t₂ t₃} → t₁ ⟶ t₁` → (if t₁ then t₂ else t₃) ⟶ (if t₁` then t₂ else t₃)
  E-IFTRUE  : ∀ {t₂ t₃} → (if true then t₂ else t₃) ⟶ t₂
  E-IFFALSE : ∀ {t₂ t₃} → (if false then t₂ else t₃) ⟶ t₃
  E-APP1 : ∀ {t₁ t₁' t₂} → t₁ ⟶ t₁' → (t₁ · t₂) ⟶ (t₁' · t₂)
  E-APP2 : ∀ {v t t'} → Value v → t ⟶ t' → (v · t) ⟶ (v · t')
  E-APPABS : ∀ {v t} {x : Id} {T} → Value v → ((ƛ x ∶ T ⇒ t) · v) ⟶ ([ x ↦ v ] t)

infix 5 _,_∶_

-- Defining the typing context
data Context : Set where
  ∅     : Context
  _,_∶_ : Context → Id → Type → Context

variable
  Γ : Context
  T T₁ T₂ : Type

infix 4 _∶_∈_ 

data _∶_∈_ : Id → Type → Context → Set where
  Z : ∀ {x} → x ∶ T ∈ (Γ , x ∶ T) 
  S : ∀ {x y} → x ≢ y → x ∶ T₁ ∈ Γ → x ∶ T₁ ∈ Γ , y ∶ T₂

-- Smart constructor for S that proofs x ≢ y while type checking
S' : ∀ {x y} → {x≢y : False (x ≟ y)} → x ∶ T₁ ∈ Γ → x ∶ T₁ ∈ Γ , y ∶ T₂
S' {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-- Defining the typing rules

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where
  T-TRUE   : Γ ⊢ true ∶ Boolean
  T-FALSE  : Γ ⊢ false ∶ Boolean
  T-IF     : ∀ {t₁ t₂ t₃} → Γ ⊢ t₁ ∶ Boolean → Γ ⊢ t₂ ∶ T → Γ ⊢ t₃ ∶ T → Γ ⊢ (if t₁ then t₂ else t₃) ∶ T
  T-VAR : ∀ {x} → x ∶ T ∈ Γ → Γ ⊢ ` x ∶ T
  T-ABS : ∀ {x t} → Γ , x ∶ T₁ ⊢ t ∶ T₂ → Γ ⊢ ƛ x ∶ T₁ ⇒ t ∶ T₁ ⇒ T₂
  T-APP : ∀ {t₁ t₂ T₁ T₂} → Γ ⊢ t₁ ∶ T₁ ⇒ T₂ → Γ ⊢ t₂ ∶ T₁ → Γ ⊢ t₁ · t₂ ∶ T₂

--------------------------------------------------------------------------------
--
-- Proofs
--
--------------------------------------------------------------------------------

-- Lemma 9.3.1
-- Inversion of the typing relation

inversion1 : ∀ {x} → Γ ⊢ ` x ∶ T → x ∶ T ∈ Γ
inversion1 (T-VAR x) = x

inversion2 : ∀ {x R t₂} → Γ ⊢ ƛ x ∶ T₁ ⇒ t₂ ∶ R → ∃[ R₂ ] (Γ , x ∶ T₁ ⊢ t₂ ∶ R₂) × (R ≡ T₁ ⇒ R₂)
inversion2 (T-ABS {T₂ = T₂} p) = T₂ , p , refl

inversion3 : ∀ {t₁ t₂ T} → Γ ⊢ t₁ · t₂ ∶ T → ∃[ R ] ((Γ ⊢ t₁ ∶ R ⇒ T) × (Γ ⊢ t₂ ∶ R))
inversion3 (T-APP {T₁ = T₁} t₁ t₂) = T₁ , t₁ , t₂

inversion4 : Γ ⊢ true ∶ T → T ≡ Boolean
inversion4 T-TRUE = refl

inversion5 : Γ ⊢ false ∶ T → T ≡ Boolean
inversion5 T-FALSE = refl

inversion6 : ∀ {t₁ t₂ t₃} → Γ ⊢ if t₁ then t₂ else t₃ ∶ T → (Γ ⊢ t₁ ∶ Boolean) × (Γ ⊢ t₂ ∶ T) × (Γ ⊢ t₃ ∶ T)
inversion6 (T-IF p p₁ p₂) = p , p₁ , p₂

-- Lemma 9.3.4
-- Canonical Forms

canonical1 : ∀ {v} → Value v → Γ ⊢ v ∶ Boolean → (v ≡ true) ⊎ (v ≡ false)
canonical1 λ-Abstraction ()
canonical1 V-True  _ = inj₁ refl
canonical1 V-False _ = inj₂ refl

canonical2 : ∀ {v} → Value v → Γ ⊢ v ∶ T₁ ⇒ T₂ → ∃[ x ] ∃[ t ] v ≡ ƛ x ∶ T₁ ⇒ t
canonical2 λ-Abstraction (T-ABS {x = x} {t = t} type) = x , t , refl


-- Theorem 9.3.5
-- Progress
progress : ∀ {t T} → ∅ ⊢ t ∶ T → (Value t) ⊎ (∃[ t' ] t ⟶ t')
progress .{true} T-TRUE   = inj₁ V-True
progress .{false} T-FALSE = inj₁ V-False
progress .{(if t₁ then t₂ else t₃)} (T-IF {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} type _ _) with progress type
... | inj₁ V-True      = inj₂ (t₂ , E-IFTRUE)
... | inj₁ V-False     = inj₂ (t₃ , E-IFFALSE)
... | inj₂ (t' , t⟶t') = inj₂ ((if t' then t₂ else t₃) , E-IF t⟶t')

progress .{(ƛ _ ∶ _ ⇒ _)} (T-ABS type) = inj₁ λ-Abstraction

progress .{(_ · _)} (T-APP {t₁ = t₁} {t₂ = t₂} {T₁ = T₁} {T₂ = T₂} type₁ type₂) with progress type₁
... | inj₂ (t' , t⟶t') = inj₂ ((t' · t₂) , E-APP1 t⟶t')
... | inj₁ (λ-Abstraction {x = x} {t = t} {T = T}) with progress type₂
...   | inj₁ λ-Abstraction = inj₂ (( [ x ↦ t₂ ] t)        , E-APPABS λ-Abstraction)
...   | inj₁ V-True        = inj₂ (( [ x ↦ true ] t )    , (E-APPABS V-True))
...   | inj₁ V-False       = inj₂ (( [ x ↦ false ] t)    , (E-APPABS V-False))
...   | inj₂ (t' , t⟶t')   = inj₂ (( (ƛ x ∶ T ⇒ t) · t') , E-APP2 λ-Abstraction t⟶t')

-- Lemma 9.3.6
-- Permutation
-- TODO

∈→⊢ : ∀ {t} → t ∶ T ∈ Γ → Γ ⊢ ` t ∶ T
∈→⊢ t = T-VAR t

-- Lemma 9.3.7
-- Weakening
weakening : ∀ {t x S U} → Γ ⊢ t ∶ T → ¬ (x ∶ U ∈ Γ) → Γ , x ∶ S ⊢ t ∶ T
weakening T-TRUE _ = T-TRUE
weakening T-FALSE _ = T-FALSE
weakening (T-IF type type₁ type₂) x = T-IF (weakening type x) (weakening type₁ x) (weakening type₂ x)
weakening (T-VAR var) x = {!!}
weakening (T-ABS type) x = {!!}
weakening (T-APP type type₁) x = T-APP (weakening type x) (weakening type₁ x)

-- Lemma 9.3.8
-- Perservation of types under subsitution
sub-preservation : ∀ {t x s S} → Γ , x ∶ S ⊢ t ∶ T → Γ ⊢ s ∶ S → Γ ⊢ [ x ↦ s ] t ∶ T
sub-preservation t s = {!!}

-- Theorem 9.3.9
-- Preservation
-- TODO

-- TODO erasure
