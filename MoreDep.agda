module MoreDep where

open import Data.Nat
open import Data.Bool hiding (_≟_) renaming (Bool to bool) 
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data type : Set where
  Nat  : type
  Bool : type
  Prod : type → type → type

data exp : type → Set where
  NConst : ℕ → exp Nat
  Plus   : exp Nat → exp Nat → exp Nat
  Eq     : exp Nat → exp Nat → exp Bool

  BConst : bool → exp Bool
  And    : exp Bool → exp Bool → exp Bool
  If     : ∀ {t} → exp Bool → exp t → exp t → exp t

  Pair   : ∀ {t1 t2} → exp t1 → exp t2 → exp (Prod t1 t2)
  Fst    : ∀ {t1 t2} → exp (Prod t1 t2) → exp t1
  Snd    : ∀ {t1 t2} → exp (Prod t1 t2) → exp t2

typeDenote : type → Set
typeDenote Nat = ℕ
typeDenote Bool = bool
typeDenote (Prod t1 t2) = typeDenote t1 × typeDenote t2

expDenote : ∀ {t} (e : exp t) → typeDenote t
expDenote (NConst n) = n
expDenote (Plus e1 e2) = expDenote e1 + expDenote e2
expDenote (Eq e1 e2) with expDenote e1 ≟ expDenote e2
expDenote (Eq e1 e2) | yes p = true
expDenote (Eq e1 e2) | no ¬p = false

expDenote (BConst b) = b
expDenote (And e1 e2) = (expDenote e1) ∧ (expDenote e2)
expDenote (If e e1 e2) = if (expDenote e) then (expDenote e1) else (expDenote e2)

expDenote (Pair e1 e2) = (expDenote e1) , (expDenote e2)
expDenote (Fst e) = proj₁ (expDenote e)
expDenote (Snd e) = proj₂ (expDenote e)

cfold : ∀ {t} (e : exp t) → exp t
cfold (NConst n) = NConst n
cfold (Plus e1 e2) with cfold e1 | cfold e2
... | NConst n1 | NConst n2 = NConst (n1 + n2)
... | e1'       | e2'       = Plus e1' e2'
cfold (Eq e1 e2) with cfold e1 | cfold e2
cfold (Eq e1 e2) | NConst e1' | NConst e2' with e1' ≟ e2'
cfold (Eq e1 e2) | NConst e1' | NConst e2' | yes p = BConst true
cfold (Eq e1 e2) | NConst e1' | NConst e2' | no ¬p = BConst false
cfold (Eq e1 e2) | e1'        | e2'        = Eq e1' e2'
cfold (BConst b) = BConst b
cfold (And e1 e2) with cfold e1 | cfold e2
cfold (And e1 e2) | BConst b1 | BConst b2 = BConst (b1 ∧ b2)
cfold (And e1 e2) | e1' | e2' = And e1' e2'
cfold (If e e1 e2) with cfold e
cfold (If e e1 e2) | BConst true  = cfold e1
cfold (If e e1 e2) | BConst false = cfold e2
... | e' = If e' e1 e2
cfold (Pair e1 e2) = Pair (cfold e1) (cfold e2)
cfold (Fst e) with cfold e
cfold (Fst e) | Pair x _ = x
cfold (Fst e) | e' = Fst e'
cfold (Snd e) with cfold e
cfold (Snd e) | Pair _ y = y
cfold (Snd e) | e' = Snd e'

cfold-correct : ∀ {t} (e : exp t) → expDenote e ≡ expDenote (cfold e)
cfold-correct (NConst y) = refl
cfold-correct (Plus e e1) = {!!}
cfold-correct (Eq e e1) = {!!}
cfold-correct (BConst y) = {!!}
cfold-correct (And e e1) = {!!}
cfold-correct (If e e1 e2) = {!!}
cfold-correct (Pair e e1) = {!!}
cfold-correct (Fst e) = {!!}
cfold-correct (Snd e) = {!!}
