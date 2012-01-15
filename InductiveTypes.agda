module InductiveTypes where
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
open import Data.Nat using (_+_)

data unit : Set where
  tt : unit

unit-singleton : (x : unit) → x ≡ tt
unit-singleton tt = refl

unit-ind : (P : unit → Set) → P tt → ∀ u → P u
unit-ind P x tt = x
-- note agda doesn't define this automatically
-- is it possible to write within agda a program that derives an induction principle for any inductive type? probably not, but what about with data codes?

data Empty-set : Set where

the-sky-is-falling : (x : Empty-set) → 2 + 2 ≡ 5
the-sky-is-falling = λ ()

Empty-set-ind : (P : Empty-set → Set) → ∀ e → P e
Empty-set-ind = λ P → λ ()

e2u : (e : Empty-set) → unit
e2u = λ ()

data bool : Set  where
  true : bool
  false : bool

negb : (b : bool) → bool
negb true = false
negb false = true

negb-inverse : (b : bool) → negb (negb b) ≡ b
negb-inverse true = refl
negb-inverse false = refl

negb-ineq : (b : bool) → negb b ≢ b
negb-ineq true = λ ()
negb-ineq false = λ ()

bool-ind : (P : bool → Set) → P true → P false → (b : bool) → P b
bool-ind P t f true = t
bool-ind P t f false = f

data nat : Set where
  O : nat
  S : (n : nat) → nat

isZero : (n : nat) → bool
isZero O = true
isZero (S _) = false

pred : (n : nat) → nat
pred O = O
pred (S n) = n

S-isZero : (n : nat) → isZero (pred (S (S n))) ≡ false
S-isZero O = refl
S-isZero (S n) = refl

plus : (n m : nat) → nat
plus O m = m
plus (S n) m = S (plus n m)

O-plus-n : (n : nat) → plus O n ≡ n
O-plus-n = λ n → refl

open import Relation.Binary.PropositionalEquality using (cong)

n-plus-O : (n : nat) → plus n O ≡ n
n-plus-O O = refl
n-plus-O (S n) = cong S (n-plus-O n)

-- open import Reflection using (Term;Arg)
-- cong-or-refl : (t : Term) →
