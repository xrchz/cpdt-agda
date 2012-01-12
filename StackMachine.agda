module StackMachine where

open import Data.Nat using (ℕ;_+_;_*_)
open import Data.List using (List;_∷_;[];_++_;monoid)
open import Data.Maybe using (Maybe;just;nothing)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans;subst)
open import Algebra using (Monoid)
open import Data.Product using (proj₂)

data binop : Set where
  Plus : binop
  Times : binop

data exp : Set where
  Const : (n : ℕ) → exp
  Binop : (b : binop) → (e1 : exp) → (e2 : exp) → exp

binopDenote : (b : binop) → ℕ → ℕ → ℕ
binopDenote Plus = _+_
binopDenote Times = _*_

expDenote : (e : exp) → ℕ
expDenote (Const n) = n
expDenote (Binop b e1 e2) = binopDenote b (expDenote e1) (expDenote e2)

data instr : Set where
  iConst : ℕ → instr
  iBinop : binop → instr

prog = List instr
stack = List ℕ

instrDenote : (i : instr) → (s : stack) → Maybe stack
instrDenote (iConst n) s = just (n ∷ s)
instrDenote (iBinop b) (arg1 ∷ arg2 ∷ s') = just ((binopDenote b) arg1 arg2 ∷ s')
instrDenote (iBinop b) _ = nothing

progDenote : (p : prog) → (s : stack) → Maybe stack
progDenote [] s = just s
progDenote (i ∷ p') s with instrDenote i s
progDenote (i ∷ p') s | just s' = progDenote p' s'
progDenote (i ∷ p') s | nothing = nothing

compile : (e : exp) → prog
compile (Const n) = (iConst n) ∷ []
compile (Binop b e1 e2) = compile e2 ++ compile e1 ++ iBinop b ∷ []

app-assoc-reverse = Monoid.assoc (monoid instr)
app-nil-end = proj₂ (Monoid.identity (monoid instr))
-- why have to specify instr?

compile-correct' : ∀ e p s → progDenote (compile e ++ p) s ≡ progDenote p (expDenote e ∷ s)
compile-correct' (Const n) p s = refl -- everything after intros done automatically
-- compile-correct' (Binop b e1 e2) p s = {!!}
compile-correct' (Binop b e1 e2) p s rewrite (app-assoc-reverse (compile e2) (compile e1 ++ iBinop b ∷ []) p) | (app-assoc-reverse (compile e1) (iBinop b ∷ []) p) = trans (compile-correct' e2 (compile e1 ++ iBinop b ∷ p) s) (compile-correct' e1 (iBinop b ∷ p) (expDenote e2 ∷ s))
-- why have to specify the instance of the rewrite?
-- note: most of actual proof was filled in by C-c C-a

compile-correct : ∀ e → progDenote (compile e) [] ≡ just (expDenote e ∷ [])
compile-correct e = subst (λ x → progDenote x [] ≡ progDenote [] (expDenote e ∷ [])) (app-nil-end (compile e)) (compile-correct' e [] [])
-- this is pretty awful