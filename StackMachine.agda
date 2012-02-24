module StackMachine where

open import Data.Nat using (ℕ;_+_;_*_)
open import Data.List using (List;_∷_;[];_++_;monoid)
open import Data.Maybe using (Maybe;just;nothing)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans;subst)
open import Algebra using (Monoid;module Monoid)
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

module I {A : Set} = Monoid (monoid A)

app-nil-end = proj₂ (Monoid.identity (monoid instr))
-- why have to specify instr?

compile-correct' : ∀ e p s → progDenote (compile e ++ p) s ≡ progDenote p (expDenote e ∷ s)
compile-correct' (Const n) p s = refl -- everything after intros done automatically
compile-correct' (Binop b e1 e2) p s = {!!}
-- compile-correct' (Binop b e1 e2) p s rewrite (I.assoc (compile e2) (compile e1 ++ iBinop b ∷ []) p) | (I.assoc (compile e1) (iBinop b ∷ []) p) = trans (compile-correct' e2 (compile e1 ++ iBinop b ∷ p) s) (compile-correct' e1 (iBinop b ∷ p) (expDenote e2 ∷ s))
-- why have to specify the instance of the rewrite? that's awful
-- is it possible to get the effects of rewriting as a proof term rather than using with (rewrite)?
-- what about rewriting possibilities via quoteGoal...?
-- note: most of actual proof was filled in by C-c C-a
-- alternatively: use equational rewriting thing in standard library
-- dan rosén's automatic theorem prover for agda proof of concept

compile-correct : ∀ e → progDenote (compile e) [] ≡ just (expDenote e ∷ [])
compile-correct e = subst (λ x → progDenote x [] ≡ progDenote [] (expDenote e ∷ [])) (app-nil-end (compile e)) (compile-correct' e [] [])
-- this is pretty awful

open import Data.Bool renaming (Bool to bool;_≟_ to _≟b_)
open import Data.Nat using (_≤?_;_≟_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Unit using (⊤;tt)
open import Data.Product using (_×_;_,_)

data type : Set where
  Nat : type
  Bool : type

data tbinop : type → type → type → Set where
  TPlus : tbinop Nat Nat Nat
  TTimes : tbinop Nat Nat Nat
  TEq : ∀ t → tbinop t t Bool
  TLt : tbinop Nat Nat Bool

data texp : type → Set where
  TNConst : (n : ℕ) → texp Nat
  TBConst : (b : bool) → texp Bool
  TBinop : ∀ {t1 t2 t} → (b : tbinop t1 t2 t) → (e1 : texp t1) → (e2 : texp t2) → texp t
  
typeDenote : (t : type) → Set
typeDenote Nat = ℕ
typeDenote Bool = bool

tbinopDenote : ∀ {arg1 arg2 res} (b : tbinop arg1 arg2 res) → typeDenote arg1 → typeDenote arg2 → typeDenote res
tbinopDenote TPlus = _+_
tbinopDenote TTimes = _*_
tbinopDenote (TEq Nat) = λ m n → ⌊ m ≟ n ⌋ 
tbinopDenote (TEq Bool) = λ a b → ⌊ a ≟b b ⌋
tbinopDenote TLt = λ m n → ⌊ m ≤? n ⌋

texpDenote : ∀ {t} → (e : texp t) → typeDenote t
texpDenote (TNConst n) = n
texpDenote (TBConst b) = b
texpDenote (TBinop b e1 e2) = tbinopDenote b (texpDenote e1) (texpDenote e2)

tstack = List type

data tinstr : tstack → tstack → Set where
  TiNConst : ∀ s → (n : ℕ) → tinstr s (Nat ∷ s)
  TiBConst : ∀ s → (b : bool) → tinstr s (Bool ∷ s)
  TiBinop : ∀ {arg1 arg2 res} s → (b : tbinop arg1 arg2 res) → tinstr (arg1 ∷ arg2 ∷ s) (res ∷ s)

data tprog : tstack → tstack → Set where
  TNil : ∀ {s} → tprog s s
  TCons : ∀ {s1 s2 s3} → tinstr s1 s2 → tprog s2 s3 → tprog s1 s3

vstack : (ts : tstack) → Set
vstack [] = ⊤
vstack (t ∷ ts') = typeDenote t × vstack ts'

tinstrDenote : ∀ {ts ts'} → (i : tinstr ts ts') → (s : vstack ts) → vstack ts'
tinstrDenote {ts} (TiNConst .ts n) s = n , s
tinstrDenote {ts} (TiBConst .ts b) s = b , s
tinstrDenote (TiBinop _ b) (arg1 , arg2 , s') = (tbinopDenote b arg1 arg2) , s'

tprogDenote : ∀ {ts ts'} → (p : tprog ts ts') → vstack ts → vstack ts'
tprogDenote TNil = λ x → x
tprogDenote (TCons i p') = λ x → tprogDenote p' (tinstrDenote i x)

tconcat : ∀  {ts ts' ts''} → (p : tprog ts ts') → tprog ts' ts'' → tprog ts ts''
tconcat TNil = λ x → x
tconcat (TCons i p1) = λ x → TCons i (tconcat p1 x)

tcompile : ∀ {t} → (e : texp t) → (ts : tstack) → tprog ts (t ∷ ts)
tcompile (TNConst n) ts = TCons (TiNConst _ n) TNil
tcompile (TBConst b) ts = TCons (TiBConst _ b) TNil
tcompile (TBinop b e1 e2) ts = tconcat (tcompile e2 _) (tconcat (tcompile e1 _) (TCons (TiBinop _ b) TNil))

tconcat-correct : ∀ {ts ts' ts''} → (p : tprog ts ts') → (p' : tprog ts' ts'') → (s : vstack ts) → tprogDenote (tconcat p p') s ≡ tprogDenote p' (tprogDenote p s)
tconcat-correct TNil = λ p' s → refl
tconcat-correct (TCons y y') = λ p' s → tconcat-correct y' p' (tinstrDenote y s)
-- case split, then auto

open import Relation.Binary.PropositionalEquality using (cong₂)

tcompile-correct' : ∀ {t} → (e : texp t) → ∀ ts → (s : vstack ts) → tprogDenote (tcompile e ts) s ≡ texpDenote e , s
tcompile-correct' (TNConst n) ts s = refl
tcompile-correct' (TBConst b) ts s = refl
tcompile-correct' (TBinop {t2 = t2} b e1 e2) ts s rewrite (tconcat-correct (tcompile e2 ts) (tconcat (tcompile e1 (t2 ∷ ts)) (TCons (TiBinop ts b) TNil)) s) | (tconcat-correct (tcompile e1 (t2 ∷ ts)) (TCons (TiBinop ts b) TNil) (tprogDenote (tcompile e2 ts) s)) | (tcompile-correct' e1 (t2 ∷ ts) (tprogDenote (tcompile e2 ts) s)) | (tcompile-correct' e2 ts s) = cong₂ _,_ refl refl
-- this is a nightmare...
-- need generalized rewriting

tcompile-correct : ∀ t → (e : texp t) → tprogDenote (tcompile e []) tt ≡ texpDenote e , tt
tcompile-correct t e = tcompile-correct' e [] tt