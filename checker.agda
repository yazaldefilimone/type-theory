module checker where
  open import Data.Nat
  open import Data.List
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Bool
  -- τ
  open import Data.Empty

  --  simple type checker for lambda calculus


  Nat = ℕ

{-
  lambda calculus language:
  x ::= x | λx.x | x x -- variables, lambda abstractions, applications

  type language:
  τ ::= Nat | τ -> τ -- signica: natural numbers, functions

  typing judgement:
  Γ ⊢ x : τ -- no contexto Γ, x tem tipo τ
  Γ ⊢ λx.x : τ -- no contexto Γ, a função lambda tem tipo τ
  Γ ⊢ x x : τ -- no contexto Γ, a aplicação de x a x tem tipo τ

  typing rules:
  --------------- (var)
  Γ ⊢ x : τ -- no contexto Γ, x tem tipo τ

  Γ, x : τ1 ⊢ x : τ1 -- x tem tipo τ1 no contexto Γ, x : τ1
  ---------------------- (abs)
  Γ ⊢ λx.x : τ1 -> τ2 -- no contexto Γ, a função lambda tem tipo τ1 -> τ2

  Γ ⊢ x : τ1 -> τ2   Γ ⊢ x : τ1 -- no contexto Γ, x tem tipo τ1 -> τ2 e x tem tipo τ1
  ------------------------------- (app) 
  Γ ⊢ x x : τ2 -- no contexto Γ, a aplicação de x a x tem tipo τ2

-}

  data Type : Set where
    nat : Type
    _=>_ : Type -> Type -> Type

  data Expr : Set where
    var : Nat -> Expr
    abs : Expr -> Expr
    app : Expr -> Expr -> Expr

  data Context : Set where
    empty : Context
    cons : Type -> Context -> Context

  -- data check : Context -> Expr -> Type -> Set where
  --   var : {Γ : Context} -> {x : Nat} -> check Γ (var x) nat
  --   abs : {Γ : Context} -> {e : Expr} -> {τ1 τ2 : Type} -> check (cons τ1 Γ) e τ2 -> check Γ (abs e) (=> τ1 τ2)
  --   app : {Γ : Context} -> {e1 e2 : Expr} -> {τ1 τ2 : Type} -> check Γ e1 (=> τ1 τ2) -> check Γ e2 τ1 -> check Γ (app e1 e2) τ2
  
  -- data check : Context → Expr → Type → Set where
  --   var : (Γ : Context) → (x : Nat) → check Γ (var x) nat
  --   abs : (Γ : Context) → (e : Expr) → (τ1 τ2 : Type) → check (cons τ1 Γ) e τ2 → check Γ (abs e) (=> τ1 τ2)
  --   app : (Γ : Context) → (e1 e2 : Expr) → (τ1 τ2 : Type) → check Γ e1 (=> τ1 τ2) → check Γ e2 τ1 → check Γ (app e1 e2) τ2

  data check : Context → Expr → Type → Set where
    var : {Γ : Context} -> {x : Nat} -> check Γ (var x) nat
    abs : {Γ : Context} -> {e : Expr} -> {τ1 τ2 : Type} -> check (cons τ1 Γ) e τ2 -> check Γ (abs e) (τ1 => τ2)
    app : {Γ : Context} -> {e1 e2 : Expr} -> {τ1 τ2 : Type} -> check Γ e1 (τ1 => τ2) -> check Γ e2 τ1 -> check Γ (app e1 e2) τ2
-- -------------- teste --------------
  var_test : check (cons nat empty) (var 0) nat 
  var_test = var

  abs_test : check empty (abs (var 0)) (nat => nat)
  abs_test = abs var_test
