module checker where
  open import Data.Nat
  open import Data.List
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Bool
  open import Data.String
  open import Data.Fin

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
  -- var : String -> Type ie. var "x" : Type in lc: λx.x
  {-
    λx.x : nat => nat
    λx.λy.x : nat => nat => nat
    λx.λy.x y : nat => nat => nat

  
  -}

  data Expr : Set where
    var : Nat -> Expr
    abs : Expr -> Expr
    app : Expr -> Expr -> Expr

  data Context : Set where
    empty : Context
    cons : Type -> Context -> Context

  -- data check : Context -> Expr -> Type -> Set where
  --  var : {Γ : Context} -> {x : Nat} -> check Γ (var x) nat
  --  abs : {Γ : Context} -> {e : Expr} -> {τ1 τ2 : Type} -> check (cons τ1 Γ) e τ2 -> check Γ (abs e) (=> τ1 τ2)
  --  app : {Γ : Context} -> {e1 e2 : Expr} -> {τ1 τ2 : Type} -> check Γ e1 (=> τ1 τ2) -> check Γ e2 τ1 -> check Γ (app e1 e2) τ2

  -- data check : Context → Expr → Type → Set where
  --  var : (Γ : Context) → (x : Nat) → check Γ (var x) nat
  --  abs : (Γ : Context) → (e : Expr) → (τ1 τ2 : Type) → check (cons τ1 Γ) e τ2 → check Γ (abs e) (=> τ1 τ2)
  --  app : (Γ : Context) → (e1 e2 : Expr) → (τ1 τ2 : Type) → check Γ e1 (=> τ1 τ2) → check Γ e2 τ1 → check Γ (app e1 e2) τ2

  data check : Context → Expr → Type → Set where
    var : {Γ : Context} -> {x : Nat} -> check Γ (var x) nat
    abs : {Γ : Context} -> {e : Expr} -> {τ1 τ2 : Type} -> check (cons τ1 Γ) e τ2 -> check Γ (abs e) (τ1 => τ2)
    app : {Γ : Context} -> {e1 e2 : Expr} -> {τ1 τ2 : Type} -> check Γ e1 (τ1 => τ2) -> check Γ e2 τ1 -> check Γ (app e1 e2) τ2


  -- ---------- teste lambda ----------
  var_test : check (cons nat empty) (var 0) nat 
  var_test = var

  abs_test : check empty (abs (var 0)) (nat => nat)
  abs_test = abs var

  app_test : check empty (app (abs (var 0)) (var 0)) nat
  app_test = app (abs var) var

  -- ----- normalize ----- ,
  rename_free_vars : (e : Expr) -> (x : Nat) -> (y : Nat) -> Expr
  rename_free_vars (var x) y z = if x == z then var y else var x
  rename_free_vars (abs e) y z = abs (rename_free_vars e y z)
  rename_free_vars (app e1 e2) y z = app (rename_free_vars e1 y z) (rename_free_vars e2 y z)