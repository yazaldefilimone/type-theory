module checker where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Data.Fin hiding (_+_)

  Nat = ℕ

  data Term : Set where
    var : Nat → Term
    type : Term
    abstraction : Term → Term → Term
    application : Term → Term → Term


  Substitution : Set
  Substitution = Term

 
  shift : Substitution → Substitution
  shift (var i) = var (suc i)
  shift type         = type
  shift (abstraction body1 body2) = abstraction (shift body1) (shift body2)
  shift (application fun arg)     = application (shift fun) (shift arg)


  substitute : Substitution → Term → Term
  substitute subs (var i) = subs -- Substitui a variável livre i por subs, i é uma variável livre
  substitute subs type = type 
  substitute subs (abstraction param body) = abstraction (substitute subs param) (substitute (shift subs) body) -- Substitui a variável livre param por subs e desloca as variáveis livres de body
  substitute subs (application fun arg) = application (substitute subs fun) (substitute subs arg) -- Substitui as variáveis livres de fun e arg por subs, subs é uma variável livre

  normalize : Term → Term
  normalize (var i) = var i 
  normalize type  = type 
  normalize (abstraction param body) = abstraction (normalize param) (normalize body) -- Normaliza os parâmetros e o corpo
  normalize (application fun arg) = substitute arg (normalize fun) -- Substitui a variável livre arg por fun

  -- -- Testes
  -- ex1 : Term
  -- ex1 = abstraction (abstraction (var 0) (var 1)) (var 0)

  -- ex2 : Term
  -- ex2 = application (abstraction (var 0) (var 0)) (var 1) 

  -- -- norm
  -- test1 : Term
  -- test1 = normalize ex1 -- 

  -- test2 : Term
  -- test2 = normalize ex2 -- y

  -- test_norm_ex1 : test1 ≡ (abstraction (var 0) (var 1))
  -- test_norm_ex1 = refl

  -- test_norm_ex2 : test2 ≡ var 1
  -- test_norm_ex2 = refl
