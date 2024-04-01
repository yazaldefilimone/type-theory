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
  shift type = type
  shift (abstraction body1 body2) = abstraction (shift body1) (shift body2)
  shift (application fun arg) = application (shift fun) (shift arg)

  substitute : Substitution → Term → Term
  substitute subs (var i) = subs
  substitute subs type = type
  substitute subs (abstraction param body) = abstraction param (substitute (shift subs) body)
  substitute subs (application fun arg) = application (substitute subs fun) (substitute subs arg)

  normalize : Term → Term
  normalize (var i) = var i
  normalize type = type
  normalize (abstraction param body) = abstraction param (normalize body)
  normalize (application fun arg) = substitute arg (normalize fun)

  -- -- Testes

  -- vars
  test1 = normalize (var 0) -- var 0
  test2 = normalize (var 1) -- var 1

  -- T
  test3 = normalize type -- type

  -- abst
  test4 = normalize (abstraction (var 0) (var 0)) -- abstraction (var 0) (var 0)
  test5 = normalize (abstraction (var 0) (abstraction (var 1) (application (var 0) (var 1)))) -- abstraction (var 0) (abstraction (var 1) (application (var 0) (var 1)))

  -- app
  test6 = normalize (application (var 0) (var 1)) -- application (var 0) (var 1)
  test7 = normalize (application (abstraction (var 0) (var 0)) (var 1)) -- var 1
  test8 = normalize (application (abstraction (var 0) (abstraction (var 1) (application (var 0) (var 1)))) (var 2)) -- abstraction (var 0) (application (var 0) (var 2))
  test9 = normalize (application (abstraction (var 0) (application (var 0) (var 1))) (abstraction (var 2) (var 2))) -- application (abstraction (var 2) (var 2)) (var 1)

  -- app + abst
  test10 = normalize (application (abstraction (var 0) (application (var 0) (var 1))) (abstraction (var 2) (application (var 2) (var 3)))) -- application (abstraction (var 2) (application (var 2) (var 3))) (var 1)
