-- module normalize.lambda_calculus where

-- open import Data.Nat
-- open import Data.Bool
-- open import Data.Product
-- open import Relation.Binary.PropositionalEquality
-- open import Data.List
-- -- use ==
-- -- open import Data.String
-- -- open import Data.Vec
-- -- open import Data.String
-- -- open import Data.Vec
-- -- open import Data.Fin

-- Nat = ℕ 

-- {- variables = x, y, z, ...
--    λ-abstraction = λx. M
--    application = M N
-- -}

-- data Term : Set where
--   var : Nat → Term
--   abs : Term → Term
--   app : Term → Term → Term

-- -- free variables
-- free_var : Term → List Nat
-- free_var (var x) = x ∷ []    -- variavel livre de uma variavel é ela mesma
-- free_var (abs t) = free_var t -- variavel livre de uma abstração é a variavel livre do termo
-- free_var (app t1 t2) = free_var t1 ++ free_var t2 -- variavel livre de uma aplicação é a união das variaveis livres dos termos

-- -- substitution
-- _subst : Nat → Term → Term → Term
-- _subst x s (var y) = if x == y then s else var y -- [x := s]x = s
-- _subst x s (abs t) = abs (_subst x s t)         -- [x := s](λy. t) = λy. [x := s]t
-- _subst x s (app t1 t2) = app (_subst x s t1) (_subst x s t2) -- [x := s](t1 t2) = ([x := s]t1 [x := s]t2)