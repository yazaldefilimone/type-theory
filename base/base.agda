module base.base where
  open import Data.Nat
  -- change == to ===
  open import Data.Bool 
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Data.List
  open import Data.String
  open import Data.Vec
  -- open import Data.Fin
  
  Nat = ℕ
  
  data List_Nat (A : Set) : Nat → Set where
    [] : List_Nat A zero
    _∷_ : {n : Nat} → A → List_Nat A n → List_Nat A (suc n)



  create_list : List_Nat ℕ 3 -- uma lista do tipo List_Nat que contém 3 elementos do conjunto Nat(ℕ)
  create_list = 1 ∷ 2 ∷ 3 ∷ [] -- uma lista de 3 elementos equivalente a [1,2,3]
  -- function definition
  add : Nat → Nat → Nat -- função que soma dois números naturais e retorna um número natural
  add zero m = m  -- caso base, se o primeiro número for zero, a soma é o segundo número
  add (suc n) m = suc (add n m) -- caso recursivo, soma o primeiro número com o segundo número
  -- exemplo de uso da função add
  result_add : Nat
  result_add = add 2 3 -- resultado é 5
  

  --  data type definition
  data LinkedList (A : Set) : Set where
    nil : LinkedList A
    cons : A → LinkedList A → LinkedList A

  
  linked_list : LinkedList ℕ -- uma lista encadeada do tipo LinkedList que contém 3 elementos do conjunto Nat(ℕ)
  linked_list = cons 1 (cons 2 (cons 3 nil)) -- uma lista de 3 elementos equivalente a 1 -> 2 -> 3 -> nil



  -- function definition with dependent types
  len_linked_list : {A : Set} → LinkedList A → Nat -- função que retorna o tamanho de uma lista encadeada
  len_linked_list nil = zero -- caso base, se a lista for vazia, o tamanho é zero
  len_linked_list (cons current_element rest_linked_list) = suc (len_linked_list rest_linked_list) -- caso recursivo, incrementa o tamanho da lista
  
  -- exemplo de uso da função len_linked_list
  result_len_linked_list : Nat
  result_len_linked_list = len_linked_list linked_list -- resultado é 3
  
  -- proof of associativity of addition 
  assoc : ∀ (m n p : Nat) → (m + n) + p ≡ m + (n + p)
  assoc zero n p = refl
  assoc (suc m) n p = cong suc (assoc m n p)
 

  -- arvore binária de Nat

  data Tree_Nat : Set where
    leaf : Tree_Nat -- nó folha, ele nao recebe nenhum valor (representa um nó vazio)
    node : Nat → Tree_Nat → Tree_Nat → Tree_Nat -- nó interno, recebe um valor do tipo Nat e duas sub-árvores (esquerda e direita)

  -- exemplo de árvore binária
  tree : Tree_Nat
  tree = node 1 (node 2 leaf leaf) (node 3 leaf leaf)
  -- uma árvore binária com raiz 1, sub-árvore esquerda com raiz 2 e sub-árvore direita com raiz 3



  -- função que retorna a altura de uma árvore binária
  max : Nat → Nat → Nat
  max zero n = n -- função que retorna o maior número entre zero e um número
  max (suc m) n = suc (max m n) -- função que retorna o maior número entre dois números
  {-
    max zero n - se o primeiro número for zero, o maior número é o segundo número
    max (suc m) n - se o primeiro número for maior que zero, 
    o maior número é o sucessor do maior número entre o primeiro número menos um e o segundo número



  -}

  height_tree : Tree_Nat → Nat
  height_tree leaf = zero
  height_tree (node current left right) = suc (max (height_tree left) (height_tree right))


  -- criar um mapa (equivalente a: { na: 10})

  data _Map : Set where
    empty : _Map
    fn_add : String → Nat → _Map → _Map

  _map : _Map
  _map = fn_add "na" 10 empty

  -- função que retorna o valor de uma chave em um mapa
  map_lookup : String → _Map → Nat
  map_lookup key empty = zero
  map_lookup key (fn_add current_key current_value rest_map) = if key == current_key then current_value else map_lookup key rest_map
    -- exemplo de uso da função map_lookup
  result_map_lookup : Nat
  result_map_lookup = map_lookup "na" _map -- resultado é 10

  -- função que adiciona uma chave e um valor em um mapa e retorna zero
  map_add : String → Nat → _Map → Nat -- função que adiciona uma chave e um valor em um mapa e retorna zero
  map_add key value empty = zero
  map_add key value (fn_add current_key current_value rest_map) = if key == current_key then value else map_add key value rest_map

  -- exemplo de uso da função map_add
  result_map_add : Nat
  result_map_add = map_add "nb" 20 _map -- resultado é 20







  -- -----------      lambda calculos      ------------

  {- variables = x, y, z, ...
    λ-abstraction = λx. M
    application = M N
  -}



  data Term : Set where
    var : Nat → Term
    abs : Term → Term
    app : Term → Term → Term

  -- free variables
  free_var : Term → List Nat
  free_var (var x) = x ∷ []    -- variavel livre de uma variavel é ela mesma
  free_var (abs t) = free_var t -- variavel livre de uma abstração é a variavel livre do termo
  free_var (app t1 t2) = free_var t1 Data.List.++ free_var t2 -- variavel livre de uma aplicação é a união das variaveis livres dos termos

  get_value_var : Term → Nat
  get_value_var (var x) = x
  -- substitution
  _subst : Nat → Term → Term → Term
  _subst x s (var y) = if get_value_var x == get_value_var y then s else var y -- [x := s]x = s
  _subst x s (abs t) = abs (_subst x s t)         -- [x := s](λy. t) = λy. [x := s]t
  _subst x s (app t1 t2) = app (_subst x s t1) (_subst x s t2) -- [x := s](t1 t2) = ([x := s]t1 [x := s]t2)