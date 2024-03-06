Um conjunto pode ser entendido como uma colecao de coisas que compartiam uma mesma caracteristicas!



1. Note: tem o diagrama de Venn, nao muda nada, soh a forma de representar o conjunto

```agda

L = {Rust, Lua, Zig, TypeScript} -- conjunto de linguagens de programacao
n(L) = 4 -- quantidade de elementos do conjunto L


E = {1,2,3,5} 
-- ou
E = {x | x ∈ N, 1 ≤ x ≤ 5} -- conjunto de numeros naturais menores ou iguais a 5

-- o simbolo | eh lido como "tal que"
--  e o simbolo ∈ eh lido como "pertence a" tambem pode ser lido como "esta em"
-- o simbolo ∈ tem o oposto que eh ∉ que eh lido como "nao pertence a" ou "nao esta em"
```


2. Conjuntos unitarios, universais e vazios

```agda

P = {x | x e um n primo e par}  --  P = {2}

E = {x  | x elemento neutro da multiplicacao} -- E = {1}

U = {x | x ∈ N} -- U = N

V = {}
-- ou pode usar o simbolo ∅
V = ∅

```


3. Subconjuntos e conjuntos das partes

```agda