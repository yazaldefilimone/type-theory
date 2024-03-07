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

-- 3. Subconjuntos e conjuntos das partes
-- Subconjunto eh um conjunto que contem todos os elementos de outro conjunto



A = {1,2,3,4}
B = {1,2,3}

B ⊆ A -- B eh subconjunto de A (ou B esta contido em A)
A ⊇ B -- A eh superconjunto de B (ou A contem B)

P = {2,6,8}
V = {8,10,12}
-- P nao esta contido em V
V /⊇ P
P /⊆ V

-- - Propriedades dos subconjuntos

∅ ⊆ A -- todo conjunto eh subconjunto do conjunto vazio
Reflexiva: A ⊆ A -- todo conjunto eh subconjunto de si mesmo

-- Anti-simetrica: 
A ⊆ B e B ⊆ A, A = B -- se A eh subconjunto de B e B eh subconjunto de A, entao A eh igual a B

--Transitiva: 

A ⊆ B e B ⊆ C, A ⊆ C -- se A eh subconjunto de B, e B eh subconjunto de C, entao A eh subconjunto de C


-- - Conjunto das partes



X = {{a}}
-- o conjunto das partes de P eh
P(x) = {∅, {a}}

n(P(x)) = 2^1 = 2 -- quantidade de elementos do conjunto das partes de X, onde o expoente eh a quantidade de elementos do conjunto X

N = {1,2,3... n} ---
n(N) = n
n(P(N)) = 2^n -- quantidade de elementos do conjunto das partes de N, onde o expoente eh a quantidade de elementos do conjunto N


-- 4. Operacoes com conjuntos

A = {1,2,3,4}
B = {3,4,5,6}
C = {1,2,3,4,5,6}
-- Uniao
C = A ∪ B -- x | x ∈ A ou x ∈ B

-- Interseccao
C = A ∩ B -- x | x ∈ A e x ∈ B
-- A ∩ A = A
-- A ∩ ∅ = A
-- A ∩ U = A


X U (Y ∩ Z) = (X U Y) ∩ (X U Z) -- propriedade distributiva da uniao e interseccao
X ∩ (Y U Z) = (X ∩ Y) U (X ∩ Z) -- propriedade distributiva da interseccao e uniao
X U (Y U Z) = (X U Y) U Z -- propriedade associativa da uniao
X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z -- propriedade associativa da interseccao


A U (B ∩ C) = A
A ∩ (B U C) = A


--- Soma de conjuntos

A = {1,2,3}
B = {3,4,5}
C = A U B -- C = {1,2,3,4,5}

D = A ∩ B -- D = {3}


n(A U B) = n(A) + n(B) - n(A ∩ B) -- formula da soma de conjuntos, subtraindo a interseccao para nao contar elementos repetidos



--- Diferenca de conjuntos

A = {1,2,3,4}
B = {3,4,5,6}
C = A - B -- C = {1,2}
D = B - A -- D = {5,6}

A - B = x | x ∈ A e x ∉ B -- o elemento x pertence a A e nao pertence a B
B - A = x | x ∈ B e x ∉ A -- o elemento x pertence a B e nao pertence a A

A -B /= B - A -- a diferenca de conjuntos nao eh comutativa


--- Complemento de um conjunto
-- complemento de um conjunto A eh o conjunto de todos os elementos que nao pertencem a A
A = {1,2,3,4}
B = {3,4,5,6}

A' = U - A -- complemento de A
B' = U - B -- complemento de B


```