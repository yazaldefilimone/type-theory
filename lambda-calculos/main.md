




```rs

0 = λf.λx.x
1 = λf.λx.f x
2 = λf.λx.f(f(x))
3 =  λf.λx.f(f(f(x)))

True = λx.λy.x
False = λx.λy.y

IF =  λb.λt.λf.b t f


if(a) False else True

NOT= λa.(λb.λt.λf.b t f) a λx.λ.y.y λx.λy.x


if(w) z else False 

AND = λw.λz.(λb.λt.λf b t f) w z λx.λy.y 

if (w) True else z
OR = λw.λz.(λb.λt.λf b t f) w λx.λy.x z


λx.x y z = f(x) = f((x y) z)

```
