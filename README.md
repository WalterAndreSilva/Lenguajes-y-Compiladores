# Laboratorio Lenguajes y Compiladores #

## Enunciado ##

Implementar la semántica denotacional para el lenguaje imperativo simple +
fallas + input-output (LIS+Fallas+IO).

**Tarea**
Implementar la sintaxis abstracta con los constructores correspondientes y
definir la función semántica

```[Haskell]
sem :: Expr dom → Σ → dom
```

que implementa el significado de estas expresiones; implementar las instancias
de la clase DomSem para Int, Bool y Ω. Para nuestra implementación estamos
eligiendo representar a los identificadores con tipo _String_ y, más importante,
al conjunto de estados Σ como una función de identificadores en Int 

```[Haskell]
Σ = Iden -> Int
```

así por ejemplo podemos implementar el estado en el cual todas las variables tiene
asignado el valor cero tan fácil como

```[Haskell]
σ :: Σ
σ _ = 0
```
(o escribiendo, `\_ -> 0`, usando https://wiki.haskell.org/Lambda_abstraction)

1.a. Agregar los constructores sintácticos correspondientes al lenguaje de
     expresiones enteras y booleanas.

1.b. Implementar su función semántica para estos constructores.

1.c. Probar con algunos ejemplos que la implementación es correcta, por ejemplo
	 ejecutando:
```[Haskell]
eval_intexp_ej1 :: IO ()
eval_intexp_ej1 = eval (Plus (Const 2) (Const 2)) (\_ -> 0)
```
1.d. - ¿Qué ocurre para el caso de la división por cero?
     - ¿cuál es su semántica?

2.a. Agregar los constructores sintácticos correspondientes al lenguaje
     imperativo simple: newvar, asignación, while, sentencia condicional y
     composición.
2.b. Implementar su función semántica. ¿quién representa a ⊥ en la
     implementación? ¿Cuál es una posible definición de bot :: Ω?

3.a. Agregar los constructores sintácticos para extender el lenguaje con fallas.
3.b. Implementar su función semántica.

4.a. Agregar los constructores sintácticos para extender el lenguaje con
     input-output
4.b. Implementar su función semántica.

## Ejemplos ##

Asumiendo algunos nombres de constructores.

**Ejemplo 1**
while x < 10 do
  !x ;
  x := x + 1
od

ej1 :: Expr Ω
ej1 = While (Lt (Var "x") (Const 10)) $
            Seq (SOut $ Var "x")
                (Assign "x" (Plus (Var "x") (Const 1)))

eval_ej1 :: IO ()
eval_ej1 = eval ej1 (\_ -> 0)

**Ejemplo 2**
while y < 10 do
  ?x ;
  !x ;
  !y ;
  y := y + 1
od

ej2 :: Expr Ω
ej2 = While (Lt (Var "y") (Const 10)) $
            Seq (Seq (Seq (SIn "x")
                          (SOut $ Var "x")
                     )
                     (SOut $ Var "y")
                )
                (Assign "y" (Plus (Var "y") (Const 1)))

eval_ej2 :: IO ()
eval_ej2 = eval ej2 (\_ -> 0)

**Ejemplo 3**
?x ;
newvar x := 10 in !x end ;
!x

ej3 :: Expr Ω
ej3 = Seq (Seq (SIn "x")
               (Newvar "x" (Const 10)
                       (SOut $ Var "x")
               )
          )
          (SOut $ Var "x")

eval_ej3 :: IO ()
eval_ej3 = eval ej3 (\_ -> 0)

## Uso ##

```console
$ ghci Lab.hs
*Main> eval_ej1
0
1
2
3
4
5
6
7
8
9
*Main>
```
