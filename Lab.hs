-- Walter Andre Silva

{-# LANGUAGE GADTs #-}

--         ∞
-- fix f = ⊔ fⁱ ⊥
--        i=0
fix :: (a -> a) -> a
fix f = f (fix f)

type Iden = String
type Σ = Iden -> Int

update :: Σ -> Iden -> Int -> Σ
update σ v n v' = if v == v' then n else σ v'

{- Ω ≈ (Σ' + Z × Ω + Z → Ω)⊥ -}
data Ω = Normal Σ | Abort Σ | Out (Int, Ω) | In (Int -> Ω)
{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
   * Out    : (Z, Ω) → Ω
   * In     : (Z → Ω) → Ω
-}

data Expr a where
  -- Expresiones enteras
  ConstI :: Int      -> Expr Int                      -- n
  Var    :: String   -> Expr Int                      -- v
  Plus   :: Expr Int -> Expr Int -> Expr Int          -- e + e'
  Res    :: Expr Int -> Expr Int -> Expr Int          -- e - e'
  Mul    :: Expr Int -> Expr Int -> Expr Int          -- e * e'
  Div    :: Expr Int -> Expr Int -> Expr Int          -- e / e'
  DivΩ   :: Expr Int -> Expr Int -> Expr Ω            -- e / e'
  Mod    :: Expr Int -> Expr Int -> Expr Int          -- e % e' 
  ModΩ   :: Expr Int -> Expr Int -> Expr Ω            -- e % e' 
  Neg    :: Expr Int -> Expr Int                      -- -e
  -- Expresiones booleanas
  ConstB :: Bool     -> Expr Bool                     -- b
  Eq     :: Expr Int -> Expr Int -> Expr Bool         -- e = e'
  Dif    :: Expr Int -> Expr Int -> Expr Bool         -- e /= e'
  Lt     :: Expr Int -> Expr Int -> Expr Bool         -- e < e'
  Le     :: Expr Int -> Expr Int -> Expr Bool         -- e <= e'
  Gt     :: Expr Int -> Expr Int -> Expr Bool         -- e > e'
  Ge     :: Expr Int -> Expr Int -> Expr Bool         -- e >= e'
  And    :: Expr Bool -> Expr Bool -> Expr Bool       -- e ∧ e'
  Or     :: Expr Bool -> Expr Bool -> Expr Bool       -- e ∨ e'
  Not    :: Expr Bool -> Expr Bool                    -- ¬ e
  -- Comandos
  Skip   :: Expr Ω                                    -- skip
  Newvar :: String -> Expr Int -> Expr Ω -> Expr Ω    -- newvar v := e in e'
  Assign :: String -> Expr Int -> Expr Ω              -- v := e 
  Fail   :: Expr Ω                                    -- fail
  Catch  :: Expr Ω -> Expr Ω -> Expr Ω                -- catch c with c'
  While  :: Expr Bool -> Expr Ω -> Expr Ω             -- while b do c
  If     :: Expr Bool -> Expr Ω -> Expr Ω -> Expr Ω   -- if b then c else c'
  Seq    :: Expr Ω -> Expr Ω -> Expr Ω                -- c ; c'
  SOut   :: Expr Int -> Expr Ω                        -- !e
  SIn    :: String -> Expr Ω                          -- ?v

    
class DomSem dom where 
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (ConstI a)   _ = a
  sem (Var v)      σ = σ v
  sem (Plus e1 e2) σ = sem e1 σ + sem e2 σ
  -- Agrego 
  sem (Res e1 e2) σ = sem e1 σ - sem e2 σ
  sem (Mul e1 e2) σ = sem e1 σ * sem e2 σ
  sem (Div e1 e2) σ = div (sem e1 σ) (sem e2 σ)
  sem (Mod e1 e2) σ = mod (sem e1 σ) (sem e2 σ)
  sem (Neg e1)    σ = -(sem e1 σ)     

instance DomSem Bool where
  sem (Eq e1 e2) σ = sem e1 σ == sem e2 σ
  -- Agrego
  sem (ConstB a)  _ = a
  sem (Dif e1 e2) σ = sem e1 σ /= sem e2 σ
  sem (Lt e1 e2)  σ = sem e1 σ < sem e2 σ
  sem (Le e1 e2)  σ = sem e1 σ <= sem e2 σ
  sem (Gt e1 e2)  σ = sem e1 σ > sem e2 σ
  sem (Ge e1 e2)  σ = sem e1 σ >= sem e2 σ
  sem (And e1 e2) σ = sem e1 σ && sem e2 σ
  sem (Or e1 e2)  σ = sem e1 σ || sem e2 σ
  sem (Not e1)    σ = not (sem e1 σ)

(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ)  = f σ
(*.) _ (Abort σ)   = Abort σ
(*.) f (Out (n,ω)) = Out (n, f *. ω)
(*.) f (In g)      = In ((f *.) . g)

(†.) :: (Σ -> Σ) -> Ω -> Ω
(†.) f (Normal σ)  = Normal $ f σ
(†.) f (Abort σ)   = Abort $ f σ
(†.) f (Out (n,ω)) = Out (n, f †. ω)
(†.) f (In g)      = In ((f †.) . g)

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ)  = Normal σ
(+.) f (Abort σ)   = f σ
(+.) f (Out (n,ω)) = Out (n, f +. ω)
(+.) f (In g)      = In ((f +.) . g)

instance DomSem Ω where
  sem Skip σ = Normal σ
  -- Agrego
  sem (Newvar s v e1) σ = (†.) res (sem e1 (update σ  s (sem v σ )))                                         
                            where res σ' = (update σ' s (σ s) )          
  sem (Assign  s e) σ   = Normal(update σ s (sem e σ))                       
  sem Fail σ            = Abort σ 
  sem (If e1 e2 e3)  σ  = if (sem e1 σ) then (sem e2 σ) else (sem e3 σ)
  sem (Catch e1 e2) σ   = (+.) (sem e2 ) (sem e1 σ) 
  sem (While b e) σ     = fix f σ  
                            where f b' σ' | sem b σ' = (*.) b' (sem e σ')
                                          | otherwise = Normal σ' 
  sem (Seq e1 e2) σ = (*.) (sem e2) (sem e1 σ)  
  sem (SOut v) σ    = Out ((sem v σ), (Normal σ))                                                       
  sem (SIn v) σ     = In (\n -> (Normal(update σ v n)))

  sem (DivΩ e1 e2) σ = if (sem e2 σ) == 0
                        then Abort σ
                        else Out (div (sem e1 σ) (sem e2 σ),  Normal σ)  
  sem (ModΩ e1 e2) σ = if (sem e2 σ) == 0
                        then Abort σ
                        else Out (mod (sem e1 σ) (sem e2 σ),  Normal σ) 

{- ################# Funciones de evaluación de dom ################# -}

class Eval dom where 
  eval :: Expr dom -> Σ -> IO ()

instance Eval Int where
  eval e = print . sem e

instance Eval Bool where
  eval e = print . sem e

instance Eval Ω where
  eval e = unrollOmega . sem e
    where unrollOmega :: Ω -> IO ()
          unrollOmega (Normal σ)   = return ()
          unrollOmega (Abort σ)    = putStrLn "Abort"
          unrollOmega (Out (n, ω)) = print n >> unrollOmega ω
          unrollOmega (In f)       = getLine >>= unrollOmega . f . read
         
{- ################# Ejercicios ################# -}

eval_intexp_ej1 :: IO ()
eval_intexp_ej1 = eval (Plus (ConstI 2) (ConstI 2)) (\_ -> 0)

eval_intexp_ej2 :: IO ()
eval_intexp_ej2 = eval (Div (ConstI 2) (ConstI 0)) (\_ -> 0)

eval_intexp_ej3 :: IO ()
eval_intexp_ej3 = eval (DivΩ (ConstI 3) (ConstI 0)) (\_ -> 0)

eval_intexp_ej4 :: IO ()
eval_intexp_ej4 = eval (If (Eq (Var "x") (ConstI 0)) (Fail) (SOut $ Div (Var "x") (ConstI 2))) (\_ -> 1)

--------------------------------------------------------------------------------------------
ej1 :: Expr Ω
ej1 = While (Lt (Var "x") (ConstI 10)) $
            Seq (SOut $ Var "x")
                (Assign "x" (Plus (Var "x") (ConstI 1)))

eval_ej1 :: IO ()
eval_ej1 = eval ej1 (\_ -> 0)

--------------------------------------------------------------------------------------------
ej2 :: Expr Ω
ej2 = While (Lt (Var "y") (ConstI 10)) $
            Seq (Seq (Seq (SIn "x")
                          (SOut $ Var "x")
                     )
                     (SOut $ Var "y")
                )
                (Assign "y" (Plus (Var "y") (ConstI 1)))

eval_ej2 :: IO ()
eval_ej2 = eval ej2 (\_ -> 0)

--------------------------------------------------------------------------------------------
ej3 :: Expr Ω
ej3 = Seq (Seq (SIn "x")
               (Newvar "x" (ConstI 10)
                       (SOut $ Var "x")
               )
          )
          (SOut $ Var "x")

eval_ej3 :: IO ()
eval_ej3 = eval ej3 (\_ -> 0)

----------------------------------------------------------------------------------------------
-- Termina el ciclo antes si se introduce le valor 5
ej4 :: Expr Ω
ej4 = While (And (Lt (Var "y") (ConstI 10)) (Dif (Var "x") (ConstI 5))) $
            Seq (Seq (Seq (SIn "x")
                          (SOut $ Var "x")
                     )
                     (SOut $ Var "y")
                )
                (Assign "y" (Plus (Var "y") (ConstI 1)))

eval_ej4 :: IO ()
eval_ej4 = eval ej4 (\_-> 0)


{-Respuestas 

Dividir por cero sin ningun tipo de control previo:
*** Exception: divide by zero
La semantica de dividir por cero deberia ser Abort σ, por lo tanto devuelvo un comportamiento.


Para el simbolo de no terminación (⊥) lo podemos representar como Abort.
Los operadores de transferencia de control (*, †, +) nos permite propagar el botton.
Una posible definicion seria: 
Bot :: Ω
sem Bot σ = Abort σ

-}