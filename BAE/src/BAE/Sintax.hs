{--
Practica 4
El lenguaje MiniHS (EAB extendido con cáculo lambda). Sintaxis
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

--Agregado el Fix y alphaEq

module BAE.Sintax where

    -- Importando algunas funciones útiles de listas
    import Data.List
    import Text.Read

    -- Extendiendo la intaxis

    -- | Renombrando String a Identificador para usar texto como el nombre de las variables.
    type Identifier = String

    -- | Definiendo las expresiones del lenguaje, igual que antes pero ahora con
    -- variables
    data Expr = V Identifier | I Int | B Bool -- ^ Expresiones basicas
                | Fix Identifier Expr -- ^Expresion fix
                | Add Expr Expr | Mul Expr Expr -- ^ Operaciones aritmeticas binarias
                | Succ Expr | Pred Expr -- ^ Operaciones aritmeticas unarias
                | Not Expr | And Expr Expr | Or Expr Expr -- ^ Operaciones logicas
                | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr -- ^ Operaciones de comparacion
                | If Expr Expr Expr -- ^ Operacion If
                | Let Identifier Expr Expr -- ^ Declaracion y ligado de variables
                | Fn Identifier Expr -- ^ Funciones lambda
                | App Expr Expr -- ^ Aplicacion de funciones
                deriving (Eq)

    -- | Implementando la clase Show para hacer la representación más estética
    instance Show Expr where
      show e = case e of
            (V x) -> "V[" ++ x ++ "]"
            (I n) -> "N[" ++ (show n) ++ "]"
            (B b) -> "B[" ++ (show b) ++ "]"
            (Fix x e1) -> "fix(" ++ x ++ "." ++ (show e1) ++ ")"
            (Add e1 e2) -> "add("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Mul e1 e2) -> "mul("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Succ e1) -> "suc(" ++ (show e1) ++ ")"
            (Pred e1) -> "pred(" ++ (show e1) ++ ")"
            (Not e1) -> "not(" ++ (show e1) ++ ")"
            (And e1 e2) -> "and["++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Or e1 e2) -> "or("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Lt e1 e2) -> "lt("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Gt e1 e2) -> "gt("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (Eq e1 e2) -> "eq("++ (show e1) ++ " , " ++ (show e2) ++ ")"
            (If ec e1 e2) -> "if("++ (show ec) ++ " , " ++ (show e1) ++ " , "
                           ++ (show e2) ++ ")"
            (Let x e1 e2) -> "let(" ++ (show e1) ++ " , " ++ (show x) ++ "." ++ (show e2) ++ ")"
            (Fn x e1) -> "fn(" ++ x ++ "." ++ (show e1) ++ ")"
            (App e1 e2) -> "app(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"

    -- | La asignacion de variables sera emulada usando substitucion textual
    type Substitution = (Identifier, Expr)

    -- | Obteniendo variables libres de una expresion
    frVars :: Expr -> [Identifier]
    frVars ex =
        case ex of
            (V x) -> [x]
            (I _) -> []
            (B _) -> []
            (Fix i e) -> (frVars e) \\ [i]
            (Add e f) -> union (frVars e) (frVars f)
            (Mul e f) -> union (frVars e) (frVars f)
            (Succ e) -> frVars e
            (Pred e) -> frVars e
            (Not e) -> frVars e
            (And e f) -> union (frVars e) (frVars f)
            (Or e f) -> union (frVars e) (frVars f)
            (Lt e f) -> union (frVars e) (frVars f)
            (Gt e f) -> union (frVars e) (frVars f)
            (Eq e f) -> union (frVars e) (frVars f)
            (If e f g) -> union (union (frVars e) (frVars f)) (frVars g)
            (Let i e f) -> union (frVars e) ((frVars f) \\ [i])
            (Fn i e) -> (frVars e) \\ [i]
            (App e f) -> union (frVars e) (frVars f)

    -- | Incrementa el sufijo numerico de un identificador. Si no hay valor numerico
    -- presente, entonces añade '1' al final del identificador.
    incrVar :: Identifier -> Identifier
    incrVar x = incrVarAux [] x

    -- | Implementando recursion de cola
    -- Usa 'Text.Read.readMaybe' para intentar analizar el sufijo del identificador.
    incrVarAux :: Identifier -> Identifier -> Identifier
    incrVarAux a [] = a ++ "1"
    incrVarAux a y@(x:xs) =
        case readMaybe y of
            Nothing -> incrVarAux (a ++ [x]) xs
            Just n -> a ++ (show ((n+1) :: Integer))

    -- | Obteniendo una variable no disponible en la expresion como variable libre
    safeName :: Identifier -> Expr -> Identifier
    safeName x e =
        let x' = (incrVar x) in
            if elem x' (frVars e)
                then safeName x' e
                else x'

    -- | Funcion que realiza alpha reduccion
    alphaExpr :: Expr -> Expr
    alphaExpr ex =
        case ex of
            Let x e1 e2 ->
                let x' = safeName x e2; e2' = subst e2 (x, V x') in
                    Let x' e1 e2'
            Fn x e ->
                let x' = safeName x e; e' = subst e (x, V x') in
                    Fn x' e'
            Fix x e ->
                let x' = safeName x e; e' = subst e (x, V x') in
                    Fix x' e'
            _ -> ex


    -- | Aplicando substitucion si es semanticamente posible
    subst :: Expr -> Substitution -> Expr
    subst ex s@(y, e') =
        case ex of
            (V x) ->
                if x == y then e' else ex
            (I _) -> ex
            (B _) -> ex
            (Fix x e) ->
                if x == y || elem x (frVars e')
                    then st (alphaExpr ex)
                    else Fix x (st e)
            (Add e f) -> Add (st e) (st f)
            (Mul e f) -> Mul (st e) (st f)
            (Succ e) -> Succ (st e)
            (Pred e) -> Pred (st e)
            (Not e) -> Not (st e)
            (And e f) -> And (st e) (st f)
            (Or e f) -> Or (st e) (st f)
            (Lt e f) -> Lt (st e) (st f)
            (Gt e f) -> Gt (st e) (st f)
            (Eq e f) -> Eq (st e) (st f)
            (If e f g) -> If (st e) (st f) (st g)
            (Let x e f) ->
                if x == y || elem x (frVars e')
                    then st (alphaExpr ex)
                    else Let x (st e) (st f)
            (Fn x e) ->
                if x == y || elem x (frVars e')
                    then st (alphaExpr ex)
                    else Fn x (st e)
            (App e f) -> App (st e) (st f)
        where st = (flip subst) s

    -- | Dice si dos expresiones son alpha equivalentes
    alphaEq :: Expr -> Expr -> Bool
    alphaEq (V x) (V y) = x == y
    alphaEq (I x) (I y) = x == y
    alphaEq (B x) (B y) = x == y
    alphaEq (Fn x e1) (Fn y e2) = alphaEq e1 (subst e2 (y, V x))
    alphaEq (Fix x e1) (Fix y e2) = alphaEq e1 (subst e2 (y, V x))
    alphaEq (Add e11 e12) (Add e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (Mul e11 e12) (Mul e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (Succ e1) (Succ e2) = (alphaEq e1 e2)
    alphaEq (Pred e1) (Pred e2) = (alphaEq e1 e2)
    alphaEq (Not e1) (Not e2) = (alphaEq e1 e2)
    alphaEq (And e11 e12) (And e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (Or e11 e12) (Or e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (Lt e11 e12) (Lt e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (Gt e11 e12) (Gt e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (Eq e11 e12) (Eq e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (App e11 e12) (App e21 e22) = (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (If e1c e11 e12) (If e2c e21 e22) = 
        (alphaEq e1c e2c) && (alphaEq e11 e21) && (alphaEq e12 e22)
    alphaEq (Let x e11 e12) (Let y e21 e22) = 
        (alphaEq e11 e21) && (alphaEq e12 (subst e22 (y, V x)))
    alphaEq _ _ = False
