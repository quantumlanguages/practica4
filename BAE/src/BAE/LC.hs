{--
Semanal 2
Cálculo Lambda
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}
module BAE.LC where
    --Importamos las funciones de data list
    import Data.List

    -- Vamos a importar funciones de text read para manejar strings y enteros
    import Text.Read

    --Renombramos el tipo de daros String a Identifier para representar al conjunto
    --de nombres de variables como cadenas de texto
    type Identifier = String

    --Definimos la sintaxis de las expresiones EAB
    data Expr = V Identifier | L  Identifier Expr | App Expr Expr deriving (Eq)

    --1. Crea una instancia de la clase Show para las expresiones
    --lambda utilizando la convención en el pdf.
    instance Show Expr where
        show e =  case e of
                (V x) -> x
                (L x e1) -> "\\" ++ x ++ " -> " ++ (show e1)
                (App e1 e2) -> "(" ++ (show e1) ++ " " ++ (show e2) ++ ")"

  --Definiremos el tipo sustitución del siguiente modo∷
    type Substitution = (Identifier, Expr)

    --Obtiene el conjunto de variables libres de una expresión.
    frVars :: Expr -> [Identifier]
    frVars (V x) = [x]
    --Quitamos las variables ligadas a la Lambda
    frVars (L x e) = (frVars e) \\ [x]
    frVars (App e1 e2) = union (frVars e1) (frVars e2)

    --Dado un identificador, si este no termina en número
    --le agrega el sufijo 1, en caso contrario toma el valor del número y lo
    --incrementa en 1.
    incrVar :: Identifier -> Identifier
    incrVar x = incrementa [] x

    -- Función auxiliar para incrementar indentificador
    -- Readmaybe Analiza una cadena usando la instancia de Read.
    incrementa :: Identifier -> Identifier -> Identifier
    incrementa e [] = e ++ "1"
    incrementa e (x:xs) =
        case readMaybe (x:xs) of
            --Si readMaybe regresa Nothing, significa que la cadena no termina en número
            Nothing -> incrementa (e ++ [x]) xs
            --Si readMaybe regresa Just, significa que la cadena termina en número y nos lo devuelve
            --Usamos show para convertir el numero en string
            Just n -> e ++ (show ((n+1) :: Integer))

    -- Revisamos que la variable nueva no este ya ligada y buscamos una nueva en caso que lo esté
    nombreNuevo :: Identifier -> Expr -> Identifier
    nombreNuevo x e =
      let y = (incrVar x) in
      if elem y (frVars e)  then nombreNuevo y e
      else y

    -- Toma una expresión lambda y devuelve una α-equivalente utilizando
    --la función incrVar hasta encontrar un nombre que no aparezca en el cuerpo.
    alphaExpr :: Expr -> Expr
    alphaExpr (L x e1) = L (nombreNuevo x e1) (subst e1 (x, V (nombreNuevo x e1)))
    alphaExpr e = e

    -- Aplica la sustitución a la expresión dada.
    subst :: Expr -> Substitution -> Expr
    subst e (y, a) =
        case e of
            V x -> if x == y then a else e
            L x e1 ->
                if x == y || elem x (frVars a)
                  --Aplicamos una alfa equivalencia en caso que no se pueda sustituir
                    then subst (alphaExpr e) (y, a)
                else L x (subst e1 (y, a))
            App e1 e2 -> App (subst e1 (y, a)) (subst e2 (y, a))

    -- Implementa la β-reducción.
    beta :: Expr -> Expr
    beta e =
        case e of
            V _ -> e
            L x e1 ->  L x (beta e1)
            --Analizamos e1 para ver en que caso entra
            App e1 e2 ->
                let e1' = (beta e1) in
                    case e1' of
                        L x a -> subst a (x, (beta e2))
                        _ -> App e1' (beta e2)

    -- Determina si una expresión está en forma normal, es decir,
    --no se pueden hacer más beta reducciones.
    normal :: Expr -> Bool
    normal (V _) = True
    normal (L _ e) = normal e
    normal (App (L _ _) e2) = False
    normal (App e1 e2) = (normal e1) && (normal e2)

    -- Evalúa una expresión lambda implementando las reglas definidas.
    eval :: Expr -> Expr
    eval e = if (normal e) then e
             else eval (beta e)
