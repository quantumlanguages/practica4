{--
Practica 4
El lenguaje MiniHS (EAB extendido con cáculo lambda). Semántica
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

--normal cambiado
--Falta agregar el fix en los eval
--Pura semántica dinamica
--eval le pide al algoritmo de inferencia y pide el contexto vacío

module BAE.Dynamic where

  import Data.List

  import  BAE.Sintax as Sintax
  import  BAE.Static as Static
  import  BAE.Type as Type


  -- | Determina si una expresión está en forma normal, es decir,
  --no se pueden hacer más beta reducciones.
  normal :: Expr -> Bool
  normal (Fn _ e) = normal e
  normal (Fix _ _) = False
  normal (App (Fn _ _) e2) = False
  normal (App e1 e2) = (normal e1) && (normal e2)
  normal _ = False

  -- | Devuelve la transición tal que eval1 e = e' syss e -> e' .
  eval1 :: Expr -> Expr
  eval1 expr =
    case expr of
      I n -> error "blocked state: integer"
      B p -> error "blocked state: boolean"
      V x -> error "blocked state: variable"
      Add (I n) (I m) -> I (n + m)
      Add (I n) e -> let e' = eval1 e in Add (I n) e'
      Add e1 e2 -> let e1' = eval1 e1 in Add e1' e2
      Mul (I n) (I m) -> I (n * m)
      Mul (I n) e -> let e' = eval1 e in Mul (I n) e'
      Mul e1 e2 -> let e1' = eval1 e1 in Mul e1' e2
      Succ (I n) -> I (n + 1)
      Succ e -> Succ (eval1 e)
      Pred (I 0) -> I 0
      Pred (I n) -> I (n - 1)
      Pred e -> Pred (eval1 e)
      Not (B p) -> B (not p)
      Not e -> Not (eval1 e)
      And (B p) (B q) -> B (p && q)
      And (B p) e -> let e' = eval1 e in And (B p) e'
      And e1 e2 -> let e1' = eval1 e1 in And e1' e2
      Or (B p) (B q) -> B (p || q)
      Or (B p) e -> let e' = eval1 e in Or (B p) e'
      Or e1 e2 -> let e1' = eval1 e1 in Or e1' e2
      Lt (I n) (I m) -> B (n < m)
      Lt (I n) e -> let e' = eval1 e in Lt (I n) e'
      Lt e1 e2 -> let e1' = eval1 e1 in Lt e1' e2
      Gt (I n) (I m) -> B (n > m)
      Gt (I n) e -> let e' = eval1 e in Gt (I n) e'
      Gt e1 e2 -> let e1' = eval1 e1 in Gt e1' e2
      Eq (I n) (I m) -> B (n == m)
      Eq (I n) e -> let e' = eval1 e in Eq (I n) e'
      Eq e1 e2 -> let e1' = eval1 e1 in Eq e1' e2
      If (B q) e1 e2 -> if q then e1 else e2
      If e1 e2 e3 -> If (eval1 e1) e2 e3
      Let i e1 e2 ->
        if locked e1
          then subst e2 (i, e1)
          else Let i (eval1 e1) e2
      Fn x e1 ->  Fn x (eval1 e1)
      App f@(Fn x e3) e2 ->
        if locked e2
          then subst e3 (x, e2)
          else App f (eval1 e2)
      App e1 e2 -> App (eval1 e1) e2

  -- | Indica si la transicion a evaluar esta bloqueada.
  locked :: Expr -> Bool
  locked expr =
    case expr of
      I n -> True
      B p -> True
      V x -> True
      Add (I _) (I _) -> False
      Add (I _) e -> locked e
      Add e1 e2 -> locked e1
      Mul (I _) (I _) -> False
      Mul (I _) e -> locked e
      Mul e1 e2 -> locked e1
      Succ (I _) -> False
      Succ e -> locked e
      Pred (I 0) -> False
      Pred (I n) -> False
      Pred e -> locked e
      Not (B p) -> False
      Not e -> locked e
      And (B p) (B q) -> False
      And (B p) e -> locked e
      And e1 e2 -> locked e1
      Or (B p) (B q) -> False
      Or (B p) e -> locked e
      Or e1 e2 -> locked e1
      Lt (I n) (I m) -> False
      Lt (I n) e -> locked e
      Lt e1 e2 -> locked e1
      Gt (I n) (I m) -> False
      Gt (I n) e -> locked e
      Gt e1 e2 -> locked e1
      Eq (I n) (I m) -> False
      Eq (I n) e -> locked e
      Eq e1 e2 -> locked e1
      If (B q) e1 e2 -> False
      If e1 e2 e3 -> locked e1
      Let i e1 e2 -> False
      Fn i e1 -> locked e1
      App e1 e2 ->
        if locked e1
          then
            if locked e2
              then case e1 of
                Fn _ _ -> False
                _ -> True
              else False
          else False

  -- | Devuelve la transición tal que eval1 e = e' syss e ->* e' y e' esta bloqueado.
  evals :: Expr -> Expr
  evals expr =
    if locked expr
      then expr
      else evals (eval1 expr)

  -- | Devuelve la transición tal que eval1 e = e' syss e ->* e' y e' es un valor.
  evale :: Expr -> Expr
  evale ex =
    case evals ex of
      I n -> I n
      B p -> B p
      V x -> error "[Var] Unasigned variable"
      Add _ _ -> error "[Add] Expected two Integer"
      Mul _ _ -> error "[Mul] Expected two Integer"
      Succ _ -> error "[Succ] Expected one Integer"
      Pred _ -> error "[Pred] Expected one Integer"
      Not _ -> error "[Not] Expected one Boolean"
      And _ _ -> error "[And] Expected two Boolean"
      Or _ _ -> error "[Or] Expected two Boolean"
      Lt _ _ -> error "[Lt] Expected two Integer"
      Gt _ _ -> error "[Gt] Expected two Integer"
      Eq _ _ -> error "[Eq] Expected two Integer"
      If _ _ _ -> error "[If] Expected one Boolean as first argument"
      Let _ _ _ -> error "[Let] Expected one value as variable asigment"
      Fn _ _ -> error "[Fn] Expected argument"
      App _ _ -> error "[App] Expected function as first argument"

{--
  -- | Verifica el tipado de un programa tal que vt F e T = True syss F |- e : T.
  vt :: Ctx -> Expr -> Type -> Bool
  vt ctx (V i) t = searchDecl ctx i t
  vt ctx (If e1 e2 e3) t = (vt ctx e1 Boolean) && (vt ctx e1 t) && (vt ctx e1 t)
  vt ctx (Let i e1 e2) t =
      if (vt ctx e1 Integer)
        then vt ((i, Integer):ctx) e2 t
        else vt ((i, Boolean):ctx) e2 t
  vt ctx e t =
    case t of
      Integer -> case e of
        I n -> True
        Add e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Mul e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Succ e -> vt ctx e t
        Pred e -> vt ctx e t
        _ -> False
      Boolean -> case e of
        B p -> True
        Not e -> vt ctx e t
        And e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Or e1 e2 -> (vt ctx e1 t) && (vt ctx e2 t)
        Lt e1 e2 -> (vt ctx e1 Integer) && (vt ctx e2 Integer)
        Gt e1 e2 -> (vt ctx e1 Integer) && (vt ctx e2 Integer)
        Eq e1 e2 -> (vt ctx e1 Integer) && (vt ctx e2 Integer)
        _ -> False

  -- | Busca la declaración de una variable en un contexto.
  searchDecl :: Ctx -> Identifier -> Type -> Bool
  searchDecl [] _ _  = False
  searchDecl ((i', t'):xs) i t =
    if i == i'
      then t == t'
      else searchDecl xs i t
--}

  -- | Verifica el tipado de un programa, y en caso de ser correcto lo evalúa hasta obtener un valor.
  eval :: Expr -> Type -> Expr
  eval e t = let (g, t') = infer e
             in
                if (g /= [] ) then
                  error "Expression with unbound variables"
                else if (t' /= t) then
                  error "Type error"
                else
                  evale e
