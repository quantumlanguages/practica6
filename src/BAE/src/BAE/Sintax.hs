{--
Practica 6
El lenguaje MiniC con continuaciones. Sintaxis
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Sintax where

    -- Importando algunas funciones útiles de listas
    import Data.List
    import Text.Read

    -- Extendiendo la sintaxis

    -- | Renombrando String a Identificador para usar texto como el nombre de las variables.
    type Identifier = String

    type Stack = [Frame]

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
                | L Int -- ^ Referencias
                | Alloc Expr -- ^ Guardar en memoria
                | Deref Expr -- ^ Borrar de memeoria
                | Assig Expr Expr -- ^ Actualizar
                | Seq Expr Expr -- ^ Secuencia de instrucciones
                | While Expr Expr -- ^ Ciclo de control
                | Void
                | Raise Expr
                | Handle Expr Identifier Expr
                | Letcc Identifier Expr
                | Continue Expr Expr
                | Cont Stack
                | Error
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
            (L i) -> "L " ++ (show i) ++ ""
            (Alloc e1) -> "*(" ++ (show e1) ++ ")"
            (Deref e1) -> "&(" ++ (show e1) ++ ")"
            (Assig e1 e2) -> (show e1) ++ " := " ++ (show e2)
            (Void) -> "void"
            (Seq e1 e2) -> (show e1) ++ " ; " ++ (show e2)
            (While e1 e2) -> "while(" ++ (show e1) ++ ") do " ++ (show e2) ++ " end"
            (Raise e1) -> "raise(" ++ (show e1) ++ ")"
            (Handle e1 x e2) -> "handle " ++ (show e1) ++ "{"++ (show x) ++" => e2}"
            (Letcc x e1) -> "letcc(" ++ (show x) ++ "." ++ (show e1) ++ ")"
            (Continue e1 e2) -> "cont(" ++ (show e1) ++ (show e2) ++ ")"
            (Cont s) -> "cont(" ++ (show s) ++ ")"
            (Error) -> "error"

    -- | Tipo de marcos vacíos
    type Pending = ()

    -- | Tipo de marco
    data Frame = SuccF Pending
               | PredF Pending
               | NotF Pending
               | FnF Identifier Pending
               | AddFL Pending Expr
               | AddFR Expr Pending
               | MulFL Pending Expr
               | MulFR Expr Pending
               | AndFL Pending Expr
               | AndFR Expr Pending
               | OrFL Pending Expr
               | OrFR Expr Pending
               | LtFL Pending Expr
               | LtFR Expr Pending
               | GtFL Pending Expr
               | GtFR Expr Pending
               | EqFL Pending Expr
               | EqFR Expr Pending
               | AppFL Pending Expr
               | AppFR Expr Pending
               | IfF Pending Expr Expr
               | LetF Identifier Pending Expr
               | AllocF Pending -- ^ Guardar en memoria
               | DerefF Pending -- ^ Borrar de memeoria
               | AssigFL Pending Expr -- ^ Actualizar
               | AssigFR Expr Pending -- ^ Actualizar
               | SeqF Pending Expr -- ^ Secuencia de instrucciones
               | WhileF Pending Expr -- ^ Ciclo de control
               | RaiseF Pending
               | HandleF Pending Identifier Expr
               | ContinueFL Pending Expr
               | ContinueFR Expr Pending
               deriving (Eq)

    -- Show para marcos
    instance Show Frame where
        show ex =
          case ex of
            (SuccF _) -> "suc(-)"
            (PredF _) -> "pred(-)"
            (NotF _) -> "not(-)"
            (FnF _) -> "fn(-)"
            (AddFL _ e) -> "add(-, " ++ (show e) ++ ")"
            (AddFR e _) -> "add(" ++ (show e) ++ ", -)"
            (MulFL _ e) -> "mul(-, " ++ (show e) ++ ")"
            (MulFR e _) -> "mul(" ++ (show e) ++ ", -)"
            (AndFL _ e) -> "and(-, " ++ (show e) ++ ")"
            (AndFR e _) -> "and(" ++ (show e) ++ ", -)"
            (OrFL _ e) -> "or(-, " ++ (show e) ++ ")"
            (OrFR e _) -> "or(" ++ (show e) ++ ", -)"
            (LtFL _ e) -> "lt(-, " ++ (show e) ++ ")"
            (LtFR e _) -> "lt(" ++ (show e) ++ ", -)"
            (GtFL _ e) -> "gt(-, " ++ (show e) ++ ")"
            (GtFR e _) -> "gt(" ++ (show e) ++ ", -)"
            (EqFL _ e) -> "eq(-, " ++ (show e) ++ ")"
            (EqFR e _) -> "eq(" ++ (show e) ++ ", -)"
            (AppFL _, e2) -> "app(-, " ++ (show e2) ++ ")"
            (AppFR e1, _) -> "app(" ++ (show e1) ++ ", -)"
            (IfF _, e1, e2) -> "if(-, " ++ (show e1) ++ ", " ++ (show e2) ++ ")"
            (LetF x, _, e2) -> "let(" ++ (show x) ++ "- , " ++ (show e2) ++ ")"
            (AllocF _) -> "alloc(-)"
            (DerefF _) -> "deref(-)"
            (AssigFL _ e) -> "assig(-, " ++ (show e) ++ ")"
            (AssigFR e _) -> "assig(" ++ (show e) ++ ", -)"
            (SeqF _ e) -> "seq(-, " ++ (show e) ++ ")"
            (WhileF _ e) -> "while(-, " ++ (show e) ++ ")"
            (RaiseF _) -> "raise(-)"
            (HandleF _, x, e2) -> "handle(-, " ++ (show x) ++ ", " ++ (show e2) ++ ")"
            (ContinueFL _ e) -> "continue(-, " ++ (show e) ++ ")"
            (ContinueFR e _) -> "continue(" ++ (show e) ++ ", -)"
  

    -- | La asignacion de variables sera emulada usando substitucion textual
    type Substitution = (Identifier, Expr)

    -- | Obteniendo variables libres de una expresion(AddFL _ e) -> "add(-, " ++ (show e) ++ ")"
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
            (L _) -> []
            (Alloc e) -> frVars e
            (Deref e) -> frVars e
            (Assig e f) ->  union (frVars e) (frVars f)
            (Void) -> []
            (Seq e f) -> union (frVars e) (frVars f)
            (While e f) -> union (frVars e) (frVars f)
            (Raise e) -> frVars e
            (Handle i e f) -> union (frVars e) ((frVars f) \\ [i])
            (Letcc) ->
            (Continue e f) -> union (frVars e) (frVars f)

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
            (L _) -> ex
            (Alloc e) -> Alloc (st e)
            (Deref e) -> Deref (st e)
            (Assig e1 e2) -> Assig (st e1) (st e2)
            (Void) -> ex
            (Seq e f) -> Seq (st e) (st f)
            (While e f) -> While (st e) (st f)
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
    alphaEq (Cont e1) (Cont e2) = e1 == e2
    alphaEq _ _ = False
