{--
Practica 5
El lenguaje MiniC (MiniHS con efectos). Semántica
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Dynamic where

  import BAE.Sintax
  import BAE.Memory
  import qualified BAE.Static as Static
  import qualified BAE.Type as Type

  -- | Indica si una expresión está bloqueada
  blocked :: Expr -> Bool
  blocked expr =
      case expr of
      I n -> True
      B p -> True
      V x -> True
      L i -> True
      Void -> True
      Add (I _) (I _) -> False
      Add (I _) e -> blocked e
      Add e1 e2 -> blocked e1
      Mul (I _) (I _) -> False
      Mul (I _) e -> blocked e
      Mul e1 e2 -> blocked e1
      Succ (I _) -> False
      Succ e -> blocked e
      Pred (I 0) -> False
      Pred (I n) -> False
      Pred e -> blocked e
      Not (B p) -> False
      Not e -> blocked e
      And (B p) (B q) -> False
      And (B p) e -> blocked e
      And e1 e2 -> blocked e1
      Or (B p) (B q) -> False
      Or (B p) e -> blocked e
      Or e1 e2 -> blocked e1
      Lt (I n) (I m) -> False
      Lt (I n) e -> blocked e
      Lt e1 e2 -> blocked e1
      Gt (I n) (I m) -> False
      Gt (I n) e -> blocked e
      Gt e1 e2 -> blocked e1
      Eq (I n) (I m) -> False
      Eq (I n) e -> blocked e
      Eq e1 e2 -> blocked e1
      If (B q) e1 e2 -> False
      If e1 e2 e3 -> blocked e1
      Let i e1 e2 -> False
      Fn i e1 -> True
      Fix _ _ -> False
      App e1 e2 ->
          if blocked e1
          then
              if blocked e2
              then case e1 of
                  Fn _ _ -> False
                  _ -> True
              else False
          else False
      Alloc e -> False
      Deref e -> False
      Assig e1 e2 -> False
      Seq Void e2 -> False
      Seq e1 e2 -> blocked e1
      While e1 e2 -> False

  -- | Devuelve la transición tal que eval1 e = e’ syss e -> e
  eval1 :: (Memory, Expr) -> (Memory, Expr)
  eval1 (mem, expr) =
    case expr of
      I n -> error "blocked state: integer"
      B p -> error "blocked state: boolean"
      V x -> error "blocked state: variable"
      L _ -> error "blocked state: reference"
      Void -> error "blocked state: void"
      Add (I n) (I m) -> sM $ I (n + m)
      Add (I n) e -> let (mem', e') = eval1' e in (mem', Add (I n) e')
      Add e1 e2 -> let (mem', e1') = eval1' e1 in (mem', Add e1' e2)
      Mul (I n) (I m) -> sM $ I (n * m)
      Mul (I n) e -> let (mem', e') = eval1' e in (mem', Mul (I n) e')
      Mul e1 e2 ->let (mem', e1') = eval1' e1 in (mem', Mul e1' e2)
      Succ (I n) -> sM $ I (n + 1)
      Succ e -> let (mem', e') = eval1' e in (mem', Succ (e'))
      Pred (I 0) -> sM $ I 0
      Pred (I n) -> sM $ I (n - 1)
      Pred e -> let (mem', e') = eval1' e in (mem', Pred (e'))
      Not (B p) -> sM $ B (not p)
      Not e -> let (mem', e') = eval1' e in (mem', Not (e'))
      And (B p) (B q) -> sM $ B (p && q)
      And (B p) e -> let (mem', e') = eval1' e in (mem', And (B p) e')
      And e1 e2 ->let (mem', e1') = eval1' e1 in (mem', And e1' e2)
      Or (B p) (B q) -> sM $ B (p || q)
      Or (B p) e -> let (mem', e') = eval1' e in (mem', Or (B p) e')
      Or e1 e2 ->let (mem', e1') = eval1' e1 in (mem', Or e1' e2)
      Lt (I n) (I m) -> sM $ B (n < m)
      Lt (I n) e -> let (mem', e') = eval1' e in (mem', Lt (I n) e')
      Lt e1 e2 ->let (mem', e1') = eval1' e1 in (mem', Lt e1' e2)
      Gt (I n) (I m) -> sM $ B (n > m)
      Gt (I n) e -> let (mem', e') = eval1' e in (mem', Gt (I n) e')
      Gt e1 e2 ->let (mem', e1') = eval1' e1 in (mem', Gt e1' e2)
      Eq (I n) (I m) -> sM $ B (n == m)
      Eq (I n) e -> let (mem', e') = eval1' e in (mem', Eq (I n) e')
      Eq e1 e2 ->let (mem', e1') = eval1' e1 in (mem', Eq e1' e2)
      If (B q) e1 e2 -> sM $ if q then e1 else e2
      If e1 e2 e3 -> let (mem', e1') = eval1' e1 in (mem', If e1' e2 e3)
      Let x (Fix y e1) e2 -> (mem, subst e2 (x, Fix y e1))
      Let x (Fn y e1) e2 -> (mem, subst e2 (x, Fn y e1))
      Let i e1 e2 ->
        if blocked e1
          then sM $ subst e2 (i, e1)
          else let (mem', e1') = eval1' e1 in (mem', Let i e1' e2)
      Fn x e1 -> let (mem', e1') = eval1' e1 in (mem', Fn x e1')
      Fix f e1 -> sM $ subst e1 (f, Fix f e1)
      App f@(Fn x e3) e2 ->
        if blocked e2
          then sM $ subst e3 (x, e2)
          else let (mem', e2') = eval1' e2 in (mem', App f e2')
      App e1 e2 -> let (mem', e1') = eval1' e1 in (mem', App e1' e2)
      Seq Void e -> sM $ e
      Seq e1 e2 -> let (mem', e1') = eval1' e1 in (mem', Seq e1' e2)
      While e1 e2 -> sM $ If e1 (Seq e2 (While e1 e2)) Void
      Alloc e ->
        if blocked e
          then let l = newAddress mem in
            case l of
              L i ->
                case e of
                  I n -> (((i, e):mem), l)
                  B p -> (((i, e):mem), l)
                  Fn x e -> (((i, e):mem), l)
                  L i -> (((i, e):mem), l)
                  _ -> error "Memory can only store values"
              _ -> error "Invalid new address"
          else let (mem', e') = eval1' e in (mem', Alloc e')
      Deref (L i) ->
        case access i mem of
          Just v -> (mem, v)
          Nothing -> error "Value not found"
      Deref e -> let (mem', e') = eval1' e in (mem', Deref e')
      Assig (L i) e2 ->
        if blocked e2
          then
            case update (i, e2) mem of
              Just m -> (m, Void)
              Nothing -> error "Unasigned reference"
          else let (mem', e2') = eval1' e2 in (mem', Assig (L i) e2')
      Assig e1 e2 -> let (mem', e1') = eval1' e1 in (mem', Assig e1' e2)
    where eval1' = (\e -> eval1 (mem, e)); sM = (\x -> (mem, x))

  -- | Devuelve la transición tal que evals e = e’ syss e ->∗ e0 y e0 está bloqueado.
  evals :: (Memory, Expr) -> (Memory, Expr)
  evals s@(_, expr) =
    if blocked expr
      then s
    else evals (eval1 s)

  -- | Devuelve la evaluación de un programa tal que evale e = e’ syss e ->∗e0 y e0 es un valor.
  evale :: Expr -> Expr
  evale ex =
    let (m, ex') = evals ([], ex)
      in
        case ex' of
          I n -> I n
          B p -> B p
          Void -> Void
          V x -> error "[Var] Unasigned variable"
          L i -> error "[L] Unused reference"
          Alloc _ -> error "[Alloc] Expected value"
          Deref _ -> error "[Deref] No value to dereference"
          Assig _ _ -> error "[Assig] Expected L and value"
          Seq _ _ -> error "[Seq] Expected two Void"
          While _ _ -> error "[While] Expected one Boolean and one Void"
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

  -- | Revisa el tipo y evalua la expresión si es correcto
  eval :: Expr -> Type.Type -> Expr
  eval e t =
    let (ctx, t') = Static.infer e
      in
        if ctx /= [] then error ("Expression with unbounded variables: " ++ (show ctx))
        else
          if (t /= t')
            then error ("Type error: " ++ (show t) ++ " is not " ++ (show t'))
            else evale e
