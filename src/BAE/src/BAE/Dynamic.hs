{--
Practica 4
El lenguaje MiniHS (EAB extendido con cáculo lambda). Semántica
Autores:
Edgar Quiroz Castañeda
Sandra del Mar Soto Corderi
--}

module BAE.Dynamic where

  import BAE.Sintax
  import BAE.Memory
  import qualified BAE.Static as Static
  import qualified BAE.Type as Type


  -- | Tipo para estados
  data State = E (Memory, Stack, Expr) | R (Memory, Stack, Expr) 
              | P (Memory, Stack, Expr)
              deriving (Show)

  eval1 :: State -> State
  eval1 (E (m, s, e)) = case e of
                      -- valores
                      (V _) -> R (m, s, e)
                      (B _) -> R (m, s, e)
                      (I _) -> R (m, s, e)
                      (L _) -> R (m, s, e)
                      (Void) -> R (m, s, e)
                      (Cont _) -> R (m, s, e)
                      -- operadores unitarios
                      (Fn x e1) -> E (m, ((FnF x ()):s), e1)
                      (Fix x e1) -> E (m, s, subst e (x, Fix x e1))
                      (Succ e1) -> E (m, (SuccF ()):s, e1)
                      (Pred e1) -> E (m, (PredF ()):s, e1)
                      (Not e1) -> E (m, (NotF ()):s, e1)
                      (Alloc e1) -> E (m, (AllocF ()):s, e1)
                      (Deref e1) -> E (m, (DerefF ()):s, e1)
                      (Raise e1) -> E (m, (RaiseF ()):s, e1)
                      -- operadores binarios
                      (Add e1 e2) -> E (m, (AddFL () e2):s, e1)
                      (Mul e1 e2) -> E (m, (MulFL () e2):s, e1)
                      (And e1 e2) -> E (m, (AndFL () e2):s, e1)
                      (Or e1 e2) -> E (m, (OrFL () e2):s, e1)
                      (Lt e1 e2) -> E (m, (LtFL () e2):s, e1)
                      (Gt e1 e2) -> E (m, (GtFL () e2):s, e1)
                      (Eq e1 e2) -> E (m, (EqFL () e2):s, e1)
                      (App e1 e2) -> E (m, (EqFL () e2):s, e1)
                      (Assig e1 e2) -> E (m, (AssigFL () e2):s, e1)
                      (Seq e1 e2) -> E (m, (SeqF () e2):s, e1)
                      (While e1 e2) -> E (m, (WhileF () e2):s, e1)
                      (Continue e1 e2) -> E (m, (ContinueFL () e2):s, e1)
                      (Handle e1 i e2) -> E (m, (HandleF () i e2):s, e1)
                      --ternarias
                      (If e1 e2 e3) -> E (m, (IfF () e2 e3):s, e1)
                      (Let x e1 e2) -> E (m, (LetF x () e2):s, e1)
                      (Letcc x e1) -> E (m, s, subst e1 (x, Cont s))
                      _ -> P (m, s, e)
  eval1 (R (mem, s, e)) =
    case e of
      (V y) ->
        case s of
          ((FnF x _) : s') -> R (mem, s', Fn x e)
          ((LetF x _ e2) : s') -> E (mem, s', subst e2 (x, e))
          _ -> P (mem, s, Raise e)
      (I m) ->
        case s of
          ((SuccF _) : s') -> R (mem, s', I (succ m))
          ((PredF _) : s') -> R (mem, s', I (pred m))
          ((FnF x _) : s') -> R (mem, s', Fn x e)
          ((AddFL _ e2) : s') -> E (mem, ((AddFR e ()) : s'), e2)
          ((AddFR (I n) _) : s') -> R (mem, s', I (n+m))
          ((MulFL _ e2) : s') -> E (mem, ((MulFR e ()) : s'), e2)
          ((MulFR (I n) _) : s') -> R (mem, s', I (n*m))
          ((LtFL _ e2) : s') -> E (mem, ((LtFR e ()) : s'), e2)
          ((LtFR (I n) _) : s') -> R (mem, s', B (n<m))
          ((GtFL _ e2) : s') -> E (mem, ((GtFR e ()) : s'), e2)
          ((GtFR (I n) _) : s') -> R (mem, s', B (n>m))
          ((EqFL _ e2) : s') -> E (mem, ((EqFR e ()) : s'), e2)
          ((EqFR (I n) _) : s') -> R (mem, s', B (n==m))
          ((AppFR (Fn x e1) _) : s') -> E (mem, s', subst e1 (x, e))
          ((LetF x _ e2) : s') -> E (mem, s', subst e2 (x, e))
          ((AllocF _) : s') -> 
              let l = newAddress mem in 
                case l of 
                  (L i) -> R ((i, e):mem, s', l)
                  _ -> P (mem, s, Raise e)
          ((AssigFR (L i) _):s') -> 
            case update (i, e) mem of
              Just mem' -> R (mem', s', Void)
              Nothing -> P (mem, s, Raise e)
          ((RaiseF _) : s') -> P (mem, s, Raise e)
          ((HandleF _ x e2) : s') -> R (mem, s', e)
          ((ContinueFL _ e2) : s') -> E (mem, ((ContinueFR e ()):s'), e2)
          ((ContinueFR (Cont s'') _) : s') -> R (mem, s'', e)
          _ -> P (mem, s, Raise e)
      (B q) ->
        case s of
          ((NotF _) : s') -> R (mem, s', B (not q))
          ((FnF x _) : s') -> R (mem, s', Fn x e)
          ((AndFL _ e2) : s') -> E (mem, (AndFR e () : s'), e2)
          ((AndFR (B p) _) : s') -> R (mem, s', B (p&&q))
          ((OrFL _ e2) : s') -> E (mem, (OrFR e () : s'), e2)
          ((OrFR (B p) _) : s') -> R (mem, s', B (p || q))
          ((AppFR (Fn x e1) _) : s') -> E (mem, s', subst e1 (x, e))
          ((IfF _ e1 e2) : s') -> E (mem, s', if q then e1 else e2)
          ((LetF x _ e2) : s') -> E (mem, s', subst e2 (x, e))
          ((AllocF _) : s') -> 
            let l = newAddress mem in 
              case l of 
                (L i) -> R ((i, e):mem, s', l)
                _ -> P (mem, s, Raise e)
          ((AssigFR (L i) _):s') -> 
            case update (i, e) mem of
              Just mem' -> R (mem', s', Void)
              Nothing -> P (mem, s, Raise e)
          ((WhileF _ e2) : s') -> E (mem, s', if q then e2 else Void)
          ((RaiseF _) : s') -> P (mem, s, Raise e)
          ((HandleF _ x e2) : s') -> R (mem, s', e)
          ((ContinueFR (Cont s'') _) : s') -> R (mem, s'', e)
          _ -> P (mem, s, Raise e)
      (L i) ->
        case s of
          ((FnF x _) : s') -> R (mem, s', Fn x e)
          ((AppFR (Fn x e1) _) : s') -> E (mem, s', subst e1 (x, e))
          ((LetF x _ e2) : s') -> E (mem, s', subst e2 (x, e))
          ((AllocF _) : s') -> 
            let l = newAddress mem in 
              case l of 
                (L i) -> R ((i, e):mem, s', l)
                _ -> P (mem, s, Raise e)
          ((DerefF _) : s') -> 
            case access i mem of
              Just v -> R (mem, s', v)
              Nothing -> P (mem, s, Raise e)
          ((AssigFL _ e2) : s') -> E (mem, ((AssigFR e ()) : s'), e2)
          ((AssigFR (L i) _):s') -> 
            case update (i, e) mem of
              Just mem' -> R (mem', s', Void)
              Nothing -> P (mem, s, Raise e)
          ((RaiseF _) : s') -> P (mem, s, Raise e)
          ((HandleF _ x e2) : s') -> R (mem, s', e)
          ((ContinueFR (Cont s'') _) : s') -> R (mem, s'', e)
          _ -> P (mem, s, Raise e)
      (Void) ->
        case s of 
          ((FnF x _) : s') -> R (mem, s', Fn x e)
          ((AppFR (Fn x e2) _) : s') -> E (mem, s', subst e2 (x, e))
          ((LetF x _ e2) : s') -> E (mem, s', subst e2 (x, e))
          ((AssigFR (L i) _) : s') -> 
            case update (i, e) mem of
              Just mem' -> R (mem', s', Void)
              Nothing -> P (mem, s, Raise e)
          ((SeqF _ e2) : s') -> E (mem, s', e2)
          ((RaiseF _) : s') -> P (mem, s, Raise e)
          ((HandleF _ x e2) : s') -> R (mem, s', e)
          ((ContinueFR (Cont s'') _) : s') -> R (mem, s'', e)
          _ -> P (mem, s, Raise e)
      (Cont st) ->
        case s of
          ((FnF x _) : s') -> R (mem, s', Fn x e)
          ((AppFR (Fn x e2) _) : s') -> E (mem, s', subst e2 (x, e))
          ((LetF x _ e2) : s') -> E (mem, s', subst e2 (x, e))
          ((AllocF _) : s') -> 
            let l = newAddress mem in 
              case l of 
                (L i) -> R ((i, e):mem, s', l)
                _ -> P (mem, s, Raise e)
          ((AssigFR (L i) _) : s') -> 
            case update (i, e) mem of
              Just mem' -> R (mem', s', Void)
              Nothing -> P (mem, s, Raise e)
          ((RaiseF _) : s') -> P (mem, s, Raise e)
          ((HandleF _ x e2) : s') -> R (mem, s', e)
          ((ContinueFL _ e2):s') -> E (mem, ((ContinueFR e ()):s'), e2)
          ((ContinueFR (Cont s'') _) : s') -> R (mem, s'', e)
          _ -> P (mem, s, Raise e)
      (Fn x e1) ->
        case s of
          ((FnF _ _) : s') -> R (mem, s', Fn x e)
          ((AppFL _ e2) : s') -> E (mem, ((AppFR e ()):s'), e2)
          ((AppFR (Fn x e2) _) : s') -> E (mem, s', subst e2 (x, e))
          ((LetF x _ e2) : s') -> E (mem, s', subst e2 (x, e))
          ((AllocF _) : s') -> 
            let l = newAddress mem in 
              case l of 
                (L i) -> R ((i, e):mem, s', l)
                _ -> P (mem, s, Raise e)
          ((AssigFR (L i) _) : s') -> 
            case update (i, e) mem of
              Just mem' -> R (mem', s', Void)
              Nothing -> P (mem, s, Raise e)
          ((RaiseF _) : s') -> P (mem, s, Raise e)
          ((HandleF _ x e2) : s') -> R (mem, s', e)
          ((ContinueFR (Cont s'') _) : s') -> R (mem, s'', e)
          _ -> P (mem, s, Raise e)
      _ ->
        case s of
          ((FnF x _) : s') -> R (mem, s', Fn x e)
          ((HandleF _ x e2) : s') -> R (mem, s', e)
          _ -> P (mem, s, Error)
  eval1 (P (mem, s, e)) =
    case s of
      (HandleF _ x e1):s' ->
        case e of 
          (Raise e1) -> E (mem, s', subst e1 (x, e1))
          _ -> P (mem, s, Raise e)
      (_:s') -> P (mem, s', e)


  evals :: State -> State
  evals s = 
    case eval1 s of
      s'@(E (_, [], e')) -> if blocked e' then s' else evals s'
      s'@(E (_, _, e')) -> evals s'
      s'@(R (_, [], e')) -> if blocked e' then s' else evals s'
      s'@(R (_, _, e')) -> evals s'
      s'@(P (_, [], e')) -> if blocked e' then s' else evals s'
      s'@(P (_, _, e')) -> evals s'

  eval :: Expr -> Expr
  eval e = 
    case evals (E ([], [], e)) of
      R (_, [], e') -> 
        case e' of
          B _ -> e'
          I _ -> e'
          _ -> error "invalid final value"
      _ -> error "no value was returned"

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
      Raise e1 -> blocked e1
      Handle e1 x e2 -> False
      Letcc x e -> False
      Continue e1 e2 -> False
      Cont s -> True
      Error -> True


{--
-- Antiguo eval1
  eval1 (mem, expr) =
    case expr of
      I n -> error "blocked state: integer"
      B p -> error "blocked state: boolean"
      V x -> error "blocked state: variable"
      L _ -> error "blocked state"
      Void -> error "blocked state"
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
      Let i e1 e2 ->
        if blocked e1
          then sM $ subst e2 (i, e1)
          else let (mem', e1') = eval1' e1 in (mem', Let i e1' e2)
      Fn x e1 ->  let (mem', e1') = eval1' e1 in (mem', Fn x e1')
      Fix f e1 -> sM $ Fn f (Fix f e1)
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
              L i -> (((i, e):mem), l)
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

  evals :: State -> State
  evals (E (s, e)) = evals (eval1 (E (s, e)))
  evals (R ([], e)) = R ([], e)
  evals (R ([], e)) = evals (eval1 (R (s, e)))
  evals (P ([], e)) = P ([], e)
  evals (P (s, e)) = evals (eval1 (P (s, e)))

  evals :: (Memory, Expr) -> (Memory, Expr)
  evals s@(_, expr) =
    if blocked expr
      then s
      else evals s

-- Antigua evale
  evale :: Expr -> Expr
  evale ex =
    let (_, ex') = evals ([], ex)
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

-- Antiguo eval
  eval :: Expr -> Type.Type -> Expr
  eval e t =
    let (ctx, t') = Static.infer e
      in
        if ctx /= [] then error ("Expression with unbounded variables: " ++ (show ctx))
        else
          if (t /= t')
            then error ("Type error: " ++ (show t) ++ " is not " ++ (show t'))
            else evale e
  --}
