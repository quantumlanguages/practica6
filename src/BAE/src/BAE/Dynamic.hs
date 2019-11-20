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

  type Pending = ()
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
             | RaiseF Pending
             | HandleF Pending Identifier Expr
             | ContinueL Pending Expr
             | ContinueR Expr Pending

  type Stack = [Frame]

  data State = E (Stack, Memory, Expr) | R (Stack, Memory, Expr) | P (Stack, Memory, Expr)

  eval1 :: State -> State
  eval1 (E (s, m, e)) = case e of
                      -- valores
                      (V _) -> R (s, m, e)
                      (B _) -> R (s, m, e)
                      (I _) -> R (s, m, e)
                      (L _) -> R (s, m, e)
                      (I _) -> R (s, m, e)
                      (Cont _) -> R (s, m, e)
                      -- operadores unitarios
                      (Fn x e) -> E (((FnF x Pending):s), m, e)
                      (Fix x e) -> E (s, m, Sintax.subst e (x, Fix x e))
                      (Succ e) -> E ((SuccF Pending):s, m, e)
                      (Pred e) -> E ((PredF Pending):s, m, e)
                      (Not e) -> E ((NotF Pending):s, m, e)
                      (Alloc e) -> E ((AllocF Pending):s, m, e)
                      (Deref e) -> E ((DerefF Pending):s, m, e)
                      (Raise e) -> E ((RaiseF Pending):s, m, e)
                      -- operadores binarios
                      (Add e1 e2) ->
                        case e1 of
                          (I n) -> E ((AddFR (I n) Pending):s, m, e2)
                          _ -> E ((AddFL Pending (e2)):s, m, e1)
                      (Mul e1 e2) ->
                        case e1 of
                          (I n) -> E ((MulFR (I n) Pending):s, m, e2)
                          _ -> E ((MulFL Pending (e2)):s, m, e1)
                      (And e1 e2) ->
                        case e1 of
                          (B p) -> E ((AndFR (B p) Pending):s, m, e2)
                          _ -> E ((AndFL Pending (e2)):s, m, e1)
                      (Or e1 e2) ->
                        case e1 of
                          (B p) -> E ((OrFR (B p) Pending):s, m, e2)
                          _ -> E ((OrFL Pending (e2)):s, m, e1)
                      (Lt e1 e2) ->
                        case e1 of
                          (I n) -> E ((LtFR (I n) Pending):s, m, e2)
                          _ -> E ((LtFL Pending (e2)):s, m, e1)
                      (Gt e1 e2) ->
                        case e1 of
                          (I n) -> E ((GtFR (I n) Pending):s, m, e2)
                          _ -> E ((GtFL Pending (e2)):s, m, e1)
                      (Eq e1 e2) ->
                        case e1 of
                          (I n) -> E ((EqFR (I n) Pending):s, m, e2)
                          _ -> E ((EqFL Pending (e2)):s, m, e1)
                      (App e1 e2) ->
                        case e1 of
                          (Fn x e) -> E ((AppFR (Fn x e) Pending):s, m, e2)
                          _ -> E ((EqFL Pending (e2)):s, m, e1)
                      (Assign e1 e2) ->
                        case e1 of
                          (L n) -> E ((AssignFR (L n) Pending):s, m, e2)
                          _ -> E ((AssignFL Pending (e2)):s, m, e1)
                      (Seq e1 e2) ->
                        case e1 of
                          (Void) -> E ((SeqFR (Void) Pending):s, m, e2) -- Revisar que sustituye Void
                          _ -> E ((SeqFL Pending (e2)):s, m, e1)
                      (While e1 e2) ->
                        case e1 of
                          (B p) -> E ((WhileFR (B p) Pending):s, m, e2)
                          _ -> E ((WhileFL Pending (e2)):s, m, e1)
                      (Continue e1 e2) ->
                        case e1 of
                          (Cont st) -> E ((ContinueFR (Cont st) Pending):s, m, e2)
                          _ -> E ((ContinueFL Pending (e2)):s, m, e1)
                      (Handle e1 i e2) -> E ((HandleF Pending i e2):s, m, e1)
                      --ternarias
                      (If e1 e2 e3) -> E ((IfF Pending e2 e3):s, m, e1)
                      (Let x e1 e2) -> E ((LetF x Pending e2):s, m, e2)
                      (Letcc i e) -> E (s, m, Sintax.subst e (x, Cont s))
  eval1 (R (s, e)) =
    case e of
      (V x) ->
        case s of
          ((LetFL x _ e2) : s') -> E (s', Sintax.subst e2 (x, e))
          _ -> P (s, Error)
      (I m) ->
        case s of
          ((FnF x _) : s') -> R (s', Fn x)
          ((SuccF _) : s') -> R (s', I (succ n))
          ((PredF _) : s') -> R (s', I (pred n))
          ((AddFL _ e2) : s') -> E ((AddFR e Pending : s'), e2)
          ((AddFR (I n) _) : s') -> R (s', I (n+m))
          ((MulFL _ e2) : s') -> E ((MulFR e Pending : s'), e2)
          ((MulFR (I n) _) : s') -> R (s', I (n*m))
          ((LtFL _ e2) : s') -> E ((LtFR e Pending : s'), e2)
          ((LtFR (I n) _) : s') -> R (s', I (n<m))
          ((GtFL _ e2) : s') -> E ((GtFR e Pending : s'), e2)
          ((GtFR (I n) _) : s') -> R (s', I (n>m))
          ((EqFL _ e2) : s') -> E ((EqFR e Pending : s'), e2)
          ((EqFR (I n) _) : s') -> R (s', I (n==m))
          ((LetFL x _ e2) : s') -> E (s', Sintax.subst e2 (x, e))
          _ -> P (s, Error)
      (B q) ->
        case s of
          ((FnF x _) : s') -> R (s', Fn x)
          ((NotF _) : s') -> R (s', B (not n))
          ((AndFL _ e2) : s') -> E ((AndFR e Pending : s'), e2)
          ((AndFR (B p) _) : s') -> R (s', I (n&&m))
          ((OrFL _ e2) : s') -> E ((OrFR e Pending : s'), e2)
          ((OrFR (B p) _) : s') -> R (s', B (p || q))
          ((IfFL _ e1 e2) : s') -> E (s', if q then e1 else e2)
          ((LetFL x _ e2) : s') -> E (s', Sintax.subst e2 (x, e))
          _ -> P (s, Error)
      (Fn x e) ->
        case s of
          ((FnF x _) : s') -> R (s', Fn x)
          ((App _ e2) : s') -> E (s', Sintax.subst e2 (x, e))
          ((LetFL x _ e2) : s') -> E (s', Sintax.subst e2 (x, e))
          _ -> P (s, Error)
  eval1 (P (s, Error)) ->
    case s of
      (s:s') -> P (s', Error)




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


  eval :: Expr -> Type.Type -> Expr
  eval e t =
    let (ctx, t') = Static.infer e
      in
        if ctx /= [] then error ("Expression with unbounded variables: " ++ (show ctx))
        else
          if (t /= t')
            then error ("Type error: " ++ (show t) ++ " is not " ++ (show t'))
            else evale e
