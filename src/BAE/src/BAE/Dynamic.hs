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
                      (LetCC x e1) -> E (m, s, subst e1 (x, Cont s))
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
          _ -> P (mem, s, Raise e)
  eval1 (P (mem, s, e)) =
    case s of
      (HandleF _ x e1):s' ->
        case e of 
          (Raise e1) -> E (mem, s', subst e1 (x, e1))
          _ -> P (mem, s, Raise e)
      (_:s') -> P (mem, s', e)



  -- | Evaular un estado exhaustivamente
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
      LetCC x e -> False
      Continue e1 e2 -> False
      Cont s -> True