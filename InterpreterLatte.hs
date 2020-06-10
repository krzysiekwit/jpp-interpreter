module InterpreterLatte where

import AbsLatte
import Data.Map as M
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Maybe


data LocType = LOC Loc
data Fun = A ([Expr] -> Semantics (Maybe VarVal))
type Loc = Int
type Ref = Bool
type St = M.Map Loc VarVal
type Env = (M.Map Ident LocType, M.Map Ident Fun)
type Semantics = ReaderT Env (StateT St (ExceptT String IO))
data VarVal = INT Int | STRING String | BOOL Bool

emptyEnv :: Env
emptyEnv = (M.empty, M.empty)

iniState :: St
iniState = M.singleton 0 (INT 1)

stmt :: Stmt -> Semantics (Maybe VarVal)
stmt Empty = return Nothing
stmt (Print e) = do {        case e of
                        (ELitInt val) -> do {   Just (INT val) <- eval e;
                                                liftIO $ print val;
                                                return Nothing}
                        (EString val) -> do {   Just (STRING val) <- eval e;
                                                liftIO $ print val;
                                                return Nothing}
                        (ELitTrue) -> do {      Just (BOOL val) <- eval e;
                                                liftIO $ print val;
                                                return Nothing}
                        (ELitFalse) -> do {      Just (BOOL val) <- eval e;
                                                liftIO $ print val;
                                                return Nothing}
                        e -> do {               mval <- eval e;
                                                case mval of
                                                        Just (INT val) -> do {  liftIO $ print val;
                                                                                return Nothing}
                                                        Just (BOOL val) -> do { liftIO $ print val;
                                                                                return Nothing}
                                                        Just (STRING val) -> do {liftIO $ print val;
                                                                                 return Nothing}}}
stmt (Cond e (Blck stmts)) = do {       ev <- eval e;
                                        case ev of
                                                Just (BOOL True) -> evalStmts stmts
                                                Just (BOOL False) -> return Nothing
                                                ev -> throwError $ "Error: if condition is not a bool value"}
stmt (CondElse e (Blck stmts1) (Blck stmts2)) = do {    ev <- eval e;
                                                        case ev of
                                                                Just (BOOL True) -> evalStmts stmts1
                                                                Just (BOOL False) -> evalStmts stmts2
                                                                ev -> throwError $ "Error: if condition is not a bool value"}
stmt (While e (Blck stmts)) = do {      ev <- eval e;
                                        case ev of
                                                Just (BOOL True) -> do {evalStmts stmts;
                                                                        stmt (While e (Blck stmts))}
                                                Just (BOOL False) -> return Nothing
                                                ev -> throwError $ "Error: while condition is not a bool value"}
stmt (BStmt (Blck stmts)) = evalStmts stmts;
stmt (Ass nm e) = do {  (envv,_) <- ask;
                        case M.lookup nm envv of
                                Just (LOC loc) -> do { ev <- eval e; 
                                                       case ev of
                                                         Just (INT exp) -> do { Just val <- gets (M.lookup loc);
                                                                                case val of
                                                                                  (INT v) -> do {modify (M.insert loc (INT exp));
                                                                                                 return Nothing}
                                                                                  v -> throwError $ "Error: assignment of value of wrong type"}
                                                         Just (BOOL exp) -> do { Just val <- gets (M.lookup loc);
                                                                                 case val of
                                                                                   (BOOL v) -> do {modify (M.insert loc (BOOL exp));
                                                                                                   return Nothing}
                                                                                   v -> throwError $ "Error: assignment of value of wrong type"}
                                                         Just (STRING exp) -> do { Just val <- gets (M.lookup loc);
                                                                                   case val of
                                                                                     (STRING v) -> do {modify (M.insert loc (STRING exp));
                                                                                                       return Nothing}
                                                                                     v -> throwError $ "Error: assignment of value of wrong type"}
                                                         ev -> throwError $ "Error: assignment of value of wrong type"}
                                Nothing -> throwError $ "Error: use of undeclared variable"}
stmt (Incr nm) = do {   (envv,_) <- ask;
                        case M.lookup nm envv of
                                Just (LOC loc) -> do {  v <- gets (M.lookup loc);
                                                        case v of
                                                          Just (INT val) -> do { modify (M.insert loc (INT (val+1)));
                                                                                 return Nothing}
                                                          v -> throwError $ "Error: incrementation of non int variable"}
                                Nothing -> throwError $ "Error: use of undeclared variable"}
stmt (Decr nm) = do {   (envv,_) <- ask;
                        case M.lookup nm envv of
                                Just (LOC loc) -> do {  v <- gets (M.lookup loc);
                                                        case v of
                                                          Just (INT val) -> do { modify (M.insert loc (INT (val-1)));
                                                                                 return Nothing}
                                                          v -> throwError $ "Error: decrementation of non int variable"}
                                Nothing -> throwError $ "Error: use of undeclared variable"}
stmt (SExp e) = do {    exp <- eval e;
                        return Nothing;}

stmt (Ret e) = do {    exp <- eval e;
                       return exp;}

decls :: Type -> [Item] -> Semantics Env
decls t [] = ask
decls t (i:is) = case i of 
                        (NoInit nm) -> do {     env' <- declv t nm;
                                                local (const env') (decls t is)}
                        (Init nm e) -> do {     env' <- decli t nm e;
                                                local (const env') (decls t is)}

getDec :: [Arg] -> [Expr] -> [(Expr, Ident, Type, Ref)]
getDec [] [] = []
getDec a [] = ((EVar (Ident "")), (Ident ""), (ArgTypeP Integer), True):[]
getDec [] a = ((EVar (Ident "")), (Ident ""), (ArgTypeP Integer), False):[]
getDec (a:args) (e:exps) = case a of 
                             (ArgVal t nm) -> (e, nm, t, False):(getDec args exps)
                             (ArgRef t nm) -> (e, nm, t, True):(getDec args exps)

argDec :: [(Expr, Ident, Type, Ref)] -> Semantics Env
argDec [] = ask
argDec ((e, nm, t, r):ds) = case nm of
                              (Ident "") -> case r of
                                      True -> throwError $ "Error: not enough arguments given to a function"
                                      False -> throwError $ "Error: too many arguments given to a function"
                              nm -> case r of
                                      True -> do { env' <- declr t nm e;
                                                   local (const env') (argDec ds)}
                                      False -> do { env' <- decli t nm e;
                                                    local (const env') (argDec ds)}

declr :: Type -> Ident -> Expr -> Semantics Env
declr (ArgTypeP Integer) nm (EVar pnm) = do {(envv,envf) <- ask;
                                             case M.lookup pnm envv of
                                               Just (LOC loc) -> do { Just val <- gets (M.lookup loc);
                                                                      case val of
                                                                        (INT v) -> return (M.insert nm (LOC loc) envv, envf)
                                                                        v -> throwError $ "Error: argumets of wrong type given to a function"}}
declr (ArgTypeP String) nm (EVar pnm) = do { (envv,envf) <- ask;
                                             case M.lookup pnm envv of
                                               Just (LOC loc) -> do { Just val <- gets (M.lookup loc);
                                                                      case val of
                                                                        (STRING v) -> return (M.insert nm (LOC loc) envv, envf)
                                                                        v -> throwError $ "Error: argumets of wrong type given to a function"}}
declr (ArgTypeP Bool) nm (EVar pnm) = do {   (envv,envf) <- ask;
                                             case M.lookup pnm envv of
                                               Just (LOC loc) -> do { Just val <- gets (M.lookup loc);
                                                                      case val of
                                                                        (BOOL v) -> return (M.insert nm (LOC loc) envv, envf)
                                                                        v -> throwError $ "Error: argumets of wrong type given to a function"}}
declr t nm pnm = throwError $ "Error: reference argument must by given by identificator"

declf :: Type -> Ident -> [Arg] -> Block -> Semantics Env
declf t nm args (Blck stmts) = do {     (envv, envf) <- ask;
                                        case M.lookup nm envf of
                                             Nothing -> let f params = do {(envv, envf) <- ask;
                                                                           (envv', envf') <- local(const (envv, envf)) (argDec (getDec args params));
                                                                           local (const (envv', M.insert nm (A f) envf')) (evalFunStmts stmts t)}
                                                                           in return (envv, M.insert nm (A f) envf)
                                             v -> throwError $ "Error: declration of more than one function with the same identificator"}
evalFunStmts :: [Stmt] -> Type -> Semantics (Maybe VarVal)
evalFunStmts stmts t = do { ret <- (evalStmts stmts);
                            case ret of
                              Nothing -> case t of
                                           (VoidType Void) -> return ret
                                           v -> throwError $ "Error: no return statement in non void function"
                              Just (INT v) -> case t of
                                                (ArgTypeP Integer) -> return ret
                                                (VoidType Void) -> throwError $ "Error: return statement in void function"
                                                v -> throwError $ "Error: value of wrong type returned by function"
                              Just (STRING v) -> case t of
                                                   (ArgTypeP String) -> return ret
                                                   (VoidType Void) -> throwError $ "Error: return statement in void function"
                                                   v -> throwError $ "Error: value of wrong type returned by function"
                              Just (BOOL v) -> case t of
                                                 (ArgTypeP Bool) -> return ret
                                                 (VoidType Void) -> throwError $ "Error: return statement in void function"
                                                 v -> throwError $ "Error: value of wrong type returned by function"}
declv :: Type -> Ident -> Semantics Env
declv (ArgTypeP Integer) nm = do {      Just (INT newLoc) <- gets (M.lookup 0);
                                        modify (M.insert newLoc (INT 0));
                                        modify (M.insert 0 (INT (newLoc+1)));
                                        (envv,envf) <- ask;
                                        return (M.insert nm (LOC newLoc) envv, envf)}
declv (ArgTypeP String) nm = do {       Just (INT newLoc) <- gets (M.lookup 0);
                                        modify (M.insert newLoc (STRING ""));
                                        modify (M.insert 0 (INT (newLoc+1)));
                                        (envv,envf) <- ask;
                                        return (M.insert nm (LOC newLoc) envv, envf)}
declv (ArgTypeP Bool) nm = do {        Just (INT newLoc) <- gets (M.lookup 0);
                                        modify (M.insert newLoc (BOOL True));
                                        modify (M.insert 0 (INT (newLoc+1)));
                                        (envv,envf) <- ask;
                                        return (M.insert nm (LOC newLoc) envv, envf)}

decli :: Type -> Ident -> Expr -> Semantics Env
decli (ArgTypeP Integer) nm e = do {    ev <- eval e;
                                        case ev of
                                          Just (INT exp) -> do { Just (INT newLoc) <- gets (M.lookup 0);
                                                                 modify (M.insert newLoc (INT exp));
                                                                 modify (M.insert 0 (INT (newLoc+1)));
                                                                 (envv,envf) <- ask;
                                                                 return (M.insert nm (LOC newLoc) envv, envf)}
                                          ev -> throwError $ "Error: assignment of non int value to int variable"}
decli (ArgTypeP String) nm e = do {    ev <- eval e;
                                        case ev of
                                          Just (STRING exp) -> do {  Just (INT newLoc) <- gets (M.lookup 0);
                                                                     modify (M.insert newLoc (STRING exp));
                                                                     modify (M.insert 0 (INT (newLoc+1)));
                                                                     (envv,envf) <- ask;
                                                                     return (M.insert nm (LOC newLoc) envv, envf)}
                                          ev -> throwError $ "Error: assignment of non string value to string variable"}
decli (ArgTypeP Bool) nm e = do {    ev <- eval e;
                                        case ev of
                                          Just (BOOL exp) -> do {  Just (INT newLoc) <- gets (M.lookup 0);
                                                                   modify (M.insert newLoc (BOOL exp));
                                                                   modify (M.insert 0 (INT (newLoc+1)));
                                                                   (envv,envf) <- ask;
                                                                   return (M.insert nm (LOC newLoc) envv, envf)}
                                          ev -> throwError $ "Error: assignment of non bool value to bool variable"}

eval :: Expr -> Semantics (Maybe VarVal)
eval (ELitInt val) = return $ Just $ INT $ fromInteger val
eval (EString val) = return $ Just $ STRING $ val
eval ELitTrue = return $ Just $ BOOL $ True
eval ELitFalse = return $ Just $ BOOL $ False
eval (Neg e) = do {     v <- eval e;
                        case v of
                          Just (INT val) -> return $ Just $ INT $ (-val)
                          v -> throwError $ "Error: negation of non int value"}
eval (Not e) = do {     v <- eval e;
                        case v of
                          Just (BOOL val) -> return $ Just $ BOOL $ (not val);
                          v -> throwError $ "Error: negation of non bool value"}
eval (EMul e1 Times e2) = do {  mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ INT $ (val1 * val2)
                                                v -> throwError $ "Error: * opperator between non int values"
                                        v -> throwError $ "Error: * opperator between non int values"}
eval (EMul e1 Div e2) = do {    mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> case val2 of
                                                                      0 -> throwError $ "Error: division by zero"
                                                                      val2 -> return $ Just $ INT $ (val1 `div` val2)
                                                v -> throwError $ "Error: / opperator between non int values"
                                        v -> throwError $ "Error: / opperator between non int values"}
eval (EMul e1 Mod e2) = do {    mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ INT $ (val1 `mod` val2)
                                                v -> throwError $ "Error: % opperator between non int values"
                                        v -> throwError $ "Error: % opperator between non int values"}
eval (EAdd e1 Plus e2) = do {   mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ INT $ (val1 + val2)
                                                v -> throwError $ "Error: + opperator between non int values"
                                        v -> throwError $ "Error: + opperator between non int values"}
eval (EAdd e1 Minus e2) = do {  mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ INT $ (val1 - val2)
                                                v -> throwError $ "Error: - opperator between non int values"
                                        v -> throwError $ "Error: - opperator between non int values"}
eval (ERel e1 LTH e2) = do {    mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ BOOL $ (val1 < val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 < val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (STRING val1) -> case mval2 of
                                                Just (STRING val2) -> return $ Just $ BOOL $ (val1 < val2)
                                                v -> throwError $ "Error: comparition between values of different types"}
eval (ERel e1 LE e2) = do {        mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ BOOL $ (val1 <= val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 <= val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (STRING val1) -> case mval2 of
                                                Just (STRING val2) -> return $ Just $ BOOL $ (val1 <= val2)
                                                v -> throwError $ "Error: comparition between values of different types"}
eval (ERel e1 GTH e2) = do {        mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ BOOL $ (val1 > val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 > val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (STRING val1) -> case mval2 of
                                                Just (STRING val2) -> return $ Just $ BOOL $ (val1 > val2)
                                                v -> throwError $ "Error: comparition between values of different types"}
eval (ERel e1 GE e2) = do do {        mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ BOOL $ (val1 >= val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 >= val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (STRING val1) -> case mval2 of
                                                Just (STRING val2) -> return $ Just $ BOOL $ (val1 >= val2)
                                                v -> throwError $ "Error: comparition between values of different types"}
eval (ERel e1 EQU e2) = do {        mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ BOOL $ (val1 == val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 == val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (STRING val1) -> case mval2 of
                                                Just (STRING val2) -> return $ Just $ BOOL $ (val1 == val2)
                                                v -> throwError $ "Error: comparition between values of different types"}
eval (ERel e1 NE e2) = do {     mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (INT val1) -> case mval2 of
                                                Just (INT val2) -> return $ Just $ BOOL $ (val1 /= val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 /= val2)
                                                v -> throwError $ "Error: comparition between values of different types"
                                        Just (STRING val1) -> case mval2 of
                                                Just (STRING val2) -> return $ Just $ BOOL $ (val1 /= val2)
                                                v -> throwError $ "Error: comparition between values of different types"}
eval (EAnd e1 e2) = do {        mval1 <- eval e1;
                                mval2 <- eval e2;
                                case mval1 of
                                        Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 && val2)
                                                v -> throwError $ "Error: && opperator between non bool values"
                                        v -> throwError $ "Error: && opperator between non bool values"}
eval (EOr e1 e2) = do {        mval1 <- eval e1;
                               mval2 <- eval e2;
                               case mval1 of
                                       Just (BOOL val1) -> case mval2 of
                                                Just (BOOL val2) -> return $ Just $ BOOL $ (val1 || val2)
                                                v -> throwError $ "Error: || opperator between non bool values"
                                       v -> throwError $ "Error: || opperator between non bool values"}
eval (EVar nm) = do {           (envv,_) <- ask;
                                case M.lookup nm envv of
                                        Just (LOC loc) -> do {
                                                Just val <- gets (M.lookup loc);                                                         
                                                return $ Just $ val}
                                        Nothing -> throwError $ "Error: use of undeclared variable"}
eval (EApp nm exps) = do {      (_, env) <- ask;
                                case M.lookup nm env of
                                        Just (A fun) -> fun exps
                                        Nothing -> throwError $ "Error: use of undeclared function"}

evalStmts :: [Stmt] -> Semantics (Maybe VarVal)
evalStmts [] = return Nothing
evalStmts (s:ss) = case s of
                        (Decl t is) -> do {     env' <- decls t is;
                                                local (const env') (evalStmts ss)}
                        (FDecl t nm args b) -> do {     env' <- declf t nm args b;
                                                        local (const env') (evalStmts ss)}                        
                        s -> do {       mval <- stmt s;
                                        case mval of
                                                Just val -> return $ Just val
                                                Nothing -> evalStmts ss}


evalProg :: [Stmt] -> IO ()
evalProg stmts = do { finalState <- runExceptT (execStateT (runReaderT (evalStmts stmts) emptyEnv) iniState) ;
                      case finalState of
                        Right a -> return ()
                        Left b -> print b}

runProgram :: Program -> IO ()
runProgram (Prg stmts) = evalProg $ stmts
