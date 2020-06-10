-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

module AbsLatte where

newtype Ident = Ident String
  deriving (Eq, Ord, Show, Read)

data Program = Prg [Stmt]
  deriving (Eq, Ord, Show, Read)

data Block = Blck [Stmt]
  deriving (Eq, Ord, Show, Read)

data Stmt
    = Empty
    | BStmt Block
    | Decl Type [Item]
    | FDecl Type Ident [Arg] Block
    | Ass Ident Expr
    | Incr Ident
    | Decr Ident
    | Ret Expr
    | VRet
    | Cond Expr Block
    | CondElse Expr Block Block
    | While Expr Block
    | SExp Expr
    | Print Expr
  deriving (Eq, Ord, Show, Read)

data Arg = ArgVal Type Ident | ArgRef Type Ident
  deriving (Eq, Ord, Show, Read)

data Item = NoInit Ident | Init Ident Expr
  deriving (Eq, Ord, Show, Read)

data Type = ArgTypeP PType | VoidType VType
  deriving (Eq, Ord, Show, Read)

data PType = Integer | String | Bool
  deriving (Eq, Ord, Show, Read)

data VType = Void
  deriving (Eq, Ord, Show, Read)

data Expr
    = EVar Ident
    | ELitInt Integer
    | EString String
    | ELitTrue
    | ELitFalse
    | EApp Ident [Expr]
    | Neg Expr
    | Not Expr
    | EMul Expr MulOp Expr
    | EAdd Expr AddOp Expr
    | ERel Expr RelOp Expr
    | EAnd Expr Expr
    | EOr Expr Expr
  deriving (Eq, Ord, Show, Read)

data AddOp = Plus | Minus
  deriving (Eq, Ord, Show, Read)

data MulOp = Times | Div | Mod
  deriving (Eq, Ord, Show, Read)

data RelOp = LTH | LE | GTH | GE | EQU | NE
  deriving (Eq, Ord, Show, Read)

