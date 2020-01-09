namespace GuardedCommands.Frontend
// Michael R. Hansen 05-01-2016
// This file is obtained by an adaption of the file MicroC/Absyn.fs by Peter Sestoft
//
// It must preceed TypeChecks.fs, CodeGen.fs, CodeGenOpt.fs, Util.fs in Solution Explorer
//

open System
open Machine

module AST =

   type Exp =                            
         | N  of int                   (* Integer constant            *)
         | B of bool                   (* Boolean constant            *)
         | Access of Access            (* x    or  ^p    or  a[e]     *)
         | Addr of Access              (* &x   or  &p^   or  &a[e]    *)
         | Apply of string * Exp list  (* Function application        *)

   and Access = 
          | AVar of string             (* Variable access        x    *) 
          | AIndex of Access * Exp     (* Array indexing         a[e] *)
          | ADeref of Exp              (* Pointer dereferencing  p^   *)

   type Stm  =                            
          | PrintLn of Exp               (* Print                          *) 
          | Ass of Access * Exp          (* x:=e  or  p^:=e  or  a[e]:=e   *)
          | Return of Exp option         (* Return from function           *)   
          | Alt of GuardedCommand        (* Alternative statement          *) 
          | Do of GuardedCommand         (* Repetition statement           *) 
          | Block of Dec list * Stm list (* Block: grouping and scope      *)
          | Call of string * Exp list    (* Procedure call                 *)
               
   and GuardedCommand = GC of (Exp * Stm list) list (* Guarded commands    *)

   and Dec = 
         | VarDec of Typ * string        (* Variable declaration               *)
         | FunDec of Typ option * string * Dec list * Stm
                                         (* Function and procedure declaration *) 

   and Typ  = 
         | ITyp                          (* Type int                    *)
         | BTyp                          (* Type bool                   *)
         | ATyp of Typ * int option      (* Type array                  *)
         | PTyp of Typ                   (* Type pointer                *)
         | FTyp of Typ list * Typ option (* Type function and procedure *)

   type Program = P of Dec list * Stm list   (* Program                 *)
