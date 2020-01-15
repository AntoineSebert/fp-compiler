namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016 , 04-01-2018

open System
open Machine
open GuardedCommands.Frontend.AST

module TypeCheck =

    let monops = ["-"; "!"; "^"; "&"]
    let dyops = ["+"; "*"; "="; "&&"; "-"; "<"; ">"; "<="; "<>"; "||"]

/// tcE gtenv ltenv e gives the type for expression e on the basis of type environments gtenv and ltenv
/// for global and local variables
    let rec tcE gtenv ltenv =
        function
        | N _                                        -> ITyp
        | B _                                        -> BTyp
        | Access acc                                 -> tcA gtenv ltenv acc
        | Apply(f, [e])
            when List.exists (fun x -> x = f) monops -> tcMonadic gtenv ltenv f e
        | Apply(f, [e1; e2])
            when List.exists (fun x -> x = f) dyops  -> tcDyadic gtenv ltenv f e1 e2
        | Apply(f, es)                               -> failwith ("tcE: not supported yet")
        | Addr acc                                   -> tcA gtenv ltenv acc

    and tcMonadic gtenv ltenv f e =
        match (f, tcE gtenv ltenv e) with
        | ("-", ITyp)                 -> ITyp
        | ("!", BTyp)                 -> BTyp
        | ("^", t)
            when t = BTyp || t = ITyp -> t
        | ("&", t)
            when t = BTyp || t = ITyp -> t
        | _                           -> failwith "illegal/illtyped monadic expression"

    and tcDyadic gtenv ltenv f e1 e2 =
        match (f, tcE gtenv ltenv e1, tcE gtenv ltenv e2) with
        | (o, ITyp, ITyp)
            when List.exists (fun x ->  x = o) ["+"; "*"; "-"]             -> ITyp
        | (o, ITyp, ITyp)
            when List.exists (fun x ->  x = o) ["="; "<"; ">"; "<="; "<>"] -> BTyp
        | (o, BTyp, BTyp)
            when List.exists (fun x ->  x = o) ["&&"; "="; "||"]           -> BTyp
        | _                                                                -> failwith("illegal/illtyped dyadic expression: " + f)

    // Typ option * string * Dec list * Stm
    and tcNaryFunction gtenv ltenv f es = failwith "type check: functions not supported yet"

    and tcNaryProcedure gtenv ltenv f es = failwith "type check: procedures not supported yet"

/// tcA gtenv ltenv e gives the type for access acc on the basis of type environments gtenv and ltenv
/// for global and local variables
    and tcA gtenv ltenv =
        function
        | AVar x         -> match Map.tryFind x ltenv with
                            | None   -> match Map.tryFind x gtenv with
                                        | None   -> failwith ("no declaration for : " + x)
                                        | Some t -> t
                            | Some t -> t
        | AIndex(acc, e) -> match tcE gtenv ltenv e with
                            | ITyp _ | BTyp _ -> tcA gtenv ltenv acc
                            | _ -> failwith "tcA: array index must be an integer"
        | ADeref e       -> tcE gtenv ltenv e

/// tcS gtenv ltenv retOpt s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
/// for global and local variables and the possible type of return expressions
    and tcS gtenv ltenv =
        function
        | PrintLn e          -> ignore(tcE gtenv ltenv e)
        | Ass(acc, e)        -> if tcA gtenv ltenv acc = tcE gtenv ltenv e
                                then ()
                                else failwith "illtyped assignment"
        | MulAssign(_as, es) -> ignore(List.iter2 (fun acc exp -> (tcS gtenv ltenv (Ass(acc, exp)))) _as, es)
        | Return opt_e       -> match opt_e with
                                | Some e -> ignore(tcE gtenv ltenv e)
                                | None   -> ()
        | Alt gcs            -> ignore(tcGCs gtenv ltenv gcs)
        | Do gcs             -> ignore(tcGCs gtenv ltenv gcs)
        | Block(decs, stms)  -> List.iter (tcS gtenv (tcGDecs ltenv decs)) stms
        | Call(s, es)        -> for e in es do ignore(tcE gtenv ltenv e)

    and tcGC gtenv ltenv =
        function
        | (_,[])   -> failwith "tcGC: Guarded command doesn't have any statements"
        | (e,stms) -> if tcE gtenv ltenv e = BTyp
                      then List.iter (tcS gtenv ltenv) stms
                      else failwith "tcGC: Guarded command is not of boolean type"

    and tcGCs gtenv ltenv = function GC(gcs) -> List.iter (tcGC gtenv ltenv) gcs
    
    (*
    and tcStmReturnType topt gtenv ltenv stm = function
        // unwrap opt and check
        | Return opt_e -> if opt_e <> topt
                            then failwith "tcStmReturnType: all return statements must have the function's return type"
                            else tcS gtenv ltenv
                          topt
        | Block([], stms) ->
          for stm in stms do
            tcStmReturnType topt gtenv ltenv stm
          topt
        | _ -> topt

    and tcFunParam decs =
        // test distinct
        //[1; 2; 2; 3]
        //[1; 2; 3]
        tcGDecs Map.empty decs

    and tcFun gtenv topt f decs stm =
        (*
        match (tcStmReturnType topt gtenv (tcFunParam decs) stm) with
        | Some t -> Map.add f t gtenv
        | None -> failith ""
        *)
        Map.epty
        *)

    and tcGDec gtenv =
        function
        | VarDec(t, s)               -> Map.add s t gtenv
        | FunDec(topt, f, decs, stm) ->
            match topt with
            | None -> tcNaryProcedure gtenv Map.empty f []
            | Some _ -> tcNaryFunction gtenv Map.empty f []

    and tcGDecs gtenv =
        function
        | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
        | _         -> gtenv

/// tcP prog checks the well-typeness of a program prog
    and tcP(P(decs, stms)) = List.iter (tcS (tcGDecs Map.empty decs) Map.empty) stms
