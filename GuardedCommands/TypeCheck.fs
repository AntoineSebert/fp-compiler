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
        | Apply(f, es)                               -> tcNaryFunction gtenv ltenv f es
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

    and tcNaryFunction gtenv ltenv f es =
        match Map.tryFind f ltenv with
        | Some t ->
            match t with
            | FTyp(pats, opt_ret) ->
                List.iter2 (fun typ exp ->
                    if typ = tcE gtenv ltenv exp
                    then ()
                    else failwith ("type mismatch in call for " + f)
                ) pats es
                match opt_ret with
                | Some t -> t
                | None -> failwith (f + " is a procedure, expected a function")
            | _ -> failwith (f + " is not a function nor a procedure")
        | None    ->
            match Map.tryFind f gtenv with
            | Some t ->
                match t with
                | FTyp(pats, opt_ret) ->
                    List.iter2 (fun typ exp ->
                        if typ = tcE gtenv ltenv exp
                        then ()
                        else failwith ("type mismatch in call for " + f)
                    ) pats es
                    match opt_ret with
                    | Some t -> t
                    | None -> failwith (f + " is a procedure, expected a function")
                | _ -> failwith (f + " is not a function nor a procedure")
            | None    -> failwith ("no declaration for : " + f)

    and tcNaryProcedure gtenv ltenv f es =
        match Map.tryFind f ltenv with
        | Some t ->
            match t with
            | FTyp(pats, opt_ret) ->
                List.iter2 (fun typ exp ->
                    if typ = tcE gtenv ltenv exp
                    then ()
                    else failwith ("type mismatch in call for " + f)
                ) pats es
                if opt_ret.IsSome
                then failwith (f + " is a function, expected a procedure")
                else ()
            | _ -> failwith (f + " is not a function nor a procedure")
        | None    ->
            match Map.tryFind f gtenv with
            | Some t ->
                match t with
                | FTyp(pats, opt_ret) ->
                    List.iter2 (fun typ exp ->
                        if typ = tcE gtenv ltenv exp
                        then ()
                        else failwith ("type mismatch in call for " + f)
                    ) pats es
                    if opt_ret.IsSome
                    then failwith (f + " is a function, expected a procedure")
                    else ()
                | _ -> failwith (f + " is not a function nor a procedure")
            | None    -> failwith ("no declaration for : " + f)

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
        | Ass(acc, e)        -> if tcA gtenv ltenv acc <> tcE gtenv ltenv e then failwith "illtyped assignment"
        | MulAssign(_as, es) -> ignore(List.iter2 (fun acc exp -> (tcS gtenv ltenv (Ass(acc, exp)))) _as, es)
        | Return e           -> ignore(tcE gtenv ltenv e)
        | Alt gcs            -> ignore(tcGCs gtenv ltenv gcs)
        | Do gcs             -> ignore(tcGCs gtenv ltenv gcs)
        | Block(decs,stms)   -> List.iter (tcS gtenv (tcGDecs ltenv decs)) stms
        | Call(_, es)        -> ignore(List.map (tcE gtenv ltenv) es)

    and tcGC gtenv ltenv =
        function
        | (_, [])   -> failwith "tcGC: Guarded command doesn't have any statements"
        | (e, stms) -> if tcE gtenv ltenv e = BTyp
                       then List.iter (tcS gtenv ltenv) stms
                       else failwith "tcGC: Guarded command is not of boolean type"

    and tcGCs gtenv ltenv = function GC(gcs) -> List.iter (tcGC gtenv ltenv) gcs

    and tcGDec gtenv =
        function
        | VarDec(t, s)               -> Map.add s t gtenv
        | FunDec(topt, f, decs, stm) ->
            let ltenv: Map<string, Typ> = tcGDecs Map.empty decs

            if ltenv.Count <> decs.Length
            then failwith ("Formal parameters for " + f + " must be all different")

            let rec check_statement (statement: Stm, ret_type: Typ) =
                match statement with
                | Return e         -> if tcE gtenv ltenv e <> ret_type then failwith ("Type mismatch in return statement in " + f)
                | Block(_,stms) -> List.iter (fun stm -> check_statement (stm, ret_type)) stms
                | _                -> tcS gtenv ltenv stm

            if topt.IsSome then check_statement (stm, Option.get topt)

            Map.add f (FTyp((List.map (fun x -> snd x) (Map.toList ltenv)), topt)) gtenv

    and tcGDecs gtenv =
        function
        | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
        | _         -> gtenv

/// tcP prog checks the well-typeness of a program prog
    and tcP(P(decs, stms)) = List.iter (tcS (tcGDecs Map.empty decs) Map.empty) stms
