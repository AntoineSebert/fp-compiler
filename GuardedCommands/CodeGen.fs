﻿namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018
// This file is obtained by an adaption of the file MicroC/Comp.fs by Peter Sestoft
open System
open Machine
open GuardedCommands.Frontend.AST

module CodeGeneration =

(* A global variable has an absolute address, a local one has an offset: *)
    type Var =
        | GloVar of int                   (* absolute address in stack           *)
        | LocVar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and
   keeps track of next available offset for local variables *)
    type varEnv = Map<string, Var*Typ> * int

(* The function environment maps function name to label and parameter decs *)
    type funEnv = Map<string, label * Typ option * Dec list>

/// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
    let rec CE vEnv fEnv =
        function
        | N n                   -> [CSTI n]
        | B b                   -> [CSTI (if b then 1 else 0)]
        | Access acc            -> CA vEnv fEnv acc @ [LDI]
        | Apply("-", [e])       -> CE vEnv fEnv e @ [CSTI 0; SWAP; SUB]
        | Apply("!", [e])       -> CE vEnv fEnv e @ [NOT]

        | Apply("&&", [b1; b2]) ->
            let labend   = newLabel()
            let labfalse = newLabel()
            CE vEnv fEnv b1 @ [IFZERO labfalse] @ CE vEnv fEnv b2 @ [GOTO labend; Label labfalse; CSTI 0; Label labend]

        | Apply("||", [b1; b2]) ->
            let labend   = newLabel()
            let labfalse = newLabel()
            CE vEnv fEnv b1 @ [IFNZRO labend] @ CE vEnv fEnv b2 @ [GOTO labend; Label labfalse; CSTI 0; Label labend]

        | Apply(o, [e1; e2])
            when List.exists (fun x -> o=x) ["+"; "*"; "="; "-"; "<"] ->
                let ins = match o with
                          | "+"  -> [ADD]
                          | "*"  -> [MUL]
                          | "-"  -> [SUB]
                          | "="  -> [EQ]
                          | "<"  -> [SWAP; LT]
                          | "<=" -> let labeleq = newLabel()
                                    [EQ; IFNZRO labeleq; LT; IFNZRO labeleq; CSTI 0; Label labeleq]
                          | "<>" -> [EQ; NOT]
                          | _    -> failwith "CE: this case is not possible"
                CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ ins
        | Addr acc              -> CA vEnv fEnv acc
        //| Apply(">", [e1; e2]) -> CE vEnv fEnv e2 @ CE vEnv fEnv e1 @ [LT] // There is no greater than: Reverse the two elements
        | Apply("<>", [e1; e2]) -> CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ [LT] // There is no greater than: Reverse the two elements
        | Apply(f, es)          ->
            match Map.tryFind f fEnv with
            | Some (labf, _, _) -> (List.collect (CE vEnv fEnv) es) @ [CALL(List.length es, labf)]
            | None -> failwith ("CE: error: could not find " + f + " in fEnv")
            

/// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
    and CA vEnv fEnv =
        function
        | AVar x         ->
            match Map.find x (fst vEnv) with
            | (GloVar addr, _) -> [CSTI addr]
            | (LocVar addr, _) -> [GETBP; CSTI addr; ADD]
        | AIndex(acc, e) -> CA vEnv fEnv acc @ [LDI] @ CE vEnv fEnv e @ [ADD]
        | ADeref e       -> CE vEnv fEnv e

(* Bind declared variable in env and generate code to allocate it: *)
    let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv) =
        let (env, fdepth) = vEnv
        match typ with
        | ATyp (ATyp _, _) -> raise (Failure "allocate: array of arrays not permitted")
        | ATyp (t, Some i) ->
            let newEnv = (Map.add x (kind fdepth, typ) env, fdepth + 1)
            let code = [INCSP i; GETSP; CSTI (i - 1); SUB]
            (newEnv, code)
        | _                ->
            let newEnv = (Map.add x (kind fdepth, typ) env, fdepth + 1)
            let code = [INCSP 1]
            (newEnv, code)

/// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment
    let rec CS vEnv fEnv =
        function
        | PrintLn e          -> CE vEnv fEnv e @ [PRINTI; INCSP -1]
        | Ass(acc, e)        -> CA vEnv fEnv acc @ CE vEnv fEnv e @ [STI; INCSP -1]
        | MulAssign(_as, es) -> List.concat (List.map2 (fun acc exp -> (CS vEnv fEnv (Ass(acc, exp)))) _as es)
        | Block(decs,stms)   -> CSs vEnv fEnv stms
        | Alt gcs            -> CGCALTs vEnv fEnv gcs
        | Do gcs             -> CGCDOs vEnv fEnv gcs
        | Return e           -> CE vEnv fEnv e @ [RET (snd vEnv)]
        | Call(f, es)        ->
            match Map.tryFind f fEnv with
            | Some (labf, _, _) -> (List.collect (CE vEnv fEnv) es) @ [CALL(List.length es, labf)]
            | None -> failwith ("CE: error: could not find " + f + " in fEnv")

    and CSs vEnv fEnv stms = List.collect (CS vEnv fEnv) stms
    and CGCDOs vEnv fEnv = function GC(gcs) -> List.collect (CGCDO vEnv fEnv) gcs

    and CGCALTs vEnv fEnv =
        function GC(gcs) -> let labfalse = newLabel()
                            List.collect (CGCALT vEnv fEnv labfalse) gcs @ [Label labfalse]

/// CGCDO vEnv fEnv (e,stms) gives the code for the guarded command Do on the basis of a variable and a function environment
    and CGCDO vEnv fEnv =
        function (e, stms) -> let labfalse = newLabel()
                              let labloop  = newLabel()
                              match stms with
                              | []   -> [CSTI 0]
                              | stms -> [Label labloop] @ CE vEnv fEnv e @ [IFZERO labfalse] @ CSs vEnv fEnv stms @ [GOTO labloop; Label labfalse]

/// CGCDO vEnv fEnv (e,stms) gives the code for the guarded command Alt on the basis of a variable and a function environment
    and CGCALT vEnv fEnv labfalse = function (e, stms) -> CE vEnv fEnv e @ [IFZERO labfalse] @ List.collect (CS vEnv fEnv) stms

(* ------------------------------------------------------------------- *)

(* Build environments for global variables and functions *)

    let makeGlobalEnvs(decs: Dec list) : varEnv * funEnv * instr list =
        let rec addv(decs: Dec list, vEnv: varEnv, fEnv: funEnv) =
            match decs with
            | []        -> (vEnv, fEnv, [])
            | dec::decr ->
                match dec with
                | VarDec (typ, var)        ->
                    let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                    let (vEnv2, fEnv2, code2) = addv(decr, vEnv1, fEnv)
                    (vEnv2, fEnv2, code1 @ code2)
                | FunDec (tyOpt, f, xs, _) ->
                    addv(decr, vEnv, (Map.add f (newLabel(), tyOpt, xs) fEnv))

        addv(decs, (Map.empty, 0), Map.empty)

/// CP prog gives the code for a program prog
    let CP (P(decs,stms)) =
        let _ = resetLabels()
        let ((gvM, _) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
        initCode @ CSs gvEnv fEnv stms @ [STOP]
        