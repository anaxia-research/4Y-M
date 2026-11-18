import YangMills
import Lean

/-!
Machine-readable dependency audit of every imported theorem whose user-facing
namespace starts with `YangMills`, including private and generated theorems.

Run after a successful `lake build`:

    lake env lean scripts/AllAxioms.lean > all-axioms.jsonl
    python scripts/check_all_axioms.py all-axioms.jsonl

The audit does not prove the hypotheses of a conditional theorem. It reports
the axioms used by its proof term, with hypotheses remaining hypotheses.
-/

open Lean Elab Command

private def emitYangMillsAudit (fields : List (String × Json)) : CommandElabM Unit :=
  liftIO <| IO.println ("YM_AXIOM_AUDIT " ++ (Json.mkObj fields).compress)

elab "#audit_yang_mills_axioms" : command => do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun result name info =>
    match info with
    | .thmInfo _ =>
        if (`YangMills).isPrefixOf (privateToUserName name) then
          result.push name
        else result
    | _ => result
  let names := names.qsort Name.lt
  if names.isEmpty then
    throwError "The YangMills import contains no theorem declarations"
  emitYangMillsAudit [
    ("kind", toJson "begin"),
    ("schema", toJson "yang-mills-axiom-audit-v1"),
    ("scope", toJson "YangMills namespace, including private and generated theorems"),
    ("expected_count", toJson names.size)]
  for name in names do
    let axioms ← collectAxioms name
    let axioms := (axioms.qsort Name.lt).map Name.toString
    emitYangMillsAudit [
      ("kind", toJson "theorem"),
      ("declaration", toJson name.toString),
      ("user_name", toJson (privateToUserName name).toString),
      ("axioms", toJson axioms)]
  emitYangMillsAudit [
    ("kind", toJson "end"),
    ("schema", toJson "yang-mills-axiom-audit-v1"),
    ("checked_count", toJson names.size)]

#audit_yang_mills_axioms
