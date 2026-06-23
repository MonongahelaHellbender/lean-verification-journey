import LeanVerificationJourney.RunnerFailClosed

open RunnerFailClosed

def rowJson (row : Kind × Nat × Verdict × String) : String :=
  let (kind, code, verdict, reason) := row
  "[\"" ++ kindName kind ++ "\"," ++ toString code ++ ",\"" ++ verdictName verdict ++ "\",\"" ++ reason ++ "\"]"

def tableJson : String :=
  let rows := String.intercalate "," (tableRows.map rowJson)
  "{\"schema_version\":\"0.1\","
    ++ "\"source\":\"LeanVerificationJourney.RunnerFailClosed\","
    ++ "\"exporter\":\"RunnerDecisionTable.lean\","
    ++ "\"field_names\":[\"path_ok\",\"artifact_present\",\"artifact_hash_ok\",\"manifest_ok\","
    ++ "\"manifest_hash_ok\",\"timeout_ok\",\"sandbox_ok\",\"rung_within_ceiling\","
    ++ "\"plugin_output_legal\",\"plugin_rung_le_ceiling\",\"plugin_rung_le_declared\","
    ++ "\"checker_positive\",\"all_parts_certified\",\"declared_eq_weakest\","
    ++ "\"quorum_count_ge_required\",\"quorum_distinct_count_ge_required\"],"
    ++ "\"kinds\":[\"atomic\",\"external\",\"composed\",\"multi-region\",\"quorum\",\"manual\",\"unknown\"],"
    ++ "\"row_format\":[\"kind\",\"code\",\"verdict\",\"reason_code\"],"
    ++ "\"rows\":[" ++ rows ++ "]}"

def main : IO Unit :=
  IO.println tableJson
